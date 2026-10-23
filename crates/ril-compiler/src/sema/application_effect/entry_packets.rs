//! An entry borrows an actual evaluated packet. Its retained Source coordinates
//! are claims to replay, never substitutes for the physical input or its duties.
use crate::sema::application_effect::generated_entries::{
    GeneratedEntryIndex, GeneratedEntryKey, GeneratedInput,
};
use crate::sema::application_effect::{CallableEntry, EntryArgument, EntryOrigin};
use crate::sema::{
    SemanticFacts,
    application_effect::ActivationKind,
    default_uses::{ArgumentSource, CallArguments, DefaultOrigin},
    evaluated::{CapturedSource, CurrentSourceView, EvaluatedValue, SourceCaptureView},
    model::{Ty, Value},
    numeric_selection::{NumericReplaySession, checked_resolution_in_query},
    record_bound_validation::OriginalOperandSources,
    source_query::SourceQuery,
    source_reception::Construction,
    source_types::{SourceSchema, SourceTypesError, WorkLimit},
};
use std::{cell::RefCell, collections::BTreeMap, rc::Rc};
#[path = "entry_current.rs"]
mod current;

type Check<T = ()> = Result<T, String>;

fn charge(work: &mut usize, count: usize) -> Check {
    match work.checked_sub(count) {
        Some(remaining) => {
            *work = remaining;
            Ok(())
        }
        None => {
            *work = 0;
            Err("entry packet evidence exceeds its work bound".into())
        }
    }
}

fn require(condition: bool, message: &str) -> Check {
    condition.then_some(()).ok_or_else(|| message.into())
}

fn graph<T>(
    work: &mut usize,
    query: impl FnOnce(&mut WorkLimit) -> Result<T, SourceTypesError>,
) -> Check<T> {
    let mut budget = WorkLimit::new(*work);
    let result = query(&mut budget);
    *work = budget.remaining();
    result.map_err(|error| format!("entry packet Source: {error}"))
}

fn source_coordinates(
    schema: &SourceSchema,
    environment: crate::sema::context::FrozenEnvId,
    work: &mut usize,
) -> Check<String> {
    charge(work, 4)?;
    let (bare, identities) = graph(work, |budget| {
        Ok((
            schema.bare_binder_identity(budget)?,
            schema.binder_identities(budget)?,
        ))
    })?;
    charge(
        work,
        8 + bare
            .as_ref()
            .map_or(0, |identity| 4 * identity.len().div_ceil(32)),
    )?;
    for identity in identities.iter().take(8) {
        charge(work, 4 * identity.len().div_ceil(32) + 1)?;
    }
    let shown: Vec<_> = identities.iter().take(8).collect();
    Ok(format!(
        "env={environment:?}, original={:?}, bare={bare:?}, binders={shown:?}, binder_count={}",
        schema.original(),
        identities.len()
    ))
}

pub(super) struct Replay<'a> {
    facts: &'a SemanticFacts,
    preparations: BTreeMap<crate::sema::copy_contract::CopyCallEventId, &'a CallArguments>,
    generated: GeneratedEntryIndex<'a>,
    sources: Option<OriginalOperandSources<'a>>,
    numeric: RefCell<NumericReplaySession>,
    query: Rc<SourceQuery>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum PhysicalPurpose {
    Occurrence,
    Receiver,
}

struct PhysicalPosition {
    epoch: usize,
    current: bool,
    depth: usize,
    purpose: PhysicalPurpose,
}

impl<'a> Replay<'a> {
    pub(super) fn pattern_windows(&mut self, work: &mut usize) -> Check {
        crate::sema::allocation::validate(self.facts, work)?;
        use crate::sema::pattern_windows;
        use std::collections::BTreeMap;
        charge(
            work,
            self.facts.pattern_windows.len() + self.facts.windows.len(),
        )?;
        let mut covered = BTreeMap::<_, crate::sema::WindowInfo>::new();
        for (ordinal, creation) in self.facts.pattern_windows.iter().enumerate() {
            if let Some(observation) = creation.input.birth_coordinates().observation {
                self.physical(
                    &creation.input,
                    observation,
                    creation.heap.allocation_epoch,
                    true,
                    work,
                )?;
            } else {
                let argument = pattern_windows::parameter_input(self.facts, creation, work)?
                    .ok_or("window subject has neither an observation nor a parameter input")?;
                self.full_value(
                    argument.value(),
                    argument.packet.current_epoch(),
                    creation.input.value(),
                    creation.input.current_epoch(),
                    work,
                )?;
            }
            pattern_windows::validate_creation(self.facts, ordinal, work)?;
            let mut node = creation.output_node.origin;
            let moves = self
                .facts
                .allocation_history
                .get(creation.output.current_epoch()..)
                .ok_or("window output lost its allocation history")?;
            charge(
                work,
                moves.len() + 2 + covered.len().checked_ilog2().unwrap_or(0) as usize,
            )?;
            for &(recent, older) in moves {
                if node == recent {
                    node = older;
                }
            }
            let mut info = pattern_windows::info_at(
                &creation.info,
                &self.facts.allocation_history,
                creation.output.current_epoch(),
                self.facts.allocation_history.len(),
                work,
            )?;
            if let Some(previous) = covered.get(&node) {
                pattern_windows::charge_info(previous, work).map_err(|e| e.to_string())?;
                require(
                    previous.pattern == info.pattern && previous.constant == info.constant,
                    "window recency merged different original allocation roles",
                )?;
                info.backing.nodes.extend(&previous.backing.nodes);
                info.backing.choices.clear();
                if info.lower != previous.lower {
                    info.lower = None;
                }
                if info.length != previous.length {
                    info.length = None;
                }
            }
            covered.insert(node, info);
        }
        for (&node, info) in &self.facts.windows {
            if info.pattern.is_some() {
                charge(
                    work,
                    1 + covered.len().checked_ilog2().unwrap_or(0) as usize,
                )?;
                require(
                    covered
                        .get(&node)
                        .is_some_and(|expected| pattern_windows::same_info(info, expected)),
                    "pattern window changed its independently replayed construction or retained metadata",
                )?;
            }
        }
        Ok(())
    }

    pub(super) fn new(facts: &'a SemanticFacts, work: &mut usize) -> Check<Self> {
        charge(work, facts.call_arguments.len() + 1)?;
        let mut preparations = BTreeMap::new();
        for row in &facts.call_arguments {
            charge(
                work,
                2 + preparations.len().checked_ilog2().unwrap_or(0) as usize,
            )?;
            require(
                preparations.insert(row.source_event, row).is_none(),
                "entry packet has duplicate argument preparations",
            )?;
        }
        Ok(Self {
            facts,
            preparations,
            generated: GeneratedEntryIndex::new(facts, work)?,
            sources: None,
            numeric: RefCell::default(),
            query: Rc::default(),
        })
    }

    /// A captured Source is a claim of the physical occurrence itself, even
    /// when that occurrence never becomes a callable input. All such claims
    /// enter the same independent replay and share the entry checker budget.
    pub(super) fn physical_sources(&mut self, work: &mut usize) -> Check {
        let facts = self.facts;
        charge(work, facts.expressions.len())?;
        for (observation, fact) in facts.expressions.iter().enumerate() {
            let packet = fact.value.packet();
            let evidence = packet.evidence_view();
            if matches!(evidence.capture, SourceCaptureView::Uncaptured) {
                // Ordinary evaluation always terminates its one birth capture.
                // Deleting that terminal claim cannot delete this obligation.
                // Explicit auxiliary emissions retain their separate, not yet
                // migrated roles; they are not ordinary expression execution.
                charge(work, 11)?;
                let record = facts
                    .evaluations
                    .get(observation)
                    .filter(|record| record.id.0 as usize == observation)
                    .ok_or("uncaptured physical value lost its evaluation record")?;
                require(
                    evidence.birth.observation == Some(observation)
                        && evidence.birth.identity == record.identity
                        && evidence.birth.context == Some(record.context)
                        && evidence.birth.environment == record.environment
                        && evidence.birth.allocation_epoch == record.allocation_epoch
                        && evidence.current_epoch == record.allocation_epoch
                        && fact.allocation_epoch == record.allocation_epoch
                        && matches!(evidence.current, CurrentSourceView::Birth),
                    "uncaptured emission changed its canonical birth or current view",
                )?;
                if let Some(identity) = record.identity {
                    let activation = facts
                        .activations
                        .get(identity.activation.0 as usize)
                        .ok_or("uncaptured physical value lost its activation")?;
                    require(
                        activation.id == identity.activation
                            && activation.source == Some(identity.source)
                            && activation.result == Some(record.id)
                            && fact.source_id == Some(identity.source),
                        "uncaptured physical value changed its original activation",
                    )?;
                    require(
                        activation.kind == ActivationKind::Emission,
                        "ordinary physical expression lost its terminal Source capture",
                    )?;
                    self.uncaptured_emission(observation, work)?;
                } else {
                    require(
                        fact.source_id.is_none(),
                        "uncaptured physical expression erased its activation identity",
                    )?;
                }
                continue;
            }
            self.physical_depth(
                packet,
                observation,
                PhysicalPosition {
                    epoch: fact.allocation_epoch,
                    current: false,
                    depth: 0,
                    purpose: PhysicalPurpose::Occurrence,
                },
                work,
            )?;
        }
        Ok(())
    }

    /// An auxiliary emission needs its existing receipt or original syntactic
    /// role. Retagging an ordinary leaf as Emission cannot erase its capture.
    fn uncaptured_emission(&self, observation: usize, work: &mut usize) -> Check {
        use crate::hir::nodes::{ExprKind, StmtKind};
        charge(work, 4)?;
        let record = self
            .facts
            .evaluations
            .get(observation)
            .ok_or("emission has no evaluation")?;
        let identity = record.identity.ok_or("emission has no original identity")?;
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("emission has no original HIR")?;
        let syntax = hir
            .expression(identity.source)
            .ok_or("emission has no original expression")?;
        if matches!(
            syntax.kind,
            ExprKind::Literal(
                ril_syntax::ast::Literal::Integer(_) | ril_syntax::ast::Literal::Float(_)
            )
        ) {
            return crate::sema::numeric_selection::validate_literal_in_query(
                self.facts,
                record.id,
                &self.numeric,
                &self.query,
                work,
            )
            .map_err(|error| {
                format!("uncaptured numeric emission lost its actual operand receipt: {error}")
            });
        }
        charge(work, self.facts.resumption_steps.len())?;
        let resumed = self
            .facts
            .resumption_steps
            .iter()
            .filter(|step| {
                step.context == record.context
                    && step.owner == record.scope
                    && (step.continuation_expression == observation
                        && step.resume_source == identity.source
                        && step.continuation_epoch == record.allocation_epoch
                        || step.arm_expression == observation
                            && step.arm_source == identity.source
                            && step.completion_epoch == record.allocation_epoch)
            })
            .count();
        require(
            resumed <= 1,
            "uncaptured emission borrowed multiple resumption answers",
        )?;
        if resumed == 1 {
            return Ok(());
        }
        if matches!(syntax.kind, ExprKind::Ambient) {
            charge(work, hir.declaration_roots().len())?;
            require(
                record.scope == crate::sema::facts::ScopeId(0)
                    && record.context.owner == Some(ril_compiler_core::ids::CallableOwner::Global),
                "ambient emission changed its module role",
            )?;
            if hir.declaration_roots().iter().any(|id| hir.statement(*id).is_some_and(|statement| matches!(statement.kind, StmtKind::Binding { value, .. } if value == identity.source))) {
                return Ok(())
            }
        }
        // A parameterized selector is a Field(Generic(...)), not a plain
        // name. Its original arm edge, not its spelling or AST shape, admits
        // this declaration-time emission.
        let mut selectors = 0;
        charge(work, self.facts.handlers.len())?;
        for handler in &self.facts.handlers {
            charge(work, handler.arms.len())?;
            for arm in &handler.arms {
                if arm.operation.hir_id != Some(identity.source) {
                    continue;
                }
                charge(work, 3)?;
                selectors += 1;
                let body = arm
                    .body
                    .hir_id
                    .ok_or("handler selector lost its original body")?;
                let original_body = hir
                    .expression(body)
                    .ok_or("handler selector body is absent")?;
                let crate::hir::nodes::LexicalOwner::HandlerArm { statement, index } =
                    original_body.info.owner
                else {
                    return Err("handler selector body lost its original arm owner".into());
                };
                let StmtKind::Handler(arms) = &hir
                    .statement(statement)
                    .ok_or("handler selector lost its original statement")?
                    .kind
                else {
                    return Err(
                        "handler selector owner is not an original handler statement".into(),
                    );
                };
                require(
                    arms.get(index as usize).is_some_and(|original| {
                        original.operation == identity.source && original.body == body
                    }),
                    "handler selector borrowed another original operation or arm",
                )?;
                if handler.callable_owner == record.context.owner {
                    return Ok(());
                }
            }
        }
        charge(work, 32)?;
        let activation = self
            .facts
            .activations
            .get(identity.activation.0 as usize)
            .ok_or("uncaptured emission diagnostic lost its activation")?;
        let cause = self
            .facts
            .expressions
            .get(observation)
            .ok_or("uncaptured emission diagnostic lost its value")?
            .value
            .cause;
        Err(format!(
            "uncaptured physical emission has no actual auxiliary role; observation={observation} HIR={identity:?} kind={:?} activation_kind={:?} parent={:?} scope={:?} context={:?} owner={:?} cause={cause:?}/{:?} selector_matches={selectors} resumption_matches={resumed}",
            std::mem::discriminant(&syntax.kind),
            activation.kind,
            activation.parent,
            record.scope,
            record.context,
            syntax.info.owner,
            self.facts.explanations.kinds.get(cause.0 as usize)
        ))
    }

    fn sources(&mut self, work: &mut usize) -> Check<&OriginalOperandSources<'a>> {
        charge(work, 1)?;
        if self.sources.is_none() {
            self.sources = Some(OriginalOperandSources::new_with_work_in(
                self.facts,
                work,
                self.query.clone(),
            )?);
        }
        self.sources
            .as_ref()
            .ok_or_else(|| "entry packet Source replay is absent".into())
    }

    fn observed_source(
        &mut self,
        observation: usize,
        work: &mut usize,
    ) -> Check<(
        Option<(SourceSchema, crate::sema::context::FrozenEnvironment)>,
        Construction,
    )> {
        let source = self
            .facts
            .expressions
            .get(observation)
            .and_then(|fact| fact.source_id)
            .ok_or("entry packet lost its original HIR expression")?;
        let result = match self.sources(work) {
            Ok(sources) => sources.observed_with_work(source, observation, work),
            Err(error) => Err(error),
        };
        self.source_result(observation, "independent original graph", result, work)
    }

    fn source_result<T>(
        &self,
        observation: usize,
        stage: &str,
        result: Check<T>,
        work: &mut usize,
    ) -> Check<T> {
        match result {
            Ok(value) => Ok(value),
            Err(error) => {
                charge(
                    work,
                    2 + stage.len().div_ceil(32) + error.len().div_ceil(32),
                )?;
                let diagnostic = self.source_diagnostic(observation, work)?;
                Err(format!("{error}; Source stage={stage}; {diagnostic}"))
            }
        }
    }

    fn source_diagnostic(&self, observation: usize, work: &mut usize) -> Check<String> {
        charge(work, 3)?;
        let fact = self
            .facts
            .expressions
            .get(observation)
            .ok_or("Source diagnostic lost its observation")?;
        let record = self
            .facts
            .evaluations
            .get(observation)
            .ok_or("Source diagnostic lost its record")?;
        crate::sema::clone_work::ty(work, &fact.value.ty, 0)
            .ok_or("Source diagnostic exceeds its shared work bound")?;
        charge(work, fact.value.sources.len() + 1)?;
        let mut bindings = Vec::with_capacity(fact.value.sources.len());
        for id in &fact.value.sources {
            charge(
                work,
                4 + self
                    .facts
                    .scopes
                    .records()
                    .len()
                    .checked_ilog2()
                    .unwrap_or(0) as usize
                    + self.facts.bindings.len().checked_ilog2().unwrap_or(0) as usize,
            )?;
            let binding = self
                .facts
                .bindings
                .get(*id)
                .ok_or("Source diagnostic binding is absent")?;
            charge(work, 1 + binding.name.len().div_ceil(32))?;
            let role = self
                .facts
                .scopes
                .get(&binding.owner)
                .map(|scope| match scope.origin {
                    crate::sema::scopes::ScopeOrigin::Module => "module",
                    crate::sema::scopes::ScopeOrigin::Unresolved => "universal",
                    crate::sema::scopes::ScopeOrigin::Named(_) => "named",
                    crate::sema::scopes::ScopeOrigin::Closure(_) => "closure",
                    crate::sema::scopes::ScopeOrigin::Operation(_) => "operation",
                });
            bindings.push(format!("{id}:{} parameter={} pattern={:?} owner={:?}/{role:?} context={:?} declaration_env={:?} index_env={:?}", binding.name,
                binding.parameter, binding.pattern, binding.owner, binding.context,
                binding.typing_environment.id(), self.facts.source_types.binding_environment(*id)));
        }
        charge(work, 2)?;
        let syntax = match record.identity.and_then(|identity| {
            self.facts
                .semantic_hir
                .as_deref()?
                .expression(identity.source)
        }) {
            Some(crate::hir::nodes::Expr {
                kind: crate::hir::nodes::ExprKind::Name(name),
                ..
            }) => {
                charge(
                    work,
                    2 + name.len().div_ceil(32)
                        + self
                            .facts
                            .constant_pool
                            .references
                            .len()
                            .checked_ilog2()
                            .unwrap_or(0) as usize,
                )?;
                format!(
                    "Name({name},constant={})",
                    self.facts.constant_pool.references.contains_key(name)
                )
            }
            Some(crate::hir::nodes::Expr {
                kind: crate::hir::nodes::ExprKind::Call { callee, .. },
                ..
            }) => format!("Call({callee:?})"),
            Some(node) => format!("{:?}", std::mem::discriminant(&node.kind)),
            None => "missing".into(),
        };
        Ok(format!(
            "observation={observation} HIR={:?} syntax={syntax} epoch={} physical_env={:?} context={:?} type={:?} bindings=[{}]",
            record.identity,
            record.allocation_epoch,
            record.environment,
            record.context,
            fact.value.ty,
            bindings.join("; ")
        ))
    }

    fn full_value(
        &self,
        original: &Value,
        from: usize,
        actual: &Value,
        to: usize,
        work: &mut usize,
    ) -> Check {
        let expected = crate::sema::evaluated::transport_value_at(
            original,
            &self.facts.allocation_history,
            from,
            to,
            work,
        )
        .map_err(|error| format!("entry packet value transport: {error}"))?;
        require(
            crate::sema::evaluated::same_birth_value(&expected, actual, work)
                .map_err(|error| error.to_string())?,
            "entry packet changed the complete original value or its nested duties",
        )
    }

    fn physical(
        &mut self,
        packet: &EvaluatedValue,
        observation: usize,
        epoch: usize,
        current: bool,
        work: &mut usize,
    ) -> Check {
        self.physical_depth(
            packet,
            observation,
            PhysicalPosition {
                epoch,
                current,
                depth: 0,
                purpose: PhysicalPurpose::Receiver,
            },
            work,
        )
    }

    fn physical_depth(
        &mut self,
        packet: &EvaluatedValue,
        observation: usize,
        position: PhysicalPosition,
        work: &mut usize,
    ) -> Check {
        let PhysicalPosition {
            epoch,
            current,
            depth,
            purpose,
        } = position;
        charge(work, 8)?;
        require(
            depth < 64,
            "entry current derivation exceeds its replay depth",
        )?;
        let evidence = packet.evidence_view();
        let fact = self
            .facts
            .expressions
            .get(observation)
            .ok_or("entry packet birth value is absent")?;
        let record = self
            .facts
            .evaluations
            .get(observation)
            .ok_or("entry packet birth occurrence is absent")?;
        let identity = record
            .identity
            .ok_or("entry packet birth has no original HIR identity")?;
        let activation = self
            .facts
            .activations
            .get(identity.activation.0 as usize)
            .ok_or("entry packet birth activation is absent")?;
        let environment = record
            .environment
            .ok_or("entry packet birth has no actual evaluation environment")?;
        let canonical = fact.value.packet();
        let canonical_evidence = canonical.evidence_view();
        require(
            packet.shares_birth(canonical)
                && canonical_evidence.birth == evidence.birth
                && canonical_evidence.current_epoch == record.allocation_epoch
                && matches!(canonical_evidence.current, CurrentSourceView::Birth)
                && evidence.birth.observation == Some(observation)
                && evidence.birth.identity == Some(identity)
                && evidence.birth.context == Some(record.context)
                && evidence.birth.allocation_epoch == record.allocation_epoch
                && evidence.birth.environment == Some(environment)
                && record.id.0 as usize == observation
                && fact.source_id == Some(identity.source)
                && fact.allocation_epoch == record.allocation_epoch
                && activation.id == identity.activation
                && activation.source == Some(identity.source)
                && activation.result == Some(record.id)
                && activation.scope == record.scope
                && activation.context == record.context
                && matches!(
                    activation.kind,
                    ActivationKind::Expression | ActivationKind::ControlTransfer
                )
                && evidence.current_epoch == epoch
                && record.allocation_epoch <= epoch
                && epoch <= self.facts.allocation_history.len(),
            "entry packet borrowed another physical birth, environment or epoch",
        )?;
        let registered_environment = graph(work, |budget| {
            self.facts.source_types.environment(environment, budget)
        });
        self.source_result(
            observation,
            "physical environment",
            registered_environment,
            work,
        )?;

        if let CurrentSourceView::Derived {
            input,
            step,
            source,
        } = evidence.current
        {
            return self.current_derivation(packet, input, step, source, depth, work);
        }

        let numeric = match evidence.capture {
            SourceCaptureView::NumericPending {
                hole,
                birth,
                environment: actual,
                ..
            } => {
                require(
                    actual == environment,
                    "numeric packet borrowed another birth environment",
                )?;
                let checked = checked_resolution_in_query(
                    self.facts,
                    record.id,
                    &self.numeric,
                    &self.query,
                    work,
                )
                .map_err(|error| format!("numeric packet birth: {error}"))?;
                let (id, resolution) =
                    checked.ok_or("numeric packet lost its actual hole resolution")?;
                require(
                    id == hole
                        && self
                            .facts
                            .numeric_holes
                            .get(hole.0 as usize)
                            .is_some_and(|record| record.id == hole && record.birth == *birth),
                    "numeric packet changed its genuine hole birth",
                )?;
                Some((hole, birth, actual, resolution))
            }
            SourceCaptureView::Captured { result, fresh } => {
                let source = result.map_err(|error| {
                    format!("entry packet retained a failed Source capture: {error}")
                })?;
                let (expected, construction) = if activation.kind == ActivationKind::ControlTransfer
                    && purpose == PhysicalPurpose::Occurrence
                {
                    // This ledger entry records sending control to the saved
                    // continuation. It is not the eventual completed resume
                    // expression, and cannot certify an input's answer Source.
                    charge(work, 1)?;
                    require(
                        self.facts
                            .semantic_hir
                            .as_deref()
                            .and_then(|hir| hir.expression(identity.source))
                            .is_some_and(|node| {
                                matches!(
                                    &node.kind,
                                    crate::hir::nodes::ExprKind::Control {
                                        operation: ril_syntax::ast::ControlOperation::Resume,
                                        ..
                                    }
                                )
                            }),
                        "physical control transfer has no original resume role",
                    )?;
                    (None, Construction::Opaque)
                } else {
                    self.observed_source(observation, work)?
                };
                let fresh =
                    fresh.ok_or("actual entry packet lost its original construction context")?;
                require(
                    construction_equal(fresh, &construction, work, 0)?,
                    "entry packet changed its real construction context",
                )?;
                match source {
                    CapturedSource::Unknown(actual) => {
                        require(
                            actual == environment,
                            "unknown packet borrowed another evaluation environment",
                        )?;
                        if let Some((schema, original_environment)) = &expected {
                            let diagnostic = self.source_diagnostic(observation, work)?;
                            return Err(format!(
                                "unknown packet contradicts an independently known Source: {diagnostic}; original_header={:?} original_env={:?}",
                                schema.original(),
                                original_environment.id()
                            ));
                        }
                    }
                    CapturedSource::Known(source) => {
                        let retained = graph(work, |budget| {
                            self.facts.source_types.view_schema(
                                source.view,
                                source.original,
                                budget,
                            )
                        });
                        let (actual, source_environment) = self.source_result(
                            observation,
                            "retained Source view",
                            retained,
                            work,
                        )?;
                        let expected = expected.ok_or_else(|| {
                            "known entry Source has no independent original graph".to_owned()
                        });
                        let (expected, expected_environment) = self.source_result(
                            observation,
                            "known Source coverage",
                            expected,
                            work,
                        )?;
                        let equivalent = graph(work, |budget| {
                            actual.equivalent_in(
                                &expected,
                                &source_environment,
                                &expected_environment,
                                budget,
                            )
                        });
                        let equivalent = match equivalent {
                            Err(error) => {
                                let actual_coordinates =
                                    source_coordinates(&actual, source_environment.id(), work)?;
                                let expected_coordinates =
                                    source_coordinates(&expected, expected_environment.id(), work)?;
                                Err(format!(
                                    "{error}; actual[{actual_coordinates}], expected[{expected_coordinates}]"
                                ))
                            }
                            answer => answer,
                        };
                        require(
                            self.source_result(
                                observation,
                                "original graph equivalence",
                                equivalent,
                                work,
                            )?,
                            "entry Source differs from its independently rebuilt graph",
                        )?;
                        let dependency =
                            graph(work, |budget| expected.requires_environment(budget));
                        if self.source_result(
                            observation,
                            "original graph environment dependency",
                            dependency,
                            work,
                        )? && source_environment.id() != expected_environment.id()
                        {
                            let diagnostic = self.source_diagnostic(observation, work)?;
                            return Err(format!(
                                "entry Source borrowed another declaration interpretation: {diagnostic}; captured_env={:?} original_env={:?} captured_header={:?} original_header={:?}",
                                source_environment.id(),
                                expected_environment.id(),
                                source.original,
                                expected.original()
                            ));
                        }
                    }
                }
                None
            }
            SourceCaptureView::Uncaptured => {
                return Err("an actual application packet lost its original Source capture".into());
            }
        };
        let mut expected = crate::sema::evaluated::transport_value_at(
            &fact.value,
            &self.facts.allocation_history,
            record.allocation_epoch,
            epoch,
            work,
        )
        .map_err(|error| error.to_string())?;
        match evidence.current {
            CurrentSourceView::Birth => {}
            CurrentSourceView::Numeric {
                hole,
                birth,
                environment: actual,
                resolution,
                source,
            } => {
                let (expected_hole, expected_birth, expected_environment, checked) = numeric
                    .as_ref()
                    .ok_or("selected packet has no genuine pending numeric basis")?;
                require(
                    hole == *expected_hole
                        && birth == *expected_birth
                        && actual == *expected_environment
                        && source.view.environment == actual,
                    "selected packet changed its actual pending basis",
                )?;
                resolution
                    .try_clone(work)
                    .map_err(|error| error.to_string())?;
                require(
                    resolution.as_ref() == checked.as_ref(),
                    "selected packet changed its independently replayed resolution",
                )?;
                checked
                    .apply(&mut expected, work)
                    .map_err(|error| error.to_string())?;
                let retained = graph(work, |budget| {
                    self.facts
                        .source_types
                        .view_schema(source.view, source.original, budget)
                });
                let (schema, _) =
                    self.source_result(observation, "numeric retained Source", retained, work)?;
                let equivalent = graph(work, |budget| {
                    let expected = SourceSchema::scalar(
                        crate::sema::evaluated::numeric_source_scalar(checked.number_type),
                        None,
                        budget,
                    )?;
                    schema.equivalent(&expected, budget)
                });
                require(
                    self.source_result(
                        observation,
                        "numeric scalar graph equivalence",
                        equivalent,
                        work,
                    )?,
                    "selected numeric packet changed its fixed scalar Source",
                )?;
            }
            CurrentSourceView::Pending if !current => {}
            CurrentSourceView::Pending => {
                return Err("callee current Source still needs its actual value derivation".into());
            }
            CurrentSourceView::Failed(error) => {
                return Err(format!("entry packet current Source failed: {error}"));
            }
            CurrentSourceView::Derived { .. } => {
                return Err("entry current derivation was not independently replayed".into());
            }
        }
        require(
            crate::sema::evaluated::same_birth_value(&expected, packet.value(), work)
                .map_err(|error| error.to_string())?,
            "entry packet changed its original value, permissions or duties",
        )
    }

    pub(super) fn entry(
        &mut self,
        entry: &CallableEntry,
        key: GeneratedEntryKey,
        work: &mut usize,
    ) -> Check {
        charge(work, entry.arguments.len() + 2)?;
        for argument in entry.arguments.iter() {
            require(
                argument.packet.current_epoch() == entry.allocation_epoch,
                "entry packet is not at its own receiving epoch",
            )?;
            let snapshot = graph(work, |budget| argument.snapshot_view(budget));
            let snapshot = if let Some(observation) =
                argument.packet.birth_coordinates().observation
            {
                self.source_result(observation, "entry heap epoch", snapshot, work)?
            } else {
                match snapshot {
                    Ok(snapshot) => snapshot,
                    Err(error) => {
                        charge(work, 4 + error.len().div_ceil(32))?;
                        let role = match entry.origin {
                            EntryOrigin::Application(_) => "application",
                            EntryOrigin::Generated { .. } => "generated",
                            EntryOrigin::DeclarationProbe => "declaration",
                            EntryOrigin::SignatureProbe(_) => "signature",
                            EntryOrigin::Unresolved => "unresolved",
                        };
                        return Err(format!(
                            "{error}; Source stage=entry heap epoch; observation=None role={role} packet_epoch={} heap_epoch={:?} entry_epoch={}",
                            argument.packet.current_epoch(),
                            argument.heap.as_ref().map(|heap| heap.allocation_epoch),
                            entry.allocation_epoch
                        ));
                    }
                }
            };
            crate::sema::heap_snapshot_validation::validate(self.facts, snapshot, work)?;
        }
        match &entry.origin {
            EntryOrigin::Application(event) => {
                charge(
                    work,
                    2 + self.preparations.len().checked_ilog2().unwrap_or(0) as usize,
                )?;
                let preparation = self
                    .preparations
                    .get(event)
                    .copied()
                    .ok_or("entry packet has no original argument preparation")?;
                let event = self
                    .facts
                    .copy_call_events
                    .get(event.0 as usize)
                    .filter(|actual| actual.id == *event)
                    .ok_or("entry packet has no original application")?;
                require(
                    preparation.evaluation_complete
                        && preparation.slots.len() == entry.arguments.len(),
                    "entry packet lost its complete application slots",
                )?;
                let callee = entry
                    .callee
                    .as_deref()
                    .ok_or("application entry lost its actual callee packet")?;
                self.physical(
                    callee,
                    event
                        .callee_expression
                        .ok_or("application callee token is absent")?,
                    entry.allocation_epoch,
                    true,
                    work,
                )?;
                for (slot, argument) in entry.arguments.iter().enumerate() {
                    let observation = match preparation.slots.get(slot) {
                        Some(ArgumentSource::Supplied) => preparation
                            .supplied
                            .get(&(slot as u32))
                            .map(|token| token.expression),
                        Some(ArgumentSource::Default(id)) => self
                            .facts
                            .default_uses
                            .get(id.0 as usize)
                            .filter(|receipt| {
                                receipt.id == *id
                                    && receipt.origin == DefaultOrigin::Call(event.id)
                                    && receipt.parameter as usize == slot
                            })
                            .and_then(|receipt| receipt.result_expression),
                        _ => None,
                    }
                    .ok_or("entry packet lost its genuine supplied/default birth")?;
                    self.physical(
                        &argument.packet,
                        observation,
                        entry.allocation_epoch,
                        false,
                        work,
                    )?;
                }
            }
            EntryOrigin::Generated { callee, .. } => {
                let packet = entry
                    .callee
                    .as_deref()
                    .ok_or("generated entry lost its actual callee packet")?;
                self.physical(
                    packet,
                    callee.0 as usize,
                    entry.allocation_epoch,
                    true,
                    work,
                )?;
                let inputs: Vec<_> = {
                    charge(work, entry.arguments.len())?;
                    let proof = self.generated.get(key, work)?;
                    (0..entry.arguments.len())
                        .map(|slot| proof.input(slot))
                        .collect::<Check<_>>()?
                };
                for (argument, input) in entry.arguments.iter().zip(inputs) {
                    self.generated_value(argument, input, entry.allocation_epoch, work)?;
                }
            }
            EntryOrigin::DeclarationProbe | EntryOrigin::SignatureProbe(_) => {
                require(
                    entry.callee.is_none(),
                    "universal entry borrowed an actual callee packet",
                )?;
                for argument in entry.arguments.iter() {
                    let evidence = argument.packet.evidence_view();
                    require(
                        evidence.birth.observation.is_none()
                            && evidence.birth.identity.is_none()
                            && evidence.birth.context.is_none()
                            && evidence.birth.environment.is_none()
                            && matches!(evidence.capture, SourceCaptureView::Uncaptured)
                            && matches!(evidence.current, CurrentSourceView::Birth),
                        "universal entry fabricated an ordinary packet birth or Source",
                    )?;
                }
            }
            EntryOrigin::Unresolved => {
                if let Some(callee) = &entry.callee {
                    require(
                        callee.current_epoch() == entry.allocation_epoch,
                        "unresolved entry changed its callee epoch",
                    )?;
                    self.unobserved(callee)?;
                }
                for argument in entry.arguments.iter() {
                    self.unobserved(&argument.packet)?;
                }
            }
        }
        Ok(())
    }

    fn unobserved(&self, packet: &EvaluatedValue) -> Check {
        let evidence = packet.evidence_view();
        require(
            evidence.birth.observation.is_none()
                && evidence.birth.identity.is_none()
                && evidence.birth.context.is_none()
                && evidence.birth.environment.is_none()
                && matches!(evidence.capture, SourceCaptureView::Uncaptured)
                && matches!(evidence.current, CurrentSourceView::Birth),
            "unresolved entry cannot authorize an ordinary packet birth or a Source derivation",
        )
    }

    fn generated_value(
        &mut self,
        argument: &EntryArgument,
        input: GeneratedInput<'a>,
        epoch: usize,
        work: &mut usize,
    ) -> Check {
        let evidence = argument.packet.evidence_view();
        require(
            matches!(evidence.capture, SourceCaptureView::Uncaptured)
                && matches!(evidence.current, CurrentSourceView::Birth)
                && evidence.birth.observation.is_none()
                && evidence.birth.identity.is_none()
                && evidence.birth.context.is_none()
                && evidence.birth.environment.is_none(),
            "generated value claimed an unproved expression or Source birth",
        )?;
        match input {
            GeneratedInput::Scope(input) => {
                let expected = Value::reference(
                    Ty::Named("Concurrent::Scope".into()),
                    input.node,
                    input.cause,
                );
                require(
                    crate::sema::evaluated::same_birth_value(&expected, argument.value(), work)
                        .map_err(|error| error.to_string())?,
                    "generated scope token changed its original value",
                )
            }
            GeneratedInput::Copied { boundary, .. } => self.full_value(
                boundary
                    .output
                    .as_ref()
                    .ok_or("generated copy has no actual output")?,
                boundary
                    .output_allocation_epoch
                    .ok_or("generated copy has no output epoch")?,
                argument.value(),
                epoch,
                work,
            ),
            GeneratedInput::Widened { original, .. } => {
                let mut expected = crate::sema::evaluated::transport_value_at(
                    &original.value,
                    &self.facts.allocation_history,
                    original.allocation_epoch,
                    epoch,
                    work,
                )
                .map_err(|error| error.to_string())?;
                expected.origins.choices.clear();
                expected.temporary = true;
                expected.constant = None;
                require(
                    crate::sema::evaluated::same_birth_value(&expected, argument.value(), work)
                        .map_err(|error| error.to_string())?,
                    "generated widening changed the complete actual value",
                )
            }
            GeneratedInput::Scalar(kind) => {
                require(
                    (argument.value().cause.0 as usize) < self.facts.explanations.causes.len(),
                    "generated scalar has no actual cause identity",
                )?;
                if let super::ScalarInput::ByteSuffix(observation) = kind {
                    require(
                        self.facts
                            .expressions
                            .get(observation.0 as usize)
                            .is_some_and(|fact| fact.value.cause == argument.value().cause),
                        "generated byte suffix borrowed another physical input",
                    )?;
                }
                let ty = match kind {
                    super::ScalarInput::PositiveInt => Ty::Int("int".into()),
                    _ => Ty::Bytes,
                };
                let expected = Value::scalar(ty, None, argument.value().cause);
                require(
                    crate::sema::evaluated::same_birth_value(&expected, argument.value(), work)
                        .map_err(|error| error.to_string())?,
                    "generated scalar acquired unrelated authority or duties",
                )
            }
        }
    }
}

fn construction_equal(
    left: &Construction,
    right: &Construction,
    work: &mut usize,
    depth: usize,
) -> Check<bool> {
    charge(work, 1)?;
    require(
        depth < 128,
        "entry construction proof exceeds its depth bound",
    )?;
    match (left, right) {
        (Construction::Opaque, Construction::Opaque) => Ok(true),
        (
            Construction::Nullary {
                declaration: a,
                source: x,
            },
            Construction::Nullary {
                declaration: b,
                source: y,
            },
        ) => Ok(a == b && x == y),
        (Construction::Array(a), Construction::Array(b))
        | (Construction::Tuple(a), Construction::Tuple(b)) => {
            if a.len() != b.len() {
                return Ok(false);
            }
            charge(work, a.len())?;
            for (a, b) in a.iter().zip(b) {
                if !construction_equal(a, b, work, depth + 1)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Construction::Map(a), Construction::Map(b)) => {
            if a.len() != b.len() {
                return Ok(false);
            }
            charge(work, a.len())?;
            for ((ak, av), (bk, bv)) in a.iter().zip(b) {
                if !construction_equal(ak, bk, work, depth + 1)?
                    || !construction_equal(av, bv, work, depth + 1)?
                {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Construction::Record(a), Construction::Record(b)) => {
            if a.len() != b.len() {
                return Ok(false);
            }
            charge(work, a.len())?;
            for ((ak, av), (bk, bv)) in a.iter().zip(b) {
                charge(work, ak.len().max(bk.len()).div_ceil(32))?;
                if ak != bk || !construction_equal(av, bv, work, depth + 1)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parameterized_handler_selectors_need_their_exact_original_arm_edge() {
        let verified = crate::Session::new(
            ril_test::case_bytes("tests/regressions/defaults.ril::local-budget").to_vec(),
        )
        .verify()
        .unwrap();
        let facts = verified.facts();
        let hir = facts.semantic_hir.as_deref().unwrap();
        let (observation, record) = facts
            .evaluations
            .iter()
            .enumerate()
            .find(|(_, record)| {
                record.identity.is_some_and(|identity| {
                    facts.activations[identity.activation.0 as usize].kind
                        == ActivationKind::Emission
                        && matches!(
                            hir.expression(identity.source).unwrap().kind,
                            crate::hir::nodes::ExprKind::Field { .. }
                        )
                })
            })
            .expect("the parameterized effect must emit its original field selector");
        let mut stage_work = 4_000_000;
        let replay = Replay::new(facts, &mut stage_work).unwrap();
        let before = stage_work;
        replay
            .uncaptured_emission(observation, &mut stage_work)
            .unwrap();
        let cost = before - stage_work;
        let mut exact = cost;
        replay.uncaptured_emission(observation, &mut exact).unwrap();
        assert_eq!(exact, 0);
        for limit in [0, cost - 1] {
            assert!(
                replay
                    .uncaptured_emission(observation, &mut { limit })
                    .is_err()
            );
        }
        for mutation in 0..2 {
            let mut changed = facts.clone();
            let source = record.identity.unwrap().source;
            for handler in &mut changed.handlers {
                for arm in &mut handler.arms {
                    if arm.operation.hir_id == Some(source) {
                        if mutation == 0 {
                            arm.operation.hir_id = None;
                        } else {
                            arm.body.hir_id = Some(source);
                        }
                    }
                }
            }
            let mut work = 4_000_000;
            let replay = Replay::new(&changed, &mut work).unwrap();
            assert!(
                replay.uncaptured_emission(observation, &mut work).is_err(),
                "selector mutation {mutation}"
            );
        }
    }

    #[test]
    fn ordinary_physical_capture_cannot_be_deleted_outside_callable_inputs() {
        for target in ["pointer32", "pointer64"] {
            let verified = crate::Session::with_options(
                ril_test::case_bytes("tests/regressions/defaults.ril::local-budget").to_vec(),
                crate::CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap();
            let facts = verified.facts();
            let (observation, record) = facts
                .evaluations
                .iter()
                .enumerate()
                .find(|(_, record)| {
                    let Some(scope) = facts.scopes.get(&record.scope) else {
                        return false;
                    };
                    let crate::sema::scopes::ScopeOrigin::Operation(entry) = &scope.origin else {
                        return false;
                    };
                    entry.operation == u64::MAX - 1
                        && matches!(entry.origin, EntryOrigin::Generated { .. })
                        && record
                            .identity
                            .is_some_and(|identity| Some(identity.source) == entry.body)
                })
                .expect("the budget must execute its real recovery body");
            let original = facts.expressions[observation].value.packet();
            assert!(matches!(
                original.evidence_view().capture,
                SourceCaptureView::Captured { .. }
            ));
            let mut changed = facts.clone();
            let value = crate::sema::evaluated::transport_value_at(
                original.value(),
                &facts.allocation_history,
                record.allocation_epoch,
                record.allocation_epoch,
                &mut 4_000_000,
            )
            .unwrap();
            let replacement = EvaluatedValue::observed(value, observation, record);
            assert!(matches!(
                replacement.evidence_view().capture,
                SourceCaptureView::Uncaptured
            ));
            changed.expressions[observation].value =
                crate::sema::evaluated::PhysicalValue::from_packet(std::sync::Arc::new(
                    replacement,
                ));
            let mut work = 4_000_000;
            let error = Replay::new(&changed, &mut work)
                .unwrap()
                .physical_sources(&mut work)
                .unwrap_err();
            assert!(
                error.contains("lost its terminal Source capture"),
                "{target}: {error}"
            );
            assert!(
                crate::sema::validate::solved_facts(&changed).is_err(),
                "{target}: deleting a non-input capture cannot erase its physical obligation"
            );
        }
    }

    #[test]
    fn erasing_capture_and_retagging_a_leaf_cannot_create_an_auxiliary_emission() {
        let verified = crate::Session::new(
            ril_test::case_bytes(
                "tests/regressions/closed-standard-data.ril::primitive-alias-read-chain",
            )
            .to_vec(),
        )
        .verify()
        .unwrap();
        let facts = verified.facts();
        let hir = facts.semantic_hir.as_deref().unwrap();
        let (observation, record) = facts
            .evaluations
            .iter()
            .enumerate()
            .find(|(_, record)| {
                record.identity.is_some_and(|identity| {
                    let node = hir.expression(identity.source).unwrap();
                    matches!(
                        node.info.origin,
                        crate::hir::nodes::NodeOrigin::Generated {
                            kind: crate::hir::nodes::GeneratedKind::PatternValue,
                            ..
                        }
                    ) && matches!(
                        node.kind,
                        crate::hir::nodes::ExprKind::Literal(ril_syntax::ast::Literal::Bytes(_))
                    )
                })
            })
            .expect("the actual read result must be tested against an original bytes pattern");
        let mut changed = facts.clone();
        let value = crate::sema::evaluated::transport_value_at(
            &facts.expressions[observation].value,
            &facts.allocation_history,
            record.allocation_epoch,
            record.allocation_epoch,
            &mut 4_000_000,
        )
        .unwrap();
        changed.expressions[observation].value = crate::sema::evaluated::PhysicalValue::from_packet(
            std::sync::Arc::new(EvaluatedValue::observed(value, observation, record)),
        );
        changed.activations[record.identity.unwrap().activation.0 as usize].kind =
            ActivationKind::Emission;
        let mut work = 4_000_000;
        let error = Replay::new(&changed, &mut work)
            .unwrap()
            .physical_sources(&mut work)
            .unwrap_err();
        assert!(error.contains("no actual auxiliary role"), "{error}");
        assert!(crate::sema::validate::solved_facts(&changed).is_err());
    }

    #[test]
    fn physical_source_coverage_preserves_control_transfer_roles_and_one_work_bound() {
        for target in ["pointer32", "pointer64"] {
            let verified = crate::Session::with_options(
                ril_test::case_bytes("tests/conformance/effects.ril::accept-duplicate-resume")
                    .to_vec(),
                crate::CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|error| panic!("{target}: {error:?}"));
            let facts = verified.facts();
            let transfers: Vec<_> = facts
                .evaluations
                .iter()
                .filter(|record| {
                    record
                        .identity
                        .and_then(|identity| facts.activations.get(identity.activation.0 as usize))
                        .is_some_and(|activation| {
                            activation.kind == ActivationKind::ControlTransfer
                        })
                })
                .collect();
            assert!(
                !transfers.is_empty(),
                "the original program must actually transfer through resume"
            );
            for record in transfers {
                let packet = facts.expressions[record.id.0 as usize].value.packet();
                assert!(matches!(packet.evidence_view().capture,
                    SourceCaptureView::Captured { result: Ok(CapturedSource::Unknown(environment)), fresh: Some(Construction::Opaque) }
                        if Some(environment) == record.environment));
                let mut work = 4_000_000;
                let mut replay = Replay::new(facts, &mut work).unwrap();
                assert!(
                    replay
                        .physical(
                            packet,
                            record.id.0 as usize,
                            record.allocation_epoch,
                            false,
                            &mut work
                        )
                        .is_err(),
                    "a control transfer cannot replace a completed receiving expression"
                );
            }
            let mut work = 4_000_000;
            let mut replay = Replay::new(facts, &mut work).unwrap();
            replay.physical_sources(&mut work).unwrap();
            let used = 4_000_000 - work;
            let mut exact = used;
            Replay::new(facts, &mut exact)
                .unwrap()
                .physical_sources(&mut exact)
                .unwrap();
            assert_eq!(exact, 0);
            for mut short in [0, used - 1] {
                let result = Replay::new(facts, &mut short)
                    .and_then(|mut replay| replay.physical_sources(&mut short));
                assert!(
                    result.is_err(),
                    "physical Source replay borrowed another work allowance"
                );
            }
        }
    }
}
