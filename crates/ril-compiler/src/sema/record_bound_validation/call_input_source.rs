//! Original named input replay. Complete source coordinates are read before
//! reception; physical argument/default identities never come from a span scan.
use super::*;
#[path = "call_input_source_carriers.rs"]
mod carrier_sources;
#[path = "call_input_source_closures.rs"]
mod closure_sources;
#[path = "call_input_source_composites.rs"]
mod composites;
#[path = "constructor_input_source.rs"]
mod constructor_inputs;
#[path = "callable_entries.rs"]
mod entries;
#[path = "call_input_source_graph.rs"]
mod graph_sources;
#[path = "inferred_parameter_sources.rs"]
mod inferred_parameters;
#[path = "numeric_source_declarations.rs"]
mod numeric_sources;
#[path = "pattern_value_sources.rs"]
mod pattern_values;
#[path = "primitive_aliases.rs"]
mod primitive_aliases;
#[path = "call_input_source_result.rs"]
mod producing_result;
#[path = "call_input_source_reception.rs"]
mod reception;
#[path = "static_key_sources.rs"]
mod static_keys;
#[path = "storage_input_source.rs"]
mod storage_inputs;
#[path = "storage_read_sources.rs"]
mod storage_reads;
use crate::sema::{
    context::FrozenEnvironment,
    copy_contract::CopyInvocation,
    default_uses::{ArgumentSource, DefaultOrigin},
    effect_identity::{InvocationContext, StaticArgumentWitness},
    model::Callable,
    source_reception,
    source_types::{SourceSchema, WorkLimit},
};
pub(super) use storage_reads::StorageAdmissions;

pub(crate) type OriginalSourceInput = (
    Option<(SourceSchema, FrozenEnvironment)>,
    source_reception::Construction,
);
type OriginalSource = (SourceSchema, FrozenEnvironment);

fn source_scan_work(work: &mut usize, count: usize) -> Check {
    *work = work
        .checked_sub(count)
        .ok_or_else(|| "Source identity lookup exceeds its work bound".to_owned())?;
    Ok(())
}

fn unique_source_record<'a, T>(
    records: &'a [T],
    work: &mut usize,
    message: &str,
    matches: impl FnMut(&&T) -> bool,
) -> Check<Option<&'a T>> {
    source_scan_work(work, records.len())?;
    let mut matching = records.iter().filter(matches);
    let first = matching.next();
    require(matching.next().is_none(), message)?;
    Ok(first)
}

pub(crate) struct OriginalOperandSources<'a> {
    replay: Replay<'a>,
    sites: super::explicit_named::SourceSites<'a>,
}

/// The caller still checks the direct declaration against its catalog. The
/// replayed read preserves every field through the authenticated alias chain.
pub(crate) struct PrimitiveRead<'a> {
    pub(crate) declaration: &'a Value,
    pub(crate) value: Value,
}

#[derive(Clone, Copy)]
pub(super) struct SourceVisit {
    pub(super) depth: usize,
    pub(super) observation: Option<usize>,
}
impl<'a> OriginalOperandSources<'a> {
    /// A primitive's identity can select its fixed catalog requirements before
    /// a concrete instance of its quantified signature has been selected.
    /// Immutable aliases retain the identity of their actual initializer.
    pub(crate) fn primitive_read(
        &self,
        observation: usize,
        identity: &str,
        work: &mut usize,
    ) -> Check<PrimitiveRead<'a>> {
        primitive_aliases::authenticate(self, observation, identity, work)
    }

    pub(crate) fn new(facts: &'a SemanticFacts) -> Check<Self> {
        Self::new_with_work(facts, &mut { 16_000_000 })
    }
    pub(crate) fn new_with_work(facts: &'a SemanticFacts, work: &mut usize) -> Check<Self> {
        Self::new_with_work_in(facts, work, std::rc::Rc::default())
    }
    pub(crate) fn new_with_work_in(
        facts: &'a SemanticFacts,
        work: &mut usize,
        query: std::rc::Rc<crate::sema::source_query::SourceQuery>,
    ) -> Check<Self> {
        let mut replay = Replay::new_with_work(facts, work)?;
        replay.source_query = query;
        Ok(Self {
            replay,
            sites: super::explicit_named::source_sites_foreign_with_work(facts, work)?,
        })
    }
    pub(crate) fn input(
        &self,
        event_id: crate::sema::copy_contract::CopyCallEventId,
        slot: u32,
    ) -> Check<OriginalSourceInput> {
        self.input_with_work(event_id, slot, &mut 4096)
    }
    pub(crate) fn input_with_work(
        &self,
        event_id: crate::sema::copy_contract::CopyCallEventId,
        slot: u32,
        work: &mut usize,
    ) -> Check<OriginalSourceInput> {
        let replay = &self.replay;
        let facts = replay.facts;
        let sites = &self.sites;
        source_scan_work(work, 1)?;
        let event = facts
            .copy_call_events
            .get(event_id.0 as usize)
            .filter(|event| event.id == event_id)
            .ok_or_else(|| "source operand origin event is absent".to_owned())?;
        let origin = unique_source_record(
            &sites.calls,
            work,
            "source operand origin has multiple actual Calls",
            |site| Some(site.owner) == event.owner && event.matches_source(site.expression),
        )?
        .ok_or("source operand origin has no actual Call")?;
        let application = AstApplication::from_ast(origin.expression)
            .ok_or_else(|| "source operand origin is not an application".to_owned())?;
        let callee = application.callee;
        let arguments = &application.operands;
        let callee_token = event
            .callee_expression
            .ok_or_else(|| "source operand origin callee is absent".to_owned())?;
        let callee_fact = facts
            .expressions
            .get(callee_token)
            .ok_or_else(|| "source operand callee token is outside its arena".to_owned())?;
        let context = replay.observations.row(callee_token, work)?.context;
        require(
            callee_fact.source_id.is_some()
                && callee_fact.source_id == callee.hir_id
                && context.owner == event.owner
                && context.invocation == event.parent,
            "source operand callee is borrowed from another occurrence",
        )?;
        let preparation = replay.input_preparation(event.id, work)?;
        require(
            preparation.target == event.target && preparation.evaluation_complete,
            "source operand preparation changed its actual target or completion",
        )?;
        source_scan_work(work, arguments.len() + preparation.slots.len())?;
        let labels = crate::sema::builtin_sources::parameter_labels(
            &callee_fact.value,
            preparation.slots.len(),
        );
        let mapping = crate::hir::application::bind_slots(
            &labels,
            arguments.iter().map(|argument| argument.label),
        );
        let mut occupied = BTreeSet::new();
        let mut selected = None;
        for (argument, position) in arguments.iter().zip(mapping) {
            let position = position.map_err(|code| {
                format!(
                    "source operand label/position is outside its original public signature: {code}"
                )
            })?;
            require(
                occupied.insert(position),
                "source operand position is written twice",
            )?;
            if position == slot as usize {
                selected = Some(argument.expression);
            }
        }
        require(
            preparation.supplied.len() == occupied.len(),
            "source operand preparation lost or added an actual input",
        )?;
        let syntax =
            selected.ok_or_else(|| "source operand selected slot is not supplied".to_owned())?;
        require(
            preparation.slots.get(slot as usize) == Some(&ArgumentSource::Supplied),
            "source operand selected slot is not its actual supplied input",
        )?;
        let token = preparation
            .supplied
            .get(&slot)
            .ok_or_else(|| "source operand root token is absent".to_owned())?;
        let value = facts
            .expressions
            .get(token.expression)
            .ok_or_else(|| "source operand root token is outside its arena".to_owned())?;
        let actual_context = replay.observations.row(token.expression, work)?;
        require(
            token.allocation_epoch <= facts.allocation_history.len()
                && value.source_id.is_some()
                && value.source_id == syntax.hir_id
                && actual_context.context == context
                && actual_context.argument_of == Some((event.id, slot)),
            "source operand token borrowed another physical occurrence or context",
        )?;
        replay.input_operand_interval(event, slot as usize, token.expression, context, work)?;
        self.observed_with_work(
            syntax.hir_id.ok_or("source input has no HIR root")?,
            token.expression,
            work,
        )
    }
    #[cfg(test)]
    pub(crate) fn observed(
        &self,
        source: ril_compiler_core::ids::ExprId,
        observation: usize,
    ) -> Check<OriginalSourceInput> {
        self.observed_with_work(source, observation, &mut 4096)
    }

    pub(crate) fn observed_with_work(
        &self,
        source: ril_compiler_core::ids::ExprId,
        observation: usize,
        work: &mut usize,
    ) -> Check<OriginalSourceInput> {
        let _entered = self
            .replay
            .source_query
            .enter(
                crate::sema::source_query::QueryKind::Source,
                ril_compiler_core::ids::EvaluationOccurrenceId(
                    u32::try_from(observation)
                        .map_err(|_| "Source observation exceeds its arena identity")?,
                ),
                work,
            )
            .map_err(|error| error.to_string())?;
        source_scan_work(
            work,
            2 + self.sites.expressions.len().checked_ilog2().unwrap_or(0) as usize,
        )?;
        let syntax = match self.sites.expressions.get(&source) {
            Some(syntax) => std::borrow::Cow::Borrowed(*syntax),
            None => std::borrow::Cow::Owned(pattern_values::expression(
                &self.replay,
                source,
                observation,
                work,
            )?),
        };
        let fact = self
            .replay
            .facts
            .expressions
            .get(observation)
            .ok_or("receiver input is outside its value arena")?;
        let record = self
            .replay
            .facts
            .evaluations
            .get(observation)
            .ok_or("receiver input has no actual evaluation")?;
        require(
            fact.source_id == Some(source) && record.id.0 as usize == observation,
            "receiver input borrowed another physical observation",
        )?;
        require(
            record
                .identity
                .and_then(|id| self.replay.facts.activations.get(id.activation.0 as usize))
                .is_some_and(|activation| {
                    activation.kind
                        != crate::sema::application_effect::ActivationKind::ControlTransfer
                }),
            "a resumption transfer is not its completed expression value",
        )?;
        let fresh = source_reception::construction(&syntax, work)
            .ok_or("receiver construction exceeded its work bound")?;
        let schema = self.replay.original_observed_source_schema_with_work(
            &syntax,
            observation,
            record.context,
            &self.sites,
            work,
        )?;
        Ok((schema, fresh))
    }
}

pub(super) fn input_select_key(
    key: &ArgumentKey,
    selected: &BTreeMap<String, ArgumentKey>,
    depth: usize,
) -> Check<ArgumentKey> {
    require(
        depth < 64,
        "call input substitution exceeds its source depth budget",
    )?;
    crate::sema::source_types::substitute_key(
        key,
        selected,
        &mut crate::sema::source_types::WorkLimit::new(4096),
    )
    .map_err(|error| format!("call input source substitution: {error}"))
}

pub(super) fn has_sources(facts: &SemanticFacts) -> Check<bool> {
    let sites = super::explicit_named::source_sites(facts)?;
    if !sites.calls.is_empty() {
        return Ok(true);
    }
    // Inspect genuine source headers before any input table or selector can
    // erase the obligation. Alias expansion is deferred to Replay::normalize.
    let mut pending: Vec<_> = facts
        .functions
        .iter()
        .flat_map(|function| {
            function
                .syntax
                .parameters
                .iter()
                .filter_map(|parameter| parameter.ty.as_ref())
        })
        .collect();
    let mut work = LIMIT;
    let mut aliases = BTreeSet::new();
    while let Some(syntax) = pending.pop() {
        work = work
            .checked_sub(1)
            .ok_or_else(|| "call input source predicate exceeds its work bound".to_owned())?;
        match &syntax.kind {
            TypeKind::Callable { .. } | TypeKind::Array { .. } => return Ok(true),
            TypeKind::Optional(element) => pending.push(element),
            TypeKind::Tuple(items) => pending.extend(items),
            TypeKind::Map { key, value } => pending.extend([key.as_ref(), value.as_ref()]),
            TypeKind::Record { fields, row } => {
                pending.extend(fields.iter().map(|field| &field.ty));
                pending.extend(row.iter().map(Box::as_ref));
            }
            TypeKind::Name { path, arguments } => {
                pending.extend(arguments);
                let name = path.join("::");
                if aliases.insert(name.clone())
                    && let Some(declaration) = facts.external_type_declarations.get(&name)
                    && !declaration.nominal
                    && !declaration.opaque
                {
                    pending.extend(declaration.value.iter());
                }
            }
            TypeKind::Computation(_) => return Ok(true),
            _ => {}
        }
    }
    Ok(false)
}

impl Replay<'_> {
    fn input_preparation(
        &self,
        event: crate::sema::copy_contract::CopyCallEventId,
        work: &mut usize,
    ) -> Check<&crate::sema::default_uses::CallArguments> {
        unique_source_record(
            &self.facts.call_arguments,
            work,
            "Source application has duplicate physical preparations",
            |row| row.source_event == event,
        )?
        .ok_or_else(|| "Source application has no physical preparation".to_owned())
    }

    fn operation_result_source(
        &self,
        observation: usize,
        work: &mut usize,
    ) -> Check<Option<ArgumentKey>> {
        let Some(event) = unique_source_record(
            &self.facts.copy_call_events,
            work,
            "operation result has duplicated physical call origins",
            |event| event.result_expression == Some(observation),
        )?
        else {
            return Ok(None);
        };
        let callee = event
            .callee_expression
            .and_then(|index| self.facts.expressions.get(index))
            .ok_or("operation result lost its actual callee")?;
        let [Callable::Builtin(name)] = callee.value.callables.as_slice() else {
            return Ok(None);
        };
        let Some(operation) = self.facts.operations.get(name) else {
            return Ok(None);
        };
        let signature = self.frames.signature(
            operation,
            callee
                .source_id
                .ok_or("operation result lost its original selector")?,
            event
                .callee_expression
                .and_then(|index| self.facts.evaluations.get(index))
                .ok_or("operation result callee context is absent")?
                .context,
            work,
        )?;
        let ArgumentKey::Callable { result, .. } = signature.declared else {
            return Err("operation result has no complete Source signature".into());
        };
        Ok(Some(*result))
    }
    fn input_operand_interval(
        &self,
        event: &super::super::copy_contract::CopyCallEvent,
        slot: usize,
        token: usize,
        context: InvocationContext,
        work: &mut usize,
    ) -> Check {
        // Replay construction has already checked the one canonical evaluation
        // algorithm. This consumer selects its exact bound prefix observation;
        // source spans and guessed callee-relative intervals play no role.
        let preparation = self.input_preparation(event.id, work)?;
        source_scan_work(work, preparation.evaluated.len())?;
        require(
            preparation.slots_bound
                && preparation
                    .supplied
                    .get(&(slot as u32))
                    .is_some_and(|supplied| {
                        supplied.expression == token
                            && preparation
                                .evaluated
                                .iter()
                                .filter(|step| {
                                    step.role != crate::sema::default_uses::EvaluationRole::Callee
                                        && step.observation == *supplied
                                })
                                .count()
                                == 1
                    }),
            "call input slot lost its exact evaluated operand",
        )?;
        let row = self.observations.row(token, work)?;
        require(
            event.result_expression.is_some_and(|result| token < result)
                && row.context == context
                && row.argument_of == Some((event.id, slot as u32)),
            "call input operand belongs to another actual invocation interval",
        )
    }
    fn input_static_environment<'a>(
        &'a self,
        call: &CopyInvocation,
    ) -> Check<&'a crate::sema::effect_identity::EffectInvocation> {
        let mut matching = self
            .facts
            .effect_invocations
            .iter()
            .filter(|row| row.invocation == Some(call.id));
        let Some(row) = matching.next() else {
            return Err("call input has no unique actual static environment".into());
        };
        require(
            matching.next().is_none(),
            "call input has duplicated actual static environments",
        )?;
        let function = self.function(call.target)?;
        require(
            row.function == call.target
                && row.verifying == call.declaration_probe
                && row.arguments.len() == function.syntax.generics.len(),
            "call input static environment has missing owned positions",
        )?;
        for (index, actual) in row.arguments.iter().enumerate() {
            let binder = self.binder(call.target, index as u32)?;
            require(
                actual.definition == call.target
                    && actual.index as usize == index
                    && actual.binder == binder.identity,
                "call input static environment changed a genuine owned binder",
            )?;
        }
        Ok(row)
    }

    fn input_static_arguments<'a>(
        &'a self,
        call: &CopyInvocation,
    ) -> Check<&'a [StaticArgumentWitness]> {
        Ok(&self.input_static_environment(call)?.arguments)
    }

    pub(super) fn input_selected_keys(
        &self,
        call: &CopyInvocation,
    ) -> Check<BTreeMap<String, ArgumentKey>> {
        let observed = self.input_static_environment(call)?;
        let mut selected = BTreeMap::new();
        for argument in &observed.arguments {
            if !self.input_type_sort(&argument.binder)? {
                continue;
            }
            if let Some(key) = &argument.key {
                selected.insert(argument.binder.clone(), key.clone());
            } else if let Some(bound) = self.facts.record_bounds.iter().find(|bound| {
                bound.definition == call.target
                    && bound.binder == argument.binder
                    && bound.generic_index == argument.index
            }) {
                let caller = self.input_caller_context(call)?;
                let context = InvocationContext {
                    owner: Some(CallableOwner::Function(call.target)),
                    invocation: Some(call.id),
                    ..caller
                };
                let identities: Vec<_> = self
                    .facts
                    .scoped_source_identities
                    .iter()
                    .enumerate()
                    .filter(|(ordinal, source)| {
                        source.id.0 as usize == *ordinal
                            && source.required == bound.id
                            && source.binder == argument.binder
                            && source.context == context
                            && !source.occurrences.is_empty()
                    })
                    .collect();
                if let [(_, source)] = identities.as_slice() {
                    require(
                        source_reception::complete(&source.key, &mut 4096).is_some(),
                        "call input scoped actual Type identity is incomplete",
                    )?;
                    selected.insert(argument.binder.clone(), source.key.clone());
                }
            }
        }
        for argument in &observed.captured_arguments {
            if !self.input_type_sort(&argument.binder)? {
                continue;
            }
            if let Some(key) = &argument.key {
                selected.insert(argument.binder.clone(), key.clone());
            }
        }
        for check in &self.facts.generic_bound_checks {
            if check.context.invocation == Some(call.id) {
                require(
                    check.context.owner == Some(CallableOwner::Function(call.target)),
                    "call input structural selection borrowed another owner",
                )?;
                for (binder, key) in &check.substitutions {
                    if let Some(previous) = selected.insert(binder.clone(), key.clone()) {
                        require(
                            previous == *key,
                            "call input structural and static source selections disagree",
                        )?;
                    }
                }
            }
        }
        Ok(selected)
    }

    fn input_caller_context(&self, call: &CopyInvocation) -> Check<InvocationContext> {
        let rows: Vec<_> = self
            .facts
            .invocation_calls
            .iter()
            .filter(|row| row.invocation == call.id)
            .collect();
        let [row] = rows.as_slice() else {
            return Err("call input lacks a unique original caller context".into());
        };
        require(
            row.caller_owner == call.caller_owner,
            "call input caller owner differs from the actual instance",
        )?;
        Ok(InvocationContext {
            owner: row.caller_owner,
            invocation: call.parent,
            closure: row.caller_closure,
            closure_invocation: row.caller_closure_invocation,
            default_use: row.default_use,
            budget_validation: false,
        })
    }

    pub(super) fn original_source_key(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::explicit_named::SourceSites<'_>,
    ) -> Check<ArgumentKey> {
        self.original_source_key_inner(
            expression,
            value,
            context,
            sites,
            &mut 4096,
            SourceVisit {
                depth: 0,
                observation: None,
            },
        )
    }

    pub(super) fn original_observed_source_key(
        &self,
        expression: &Expr,
        observation: usize,
        context: InvocationContext,
        sites: &super::explicit_named::SourceSites<'_>,
    ) -> Check<ArgumentKey> {
        self.original_observed_source_key_if_known(expression, observation, context, sites)?
            .ok_or_else(|| {
                format!(
                    "call input has no complete original source view at HIR {:?}",
                    expression.hir_id
                )
            })
    }

    /// Absence is a genuine unresolved source view, such as a lambda whose
    /// parameter types are selected only when it is later invoked. The exact
    /// initializer occurrence is still required before reporting that absence.
    pub(super) fn original_observed_source_key_if_known(
        &self,
        expression: &Expr,
        observation: usize,
        context: InvocationContext,
        sites: &super::explicit_named::SourceSites<'_>,
    ) -> Check<Option<ArgumentKey>> {
        self.original_observed_source_key_if_known_with_work(
            expression,
            observation,
            context,
            sites,
            &mut 4096,
        )
    }

    fn original_observed_source_key_if_known_with_work(
        &self,
        expression: &Expr,
        observation: usize,
        context: InvocationContext,
        sites: &super::explicit_named::SourceSites<'_>,
        work: &mut usize,
    ) -> Check<Option<ArgumentKey>> {
        let fact =
            self.facts.expressions.get(observation).ok_or_else(|| {
                "original Source root is outside its observation arena".to_owned()
            })?;
        self.original_source_root(expression, &fact.value, context, Some(observation), work)?;
        if let Some(key) = self.operation_result_source(observation, work)? {
            return Ok(Some(key));
        }
        self.original_source_key_inner_if_known(
            expression,
            &fact.value,
            context,
            sites,
            work,
            SourceVisit {
                depth: 0,
                observation: Some(observation),
            },
        )
    }

    /// Identify a physical root once. A known observation selects that exact
    /// occurrence; a legacy value query still rejects equal repeated values.
    pub(super) fn original_source_root(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        observation: Option<usize>,
        work: &mut usize,
    ) -> Check<usize> {
        let source = expression
            .hir_id
            .ok_or_else(|| "Source root has no genuine HIR identity".to_owned())?;
        if let Some(index) = observation {
            let row = self.observations.row(index, work)?;
            let fact = self
                .facts
                .expressions
                .get(index)
                .ok_or_else(|| "Source root is outside its observation arena".to_owned())?;
            let same = if matches!(fact.value.ty, Ty::NumericHole(_)) {
                self.numeric_source_value_matches(index, value, work)?
            } else {
                fact.value == *value
            };
            require(
                row.context == context && fact.source_id == Some(source) && same,
                "Source root borrowed another physical occurrence or complete value",
            )?;
            return Ok(index);
        }
        let candidates = self
            .observations
            .range(source, context, 0..usize::MAX, work)?;
        *work = work
            .checked_sub(candidates.len())
            .ok_or_else(|| "Source root candidates exceed their work bound".to_owned())?;
        let mut root = None;
        for &index in candidates {
            let original = &self.facts.expressions[index].value;
            let same = if matches!(original.ty, Ty::NumericHole(_)) {
                self.numeric_source_value_matches(index, value, work)?
            } else {
                *original == *value
            };
            if same {
                require(
                    root.replace(index).is_none(),
                    "Source has multiple matching physical root observations",
                )?;
            }
        }
        root.ok_or_else(|| "Source has no matching actual root observation".to_owned())
    }

    fn numeric_source_value_matches(
        &self,
        observation: usize,
        value: &Value,
        work: &mut usize,
    ) -> Check<bool> {
        let fact = &self.facts.expressions[observation];
        if crate::sema::evaluated::same_birth_value(&fact.value, value, work)
            .map_err(|error| format!("numeric birth comparison failed: {error}"))?
        {
            return Ok(true);
        }
        let observation = ril_compiler_core::ids::EvaluationOccurrenceId(
            u32::try_from(observation).map_err(|_| "numeric occurrence is outside its arena")?,
        );
        let (_, resolution) = crate::sema::numeric_selection::checked_resolution_in_query(
            self.facts,
            observation,
            &self.numeric_session,
            &self.source_query,
            work,
        )
        .map_err(|error| format!("numeric current view could not be replayed: {error}"))?
        .ok_or("numeric current view lost its actual hole resolution")?;
        let mut selected = crate::sema::evaluated::transport_value_at(
            &fact.value,
            &self.facts.allocation_history,
            fact.allocation_epoch,
            fact.allocation_epoch,
            work,
        )
        .map_err(|error| format!("numeric current view could not be copied: {error}"))?;
        resolution
            .apply(&mut selected, work)
            .map_err(|error| format!("numeric current view could not be selected: {error}"))?;
        crate::sema::evaluated::same_birth_value(&selected, value, work)
            .map_err(|error| format!("numeric current view comparison failed: {error}"))
    }

    fn original_source_key_inner(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        visit: SourceVisit,
    ) -> Check<ArgumentKey> {
        self.original_source_key_inner_if_known(expression, value, context, sites, work, visit)?
            .ok_or_else(|| {
                format!(
                    "call input has no complete original source view at HIR {:?}",
                    expression.hir_id
                )
            })
    }

    fn original_source_key_inner_if_known(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        visit: SourceVisit,
    ) -> Check<Option<ArgumentKey>> {
        let SourceVisit { depth, .. } = visit;
        require(
            depth < 64 && *work > 0,
            "original Source reconstruction exceeds its bound",
        )?;
        *work -= 1;
        if matches!(value.ty, Ty::NumericHole(_)) || !value.numeric.uses.is_empty() {
            let root =
                self.original_source_root(expression, value, context, visit.observation, work)?;
            if matches!(self.facts.expressions[root].value.ty, Ty::NumericHole(_)) {
                let (schema, _) = self.original_numeric_source_schema(root, context, work)?;
                return graph_sources::schema_work(work, |budget| schema.key_with_work(budget))
                    .map(Some);
            }
        }
        let key =
            match self.raw_original_source_key(expression, value, context, sites, work, visit)? {
                Some(key) => key,
                None if matches!(&value.ty, Ty::Generic(_)) => {
                    self.symbolic_input_source_key(expression, value, context)?
                }
                None => return Ok(None),
            };
        if self.source_optional_projection(expression, value, context, visit.observation, work)?
            && let ArgumentKey::Name { name, arguments } = &key
            && name == "Option"
            && arguments.len() == 1
        {
            return Ok(Some(arguments[0].clone()));
        }
        Ok(Some(key))
    }

    fn symbolic_input_source_key(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
    ) -> Check<ArgumentKey> {
        let Ty::Generic(identity) = &value.ty else {
            return Err("call input has no symbolic Type leaf".into());
        };
        self.type_binder(identity)?;
        require(
            self.facts
                .invocation_expressions
                .iter()
                .filter(|row| {
                    row.context == context
                        && self
                            .facts
                            .expressions
                            .get(row.expression)
                            .is_some_and(|fact| {
                                fact.source_id.is_some()
                                    && fact.source_id == expression.hir_id
                                    && fact.value.cause == value.cause
                                    && fact.value.ty == value.ty
                            })
                })
                .count()
                == 1,
            "call input symbolic Source lost its exact actual expression observation",
        )?;
        if let Some(key) =
            self.formal_input_path_key_if_known(expression, value, context, &mut 4096)?
        {
            let call = context
                .invocation
                .and_then(|id| self.facts.copy_invocations.get(id.0 as usize))
                .ok_or_else(|| "call input formal Source has no actual named entry".to_owned())?;
            let key = input_select_key(&key, &self.input_selected_keys(call)?, 0)?;
            require(
                matches!(&key, ArgumentKey::Binder {identity:actual,sort:StaticBinderSort::Type} if actual == identity),
                "call input formal Source selected another Type UID",
            )?;
            return Ok(key);
        }
        let ExprKind::Index { base, .. } = &expression.kind else {
            return Err("call input symbolic leaf has no proven Source operation".into());
        };
        let cause = self
            .facts
            .explanations
            .causes
            .get(value.cause.0 as usize)
            .ok_or_else(|| "call input symbolic index lost its actual cause".to_owned())?;
        let projections: Vec<_> = self
            .facts
            .generic_bound_projections
            .iter()
            .filter(|projection| {
                projection.context == context
                    && projection.span == base.span
                    && cause.parents.contains(&projection.output.value.cause)
            })
            .collect();
        let [projection] = projections.as_slice() else {
            return Err(
                "call input symbolic index has no unique actual bound member Source".into(),
            );
        };
        let bound = self
            .facts
            .record_bounds
            .get(projection.required.0 as usize)
            .filter(|bound| bound.id == projection.required)
            .ok_or_else(|| {
                "call input symbolic index lost its real bound declaration".to_owned()
            })?;
        let Slot::Field(label) = &projection.slot else {
            return Err("call input symbolic index borrowed a nonmember projection".into());
        };
        let field = bound
            .fields
            .iter()
            .find(|field| &field.label == label)
            .ok_or_else(|| {
                "call input symbolic index is absent from its actual bound".to_owned()
            })?;
        let raw = self.input_callable_source_key(&field.syntax, &bound.scope)?;
        require(
            raw == field.key,
            "call input symbolic index changed its original declared field coordinates",
        )?;
        let call = context
            .invocation
            .and_then(|id| self.facts.copy_invocations.get(id.0 as usize))
            .filter(|call| Some(CallableOwner::Function(call.target)) == context.owner)
            .ok_or_else(|| "call input symbolic index has no actual named scope".to_owned())?;
        let key = input_select_key(&raw, &self.input_selected_keys(call)?, 0)?;
        let ArgumentKey::Array { element, .. } = key else {
            return Err("call input symbolic index's actual source is not an array".into());
        };
        require(
            matches!(&*element, ArgumentKey::Binder { identity:actual, sort:StaticBinderSort::Type } if actual == identity),
            "call input symbolic index borrowed a different genuine Type identity",
        )?;
        Ok(*element)
    }

    /// A nonformal path has no result here. Once an actual named formal is
    /// selected, its identity, source projection and work failures are errors.
    fn formal_input_path_key_if_known(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        work: &mut usize,
    ) -> Check<Option<ArgumentKey>> {
        let Some(CallableOwner::Function(owner)) = context.owner else {
            return Ok(None);
        };
        let mut root = expression;
        let mut depth = 0usize;
        loop {
            require(
                depth < 64 && *work > 0,
                "call input formal Source applicability exceeds its bound",
            )?;
            *work -= 1;
            depth += 1;
            match &root.kind {
                ExprKind::Field { base, .. }
                | ExprKind::Index { base, .. }
                | ExprKind::ComputedField { base, .. } => root = base,
                ExprKind::Name(name) => {
                    if value.sources.len() != 1 {
                        return Ok(None);
                    }
                    let id = *value.sources.first().unwrap();
                    let binding = self
                        .facts
                        .bindings
                        .get(id)
                        .ok_or("call input formal Source candidate binding is absent")?;
                    if !binding.parameter
                        || binding.context.owner != Some(CallableOwner::Function(owner))
                        || !self.facts.scopes.get(&binding.owner).is_some_and(|scope| {
                            matches!(scope.origin, crate::sema::scopes::ScopeOrigin::Named(invocation)
                                if binding.context.invocation == Some(invocation))
                        })
                    {
                        return Ok(None);
                    }
                    require(
                        binding.name == *name,
                        "call input formal Source candidate borrowed another Name",
                    )?;
                    return self
                        .formal_input_path_key(expression, value.cause, context, work, 0)
                        .map(Some);
                }
                _ => return Ok(None),
            }
        }
    }

    fn formal_input_path_key(
        &self,
        expression: &Expr,
        cause: CauseId,
        context: InvocationContext,
        work: &mut usize,
        depth: usize,
    ) -> Check<ArgumentKey> {
        require(
            depth < 64 && *work > 0,
            "call input formal Source path exceeds its bound",
        )?;
        *work -= 1;
        let matching: Vec<_> = self
            .facts
            .invocation_expressions
            .iter()
            .filter_map(|row| {
                if row.context != context {
                    return None;
                }
                self.facts
                    .expressions
                    .get(row.expression)
                    .filter(|fact| {
                        fact.source_id.is_some()
                            && fact.source_id == expression.hir_id
                            && fact.value.cause == cause
                    })
                    .map(|fact| (row.expression, fact))
            })
            .collect();
        let [(observation, fact)] = matching.as_slice() else {
            return Err("call input formal Source path lost its exact observation".into());
        };
        if let ExprKind::Name(name) = &expression.kind {
            let binding = fact
                .value
                .sources
                .first()
                .and_then(|id| self.facts.bindings.get(*id))
                .filter(|binding| binding.parameter && binding.name == *name)
                .ok_or_else(|| {
                    "call input formal Source root is not its genuine parameter".to_owned()
                })?;
            let Some(CallableOwner::Function(owner)) = context.owner else {
                return Err("call input formal Source has no named owner".into());
            };
            self.parameter_declaration_context(
                expression,
                &fact.value,
                context,
                Some(*observation),
                work,
            )?;
            let function = self.function(owner)?;
            let parameter = function.syntax.parameters.iter().find(|parameter| parameter.pattern.hir_id.is_some() && parameter.pattern.hir_id == binding.pattern
                && matches!(&parameter.pattern.kind, ril_syntax::ast::PatternKind::Name(actual) if actual == name))
                .ok_or_else(|| "call input formal Source differs from its real header index".to_owned())?;
            // This legacy constraint path selects only the written type. Its
            // access mode and actual loan are independently replayed at entry.
            return self.input_callable_source_key(
                parameter
                    .ty
                    .as_ref()
                    .ok_or_else(|| "call input formal Source has no written type".to_owned())?,
                &self.scope(owner)?,
            );
        }
        require(
            self.facts.explanations.kinds.get(cause.0 as usize)
                == Some(&super::super::facts::CauseKind::Projection),
            "call input formal Source path lacks a genuine projection cause",
        )?;
        let parent = *self
            .facts
            .explanations
            .causes
            .get(cause.0 as usize)
            .and_then(|cause| cause.parents.first())
            .ok_or_else(|| "call input formal Source path lost its actual parent".to_owned())?;
        let (base, step) = match &expression.kind {
            ExprKind::Index { base, .. } => (base.as_ref(), None),
            ExprKind::Field { base, field, .. } => {
                (base.as_ref(), Some(Slot::Field(field.clone())))
            }
            ExprKind::ComputedField { base, key } => {
                let ExprKind::Literal(Literal::Integer(text)) = &key.kind else {
                    return Err("call input formal tuple path lacks a literal coordinate".into());
                };
                let coordinate = text.parse::<u32>().map_err(|_| {
                    "call input formal tuple coordinate is not canonical".to_owned()
                })?;
                require(
                    self.facts
                        .invocation_expressions
                        .iter()
                        .filter(|row| {
                            row.context == context
                                && self
                                    .facts
                                    .expressions
                                    .get(row.expression)
                                    .is_some_and(|fact| {
                                        fact.source_id.is_some()
                                            && fact.source_id == key.hir_id
                                            && fact.value.constant
                                                == Some(super::super::model::Constant::Integer(
                                                    i128::from(coordinate),
                                                ))
                                    })
                        })
                        .count()
                        == 1,
                    "call input formal tuple coordinate lost its actual observation",
                )?;
                (base.as_ref(), Some(Slot::Tuple(coordinate)))
            }
            _ => return Err("call input formal Source path has an unsupported operation".into()),
        };
        let key = self.formal_input_path_key(base, parent, context, work, depth + 1)?;
        let key = if matches!(&key, ArgumentKey::Name { .. }) {
            let hir = self
                .facts
                .semantic_hir
                .as_deref()
                .ok_or("formal alias has no original HIR")?;
            let mut limit = crate::sema::source_types::WorkLimit::new(*work);
            let key = crate::sema::source_types::declarations::expanded_key(&key, hir, &mut limit)
                .map_err(|error| format!("formal alias Source: {error}"))?;
            *work = limit.remaining();
            key
        } else {
            key
        };
        match (key, step) {
            (ArgumentKey::Array { element, .. }, None) => Ok(*element),
            (ArgumentKey::Tuple(items), Some(Slot::Tuple(index))) => items
                .get(index as usize)
                .cloned()
                .ok_or_else(|| "call input formal tuple path is outside its header".to_owned()),
            (ArgumentKey::Record { fields, .. }, Some(Slot::Field(label))) => fields
                .into_iter()
                .find(|field| field.0 == label)
                .map(|field| field.2)
                .ok_or_else(|| "call input formal field is absent from its header".to_owned()),
            (ArgumentKey::Binder { identity, .. }, Some(Slot::Field(label))) => {
                let bound = self
                    .facts
                    .record_bounds
                    .iter()
                    .find(|bound| bound.binder == identity)
                    .ok_or_else(|| {
                        "call input formal field has no real structural constraint".to_owned()
                    })?;
                let field = bound
                    .fields
                    .iter()
                    .find(|field| field.label == label)
                    .ok_or_else(|| {
                        "call input formal field is absent from its real bound".to_owned()
                    })?;
                let key = self.input_callable_source_key(&field.syntax, &bound.scope)?;
                require(
                    key == field.key,
                    "call input formal field changed its actual declared type",
                )?;
                Ok(key)
            }
            _ => Err("call input formal Source shape does not support this actual path".into()),
        }
    }

    fn source_optional_projection(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        observation: Option<usize>,
        work: &mut usize,
    ) -> Check<bool> {
        *work = work
            .checked_sub(self.facts.invocation_witnesses.len())
            .ok_or("optional Source receipts exceed their work bound")?;
        let projected = self.facts.invocation_witnesses.iter().any(|row| {
            row.context == context
                && matches!(&row.kind, super::super::effect_identity::InvocationWitnessKind::ImplicitUnwrap(proof)
                    if Some(proof.occurrence.source) == expression.hir_id && proof.cause == value.cause)
        });
        if !projected {
            return Ok(false);
        }
        let root = self.original_source_root(expression, value, context, observation, work)?;
        let record = self
            .facts
            .evaluations
            .get(root)
            .ok_or("optional Source lost its read")?;
        use crate::sema::source_types::{
            WorkLimit,
            projection_receipts::{ProjectionOccurrence, ProjectionReceipts},
        };
        let occurrence = ProjectionOccurrence {
            identity: record
                .identity
                .ok_or("optional Source has no original occurrence")?,
            context,
            cause: value.cause,
        };
        let mut budget = WorkLimit::new(*work);
        let result =
            ProjectionReceipts::from_facts(self.facts).unwrap_depth(occurrence, &mut budget);
        *work = budget.remaining();
        result
            .map(|depth| depth == 1)
            .map_err(|error| error.to_string())
    }

    fn raw_original_source_key(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        visit: SourceVisit,
    ) -> Check<Option<ArgumentKey>> {
        let SourceVisit { depth, .. } = visit;
        if let Some(key) =
            self.storage_binding_source_key_if_known(expression, value, context, visit.observation)
        {
            return key;
        }
        if !matches!(&value.ty, Ty::Generic(_))
            && matches!(
                &expression.kind,
                ExprKind::Field { .. } | ExprKind::Index { .. } | ExprKind::ComputedField { .. }
            )
            && let Some(key) =
                self.formal_input_path_key_if_known(expression, value, context, work)?
        {
            let call = context
                .invocation
                .and_then(|id| self.facts.copy_invocations.get(id.0 as usize))
                .ok_or("projected formal Source has no actual invocation")?;
            let key = input_select_key(&key, &self.input_selected_keys(call)?, 0)?;
            if matches!(&key, ArgumentKey::Name { .. }) {
                let hir = self
                    .facts
                    .semantic_hir
                    .as_deref()
                    .ok_or("projected alias has no original HIR")?;
                let mut limit = crate::sema::source_types::WorkLimit::new(*work);
                let key =
                    crate::sema::source_types::declarations::expanded_key(&key, hir, &mut limit)
                        .map_err(|error| format!("projected alias Source: {error}"))?;
                *work = limit.remaining();
                return Ok(Some(key));
            }
            return Ok(Some(key));
        }
        if let Some((source, hir)) = expression.hir_id.zip(self.facts.semantic_hir.as_deref()) {
            let mut limit = crate::sema::source_types::WorkLimit::new(*work);
            let declared =
                crate::sema::source_types::declarations::construction(source, hir, &mut limit);
            *work = limit.remaining();
            if let Some(key) =
                declared.map_err(|error| format!("typed construction Source: {error}"))?
            {
                self.original_source_root(expression, value, context, visit.observation, work)?;
                return Ok(Some(key));
            }
        }
        if let Some(key) =
            self.original_copy_source_key(expression, value, context, sites, work, visit)?
        {
            return Ok(key);
        }
        if value.source_type_witness.is_none()
            && let Some(key) =
                self.original_carrier_source_key(expression, value, context, sites, work, depth)?
        {
            return Ok(Some(key));
        }
        if let ExprKind::Name(name) = &expression.kind
            && self.facts.constant_pool.references.contains_key(name)
        {
            let original = self
                .facts
                .constant_pool
                .source_views
                .get(name)
                .ok_or_else(|| {
                    "constant reference has no sealed original Source view".to_owned()
                })?;
            require(
                original.validate_closed() && value.source_type_witness.as_ref() == Some(original),
                "constant reference changed its original per-reference Source view",
            )?;
            return self
                .input_callable_source_key(&original.syntax, &BoundScope::default())
                .map(Some);
        }
        if super::super::checker::BuiltinNameIndex::is_candidate(expression, work)? {
            let observation =
                self.original_source_root(expression, value, context, visit.observation, work)?;
            let names = self.builtin_source_names(work)?;
            let mut budget = WorkLimit::new(*work);
            let canonical = super::super::checker::original_canonical_builtin_source_key(
                self.facts,
                &super::super::checker::CanonicalBuiltinUse {
                    value,
                    actual: expression,
                    context,
                    observation,
                },
                &names,
                &mut budget,
            );
            *work = budget.remaining();
            drop(names);
            if let Some(key) = canonical? {
                return Ok(Some(key));
            }
        }
        if let ExprKind::Name(name) = &expression.kind
            && value.sources.len() == 1
        {
            let binding = value
                .sources
                .iter()
                .next()
                .and_then(|id| self.facts.bindings.get(*id))
                .ok_or_else(|| "call input source Name has no actual binding".to_owned())?;
            require(
                binding.name == *name,
                "call input source borrowed another Name binding",
            )?;
            if binding.parameter {
                let declaration = self.parameter_declaration_context(
                    expression,
                    value,
                    context,
                    visit.observation,
                    work,
                )?;
                if let Some(key) = self.operation_formal_source_key(binding, work)? {
                    return Ok(Some(key));
                }
                if matches!(declaration.owner, Some(CallableOwner::Lambda(_))) {
                    return self
                        .lambda_formal_source_key(expression, value, context, sites, work, visit)
                        .map(Some);
                }
                let Some(CallableOwner::Function(owner)) = declaration.owner else {
                    return Err("call input parameter has no genuine named header".into());
                };
                let function = self.function(owner)?;
                let (parameter_index, parameter) = function.syntax.parameters.iter().enumerate().find(|(_,parameter)|
                    binding.pattern.is_some() && parameter.pattern.hir_id == binding.pattern && matches!(&parameter.pattern.kind, ril_syntax::ast::PatternKind::Name(actual) if actual == name))
                    .ok_or_else(|| "call input parameter Name differs from its actual header".to_owned())?;
                let scope = self.scope(owner)?;
                let key = self.input_callable_source_key(
                    parameter.ty.as_ref().ok_or_else(|| {
                        "call input header has no complete type source".to_owned()
                    })?,
                    &scope,
                )?;
                if let Some(default) = self.parameter_preparation(binding, context, work)? {
                    require(
                        default.owner == declaration.owner
                            && default.target == Some(owner)
                            && parameter_index < default.parameter as usize,
                        "call input default borrowed a later or unrelated formal header",
                    )?;
                    if default.origin == DefaultOrigin::DeclarationProbe {
                        require(
                            default.entered.is_empty() && default.caller == declaration,
                            "declaration formal invented an actual body entry",
                        )?;
                        return input_select_key(
                            &key,
                            &self.declaration_default_selections(owner, default)?,
                            0,
                        )
                        .map(Some);
                    }
                    require(
                        default.status == CopyInvocationStatus::Completed,
                        "call input default has no completed receiving invocation",
                    )?;
                    let [entered] = default.entered.as_slice() else {
                        return Err(
                            "call input default has no unique receiving named instance".into()
                        );
                    };
                    let instance = self
                        .facts
                        .copy_invocations
                        .get(entered.0 as usize)
                        .filter(|call| call.id == *entered && call.target == owner)
                        .ok_or_else(|| {
                            "call input default entry differs from its actual owner".to_owned()
                        })?;
                    require(
                        instance.caller_activation.is_some_and(|parent| {
                            self.facts.scopes.parent(&binding.owner) == Some(&parent)
                        }),
                        "call input earlier formal belongs to another default activation",
                    )?;
                    let selected = self.input_selected_keys(instance)?;
                    for argument in default.arguments.iter().chain(&default.captured_arguments) {
                        require(
                            argument
                                .key
                                .as_ref()
                                .is_some_and(|key| selected.get(&argument.binder) == Some(key)),
                            "call input default and body selected different source identities",
                        )?;
                    }
                    return input_select_key(&key, &selected, 0).map(Some);
                }
                let instance = declaration
                    .invocation
                    .and_then(|id| self.facts.copy_invocations.get(id.0 as usize))
                    .filter(|call| call.target == owner)
                    .ok_or_else(|| {
                        "call input formal has no original header instance".to_owned()
                    })?;
                // This independently checks the real root/participants/epoch,
                // rather than consulting the binding's final mutable Value.
                if parameter.mode == ril_syntax::ast::ParameterMode::Read {
                    self.read_parameter_reception(
                        value,
                        expression,
                        declaration,
                        binding.owner,
                        instance.entry.allocation_epoch,
                    )?;
                    let original = instance.entry.arguments[parameter_index].value();
                    let original = if self.source_optional_projection(
                        expression,
                        value,
                        context,
                        visit.observation,
                        work,
                    )? {
                        original.option_payload.as_deref().ok_or_else(|| {
                            "call input optional projection lacks its original Some payload"
                                .to_owned()
                        })?
                    } else {
                        original
                    };
                    require(
                        value.callables == original.callables,
                        "call input readonly formal changed its original callable targets",
                    )?;
                } else {
                    let matching: Vec<_> = self
                        .facts
                        .invocation_loan_starts
                        .iter()
                        .filter(|loan| {
                            loan.owner == declaration.owner
                                && loan.named == Some(instance.id)
                                && loan.parameter as usize == parameter_index
                                && loan.activation == binding.owner
                                && loan.bindings.contains(value.sources.first().unwrap())
                        })
                        .collect();
                    let [loan] = matching.as_slice() else {
                        return Err(
                            "call input mutable formal lost its exact original loan entry".into(),
                        );
                    };
                    let entry = instance
                        .entry
                        .arguments
                        .get(parameter_index)
                        .ok_or_else(|| {
                            "call input mutable formal lost its whole entry".to_owned()
                        })?;
                    require(
                        loan.retained
                            == (parameter.mode == ril_syntax::ast::ParameterMode::SharedMut)
                            && loan.origins == entry.value().origins
                            && loan.allocation_epoch == instance.entry.allocation_epoch
                            && value.origins == loan.origins
                            && value.participants
                                == BTreeSet::from([super::super::facts::Participant::Loan(
                                    loan.loan,
                                )])
                            && binding.forwarded == entry.value().sources,
                        "call input mutable formal changed its source or actual loan participant",
                    )?;
                }
                return input_select_key(&key, &self.input_selected_keys(instance)?, 0).map(Some);
            }
            let declared: Vec<_> = sites
                .bindings
                .iter()
                .filter(|site| site.binding.pattern.span == binding.span)
                .collect();
            if let [declaration] = declared.as_slice()
                && let Some(syntax) = &declaration.binding.ty
            {
                let scope = self.lambda_input_scope(declaration.owner, work)?;
                let key = self.input_callable_source_key(syntax, &scope)?;
                let selected = self.binding_source_selections(binding, declaration.owner)?;
                return input_select_key(&key, &selected, 0).map(Some);
            }
            if let [crate::sema::model::Callable::Named(index)] = value.callables.as_slice() {
                let function = self
                    .facts
                    .functions
                    .get(*index)
                    .ok_or_else(|| "call input function source target is missing".to_owned())?;
                require(
                    binding.span == function.syntax.span && binding.name == function.syntax.name,
                    "call input callable source is an unproved alias",
                )?;
                let mut parameters = function.syntax.parameters.clone();
                for parameter in &mut parameters {
                    parameter.default = None;
                }
                let syntax = TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span: expression.span,
                    kind: TypeKind::Callable {
                        parameters,
                        result: function.syntax.return_type.clone().map(Box::new),
                        annotations: function.syntax.annotations.clone(),
                    },
                };
                return self
                    .input_callable_source_key(&syntax, &self.scope(function.definition)?)
                    .map(Some);
            }
        }
        if let Some(key) = self.inferred_lambda_source_key(expression, value, context, sites)? {
            return Ok(Some(key));
        }
        if let Some(application) = AstApplication::from_ast(expression) {
            let callee_syntax = application.callee;
            let calls: Vec<_> = self
                .facts
                .copy_call_events
                .iter()
                .filter(|call| {
                    call.matches_source(expression)
                        && call.owner == context.owner
                        && call.parent == context.invocation
                })
                .collect();
            if let [source] = calls.as_slice()
                && let Some(target) = source.target
            {
                let function = self.function(target)?;
                if let Some(result) = &function.syntax.return_type {
                    let causes = self.producing_result_causes(value.cause, work)?;
                    let instances: Vec<_> = self
                        .facts
                        .copy_invocations
                        .iter()
                        .filter(|call| call.source_event == Some(source.id))
                        .filter(|call| {
                            call.result
                                .as_ref()
                                .is_some_and(|result| causes.contains(&result.value.cause.0))
                        })
                        .collect();
                    if let [instance] = instances.as_slice() {
                        let key = self.input_callable_source_key(result, &self.scope(target)?)?;
                        let selected = self.producing_input_selected_keys(instance, value, work)?;
                        let declared = input_select_key(&key, &selected, 0)?;
                        let callee = source
                            .callee_expression
                            .and_then(|index| self.facts.expressions.get(index))
                            .ok_or_else(|| {
                                "call input returned Source lost its exact callee".to_owned()
                            })?;
                        require(
                            callee.source_id.is_some()
                                && callee.source_id == callee_syntax.hir_id
                                && self
                                    .facts
                                    .invocation_expressions
                                    .iter()
                                    .filter(|row| {
                                        Some(row.expression) == source.callee_expression
                                            && row.context == context
                                    })
                                    .count()
                                    == 1,
                            "call input returned Source borrowed another callee context",
                        )?;
                        let mut base = callee_syntax;
                        while let ExprKind::Generic { base: inner, .. } = &base.kind {
                            base = inner;
                        }
                        let public = if base.hir_id == callee.source_id {
                            self.original_observed_source_key(
                                base,
                                source.callee_expression.unwrap(),
                                context,
                                sites,
                            )?
                        } else {
                            self.original_source_key(base, &callee.value, context, sites)?
                        };
                        let ArgumentKey::Callable { result: public, .. } = public else {
                            return Err("call input returned Source has no public Fn result".into());
                        };
                        let public = input_select_key(&public, &selected, 0)?;
                        self.validate_producing_result_transport(instance, value, work)?;
                        if let Ty::Generic(identity) = &value.ty {
                            self.type_binder(identity)?;
                            require(
                                matches!(&public, ArgumentKey::Binder { identity:actual,sort:StaticBinderSort::Type } if actual == identity)
                                    && declared == public,
                                "call input returned Source differs from its genuine selected Type UID",
                            )?;
                        }
                        return Ok(Some(public));
                    }
                }
            }
        }
        if value.source_type_witness.is_none()
            && let Some(key) =
                self.original_composite_source_key(expression, value, context, sites, work, visit)?
        {
            return Ok(Some(key));
        }
        let Some(witness) = value.source_type_witness.as_ref() else {
            return Ok(None);
        };
        require(
            witness.validate_closed()
                && crate::sema::source_type_validation::resolved_names(
                    witness,
                    &self.facts.external_type_declarations,
                ),
            "call input complete witness has inconsistent or unresolved source names",
        )?;
        self.input_callable_source_key(&witness.syntax, &BoundScope::default())
            .map(Some)
    }

    pub(super) fn input_value_transport(
        &self,
        original: &Value,
        actual: &Value,
        from: usize,
        to: usize,
    ) -> Check {
        require(
            original.cause == actual.cause,
            "call input entry changed its original cause",
        )?;
        self.input_view_transport(original, actual, from, to)
    }

    pub(super) fn input_view_transport(
        &self,
        original: &Value,
        actual: &Value,
        from: usize,
        to: usize,
    ) -> Check {
        require(
            from <= to && to <= self.facts.allocation_history.len(),
            "call input source epoch is outside its actual interval",
        )?;
        let mut origins = original.origins.clone();
        for &(recent, older) in &self.facts.allocation_history[from..to] {
            if origins.nodes.remove(&recent) {
                origins.nodes.insert(older);
            }
            for alternatives in origins.choices.values_mut() {
                for alternative in alternatives {
                    if alternative.remove(&recent) {
                        alternative.insert(older);
                    }
                }
            }
        }
        require(
            origins == actual.origins
                && original.sources == actual.sources
                && original.results == actual.results
                && original.outer_results == actual.outer_results
                && original.source_type_witness == actual.source_type_witness,
            "call input entry differs from its original physical expression or source schema",
        )
    }

    pub(super) fn call_input_sources(&self) -> Result<(), Failure> {
        let fallback = self
            .facts
            .functions
            .first()
            .map(|function| function.syntax.span)
            .unwrap_or(Span {
                file: ril_compiler_core::source::FileId(0),
                start: 0,
                end: 0,
            });
        let sites = super::explicit_named::source_sites(self.facts)
            .map_err(|message| (fallback, None, message))?;
        let mut input_work = 16_000_000usize;
        self.producing_result_contexts(&sites, &mut input_work)
            .map_err(|message| (fallback, None, message))?;
        // The frozen Program, rather than an arena's current contents, supplies
        // the coverage obligation. A deleted event/instance cannot make a real
        // invocation disappear from this replay.
        for site in &sites.calls {
            source_scan_work(
                &mut input_work,
                self.facts.expressions.len() + self.facts.copy_call_events.len(),
            )
            .map_err(|message| (site.expression.span, None, message))?;
            if !self.facts.expressions.iter().any(|observed| {
                observed.source_id.is_some() && observed.source_id == site.expression.hir_id
            }) {
                // An abrupt earlier operand can leave this static child
                // unevaluated. Actual root coverage is checked independently.
                continue;
            }
            require(
                self.facts.copy_call_events.iter().any(|event| {
                    event.owner == Some(site.owner) && event.matches_source(site.expression)
                }),
                "call input Source lost every actual event for a genuine Call",
            )
            .map_err(|message| (site.expression.span, None, message))?;
        }
        for event in &self.facts.copy_call_events {
            let mut run = || -> Check {
                let site = unique_source_record(
                    &sites.calls,
                    &mut input_work,
                    "call input event has multiple genuine Calls in its real owner",
                    |site| event.owner == Some(site.owner) && event.matches_source(site.expression),
                )?
                .ok_or("call input event has no genuine Call in its real owner")?;
                let application = AstApplication::from_ast(site.expression)
                    .ok_or_else(|| "source application has no original shape".to_owned())?;
                let syntax = application.callee;
                let preparation = self.input_preparation(event.id, &mut input_work)?;
                if !preparation.slots_bound || !preparation.evaluation_complete {
                    source_scan_work(
                        &mut input_work,
                        self.facts.copy_invocations.len() + self.facts.closure_invocations.len(),
                    )?;
                    require(
                        !self
                            .facts
                            .copy_invocations
                            .iter()
                            .any(|call| call.source_event == Some(event.id))
                            && !self
                                .facts
                                .closure_invocations
                                .iter()
                                .any(|call| call.source_event == Some(event.id)),
                        "abrupt application prefix claims an entered callable body",
                    )?;
                    return Ok(());
                }
                let token = event
                    .callee_expression
                    .ok_or_else(|| "call input event lost its actual callee token".to_owned())?;
                let callee = self.facts.expressions.get(token).ok_or_else(|| {
                    "call input callee token is outside the expression arena".to_owned()
                })?;
                let row = self.observations.row(token, &mut input_work)?;
                require(
                    callee.source_id.is_some()
                        && callee.source_id == syntax.hir_id
                        && row.context.owner == event.owner
                        && row.context.invocation == event.parent,
                    "call input callee token belongs to another Source occurrence or caller",
                )?;
                source_scan_work(
                    &mut input_work,
                    callee.value.callables.len() + self.facts.copy_invocations.len(),
                )?;
                let targets: BTreeSet<_> = callee
                    .value
                    .callables
                    .iter()
                    .filter_map(|callable| {
                        if let crate::sema::model::Callable::Named(index) = callable {
                            self.facts
                                .functions
                                .get(*index)
                                .map(|function| function.definition)
                        } else {
                            None
                        }
                    })
                    .collect();
                let expected_target = if callee.value.callables.len() == 1 && targets.len() == 1 {
                    targets.first().copied()
                } else {
                    None
                };
                require(
                    event.target == expected_target,
                    "call input event changed its actual named callee identity",
                )?;
                require(
                    self.facts
                        .copy_invocations
                        .iter()
                        .filter(|call| call.source_event == Some(event.id))
                        .all(|call| targets.contains(&call.target)),
                    "call input instance targets a function absent from its genuine callee",
                )?;
                if let Some(target) = expected_target
                    && let ExprKind::Name(name) = &syntax.kind
                    && callee.value.sources.len() == 1
                {
                    source_scan_work(&mut input_work, self.facts.functions.len())?;
                    let binding = callee
                        .value
                        .sources
                        .first()
                        .and_then(|id| self.facts.bindings.get(*id))
                        .ok_or_else(|| {
                            "call input named callee lost its actual source binding".to_owned()
                        })?;
                    require(
                        binding.name == *name,
                        "call input named callee borrowed another Source Name",
                    )?;
                    if self
                        .facts
                        .functions
                        .iter()
                        .any(|function| function.syntax.span == binding.span)
                    {
                        let function = self.function(target)?;
                        require(
                            !binding.parameter
                                && binding.span == function.syntax.span
                                && binding.name == function.syntax.name,
                            "call input named callee changed its genuine declaration identity",
                        )?;
                    }
                }
                for target in targets {
                    source_scan_work(&mut input_work, self.facts.copy_invocations.len())?;
                    require(
                        self.facts.copy_invocations.iter().any(|call| {
                            call.source_event == Some(event.id) && call.target == target
                        }),
                        "call input Source lost an actual named body instance",
                    )?;
                }
                self.constructor_input_sources(
                    event,
                    site.expression,
                    &callee.value,
                    row.context,
                    &sites,
                )?;
                self.storage_input_sources(
                    event,
                    site.expression,
                    &callee.value,
                    row.context,
                    &sites,
                )?;
                self.open_carrier_source_result(
                    event,
                    site.expression,
                    &callee.value,
                    row.context,
                    &sites,
                )?;
                if expected_target.is_none()
                    && callee.value.callables.iter().any(|callable| {
                        !matches!(
                            callable,
                            crate::sema::model::Callable::Builtin(_)
                                | crate::sema::model::Callable::Constructor(_)
                        )
                    })
                {
                    self.public_input_sources(
                        event,
                        site.expression,
                        &callee.value,
                        row.context,
                        &sites,
                        &mut input_work,
                    )?;
                }
                Ok(())
            };
            run().map_err(|message| (event.span, None, message))?;
        }
        for call in &self.facts.copy_invocations {
            let mut run = || -> Check {
                let function = self.function(call.target)?;
                if function.syntax.parameters.is_empty() {
                    return Ok(());
                }
                // Genuine header entries do not claim an actual input receipt.
                if call.span == function.syntax.span
                    && call.parent.is_none()
                    && call.source_event.is_none()
                    && call.caller_owner.is_none()
                    && call.caller_activation.is_none()
                {
                    return Ok(());
                }
                let schemas = self.named_input_source_schemas(call, &sites, &mut input_work)?;
                let expected = &schemas.expected;
                input_work = input_work
                    .checked_sub(expected.len())
                    .ok_or("call input source obligations exceed their work bound")?;
                let required = expected
                    .iter()
                    .map(|source| {
                        source.as_ref().map_or(Ok(false), |(schema, _)| {
                            self.input_graph_required(schema, &mut input_work)
                        })
                    })
                    .collect::<Check<Vec<_>>>()?;
                if required.iter().all(|required| !required) {
                    return Ok(());
                }
                if matches!(
                    call.entry.origin,
                    crate::sema::application_effect::EntryOrigin::SignatureProbe(_)
                ) {
                    require(
                        call.source_event.is_none() && !call.declaration_probe,
                        "signature assumption claimed a physical application",
                    )?;
                    for (slot, expected) in expected.iter().enumerate() {
                        let Some((expected, _)) = expected else {
                            continue;
                        };
                        if !required[slot] {
                            continue;
                        }
                        let hir = self
                            .facts
                            .semantic_hir
                            .as_deref()
                            .ok_or("signature input has no original HIR")?;
                        let actual = graph_sources::schema_work(&mut input_work, |budget| {
                            crate::sema::application_effect::signature_assumption(
                                call,
                                slot,
                                hir,
                                &self.facts.bindings,
                                self.facts.allocation_history.len(),
                                budget,
                            )
                        })?;
                        require(
                            function
                                .syntax
                                .parameters
                                .get(slot)
                                .is_some_and(|parameter| parameter.mode == actual.mode),
                            "signature input changed its original parameter mode",
                        )?;
                        let scope =
                            reception::environment_scope(actual.environment, &mut input_work)?;
                        let root = self.source_type_header(
                            actual.header,
                            &scope,
                            actual.environment.clone(),
                            &mut input_work,
                        )?;
                        let actual = (
                            graph_sources::schema_work(&mut input_work, |budget| {
                                actual.parameter_schema(&root.0, budget)
                            })?,
                            root.1,
                        );
                        self.receive_input_source_graph(
                            expected,
                            Some(&actual),
                            &source_reception::Construction::Opaque,
                            &mut input_work,
                        )?;
                        let (raw, _) = schemas.raw[slot]
                            .as_ref()
                            .ok_or("signature input lost its original target header")?;
                        self.input_row_graph_equations(
                            raw,
                            &actual.0,
                            &schemas.selected,
                            call.target,
                            &mut input_work,
                        )?;
                    }
                    return Ok(());
                }
                if matches!(
                    call.entry.origin,
                    crate::sema::application_effect::EntryOrigin::Generated { .. }
                ) {
                    for (index, expected) in expected.iter().enumerate() {
                        let Some((expected, _)) = expected else {
                            continue;
                        };
                        if !required[index] {
                            continue;
                        }
                        let actual =
                            self.named_entry_source_schema(call, index, &sites, &mut input_work)?;
                        self.receive_input_source_graph(
                            expected,
                            Some(&actual),
                            &source_reception::Construction::Opaque,
                            &mut input_work,
                        )?;
                        let (raw, _) = schemas.raw[index]
                            .as_ref()
                            .ok_or("generated input lost its original source header")?;
                        self.input_row_graph_equations(
                            raw,
                            &actual.0,
                            &schemas.selected,
                            call.target,
                            &mut input_work,
                        )?;
                    }
                    return Ok(());
                }
                let event = call
                    .source_event
                    .and_then(|id| {
                        self.facts
                            .copy_call_events
                            .get(id.0 as usize)
                            .filter(|event| event.id == id)
                    })
                    .ok_or_else(|| "call input has no actual application identity".to_owned())?;
                let context = self.input_caller_context(call)?;
                require(
                    event.owner == context.owner && event.parent == context.invocation,
                    "call input source event belongs to another actual caller",
                )?;
                let site = unique_source_record(
                    &sites.calls,
                    &mut input_work,
                    "call input has multiple real Call ASTs in its owner",
                    |site| Some(site.owner) == event.owner && event.matches_source(site.expression),
                )?
                .ok_or("call input has no real Call AST in its owner")?;
                let application = AstApplication::from_ast(site.expression)
                    .ok_or_else(|| "source invocation has no actual application".to_owned())?;
                let arguments = &application.operands;
                let preparation = self.input_preparation(event.id, &mut input_work)?;
                require(
                    preparation.target == event.target
                        && preparation.evaluation_complete
                        && preparation.slots.len() == function.syntax.parameters.len()
                        && call.entry.arguments.len() == function.syntax.parameters.len(),
                    "call input preparation changed its target, completion or full arity",
                )?;
                let callee = event
                    .callee_expression
                    .and_then(|index| self.facts.expressions.get(index))
                    .ok_or_else(|| "call input has no physical callee expression".to_owned())?;
                let parameters = callee
                    .value
                    .signature
                    .as_ref()
                    .unwrap_or(&function.syntax.parameters);
                source_scan_work(&mut input_work, parameters.len() + arguments.len())?;
                let mut written = BTreeMap::new();
                let labels = crate::hir::application::parameter_labels(parameters);
                let mapping = crate::hir::application::bind_slots(
                    &labels,
                    arguments.iter().map(|argument| argument.label),
                );
                for (argument, index) in arguments.iter().zip(mapping) {
                    let index = index.map_err(|code|format!("call input label/position is outside its actual public signature: {code}"))?;
                    require(
                        written.insert(index, argument.expression).is_none(),
                        "call input parameter is supplied twice",
                    )?;
                }
                require(
                    preparation.supplied.len() == written.len(),
                    "call input supplied tokens have missing or excess actual slots",
                )?;
                for (index, expected) in expected.iter().enumerate() {
                    let Some((expected, _)) = expected else {
                        continue;
                    };
                    if !required[index] {
                        continue;
                    }
                    let entry = call.entry.arguments.get(index).ok_or_else(|| {
                        "call input entry lacks its original whole argument".to_owned()
                    })?;
                    let (syntax, original, epoch, source_context, observation) = match preparation
                        .slots
                        .get(index)
                    {
                        Some(ArgumentSource::Supplied) => {
                            let syntax = written.get(&index).ok_or_else(|| {
                                "call input supplied slot has no real written argument".to_owned()
                            })?;
                            let token =
                                preparation.supplied.get(&(index as u32)).ok_or_else(|| {
                                    "call input supplied slot lost its actual expression token"
                                        .to_owned()
                                })?;
                            let expression = self
                                .facts
                                .expressions
                                .get(token.expression)
                                .ok_or_else(|| {
                                    "call input supplied expression token is missing".to_owned()
                                })?;
                            let observed_context =
                                self.observations.row(token.expression, &mut input_work)?;
                            require(
                                expression.source_id.is_some()
                                    && expression.source_id == syntax.hir_id
                                    && observed_context.context == context
                                    && observed_context.argument_of
                                        == Some((event.id, index as u32)),
                                "call input supplied token belongs to another Source occurrence or caller",
                            )?;
                            self.input_operand_interval(
                                event,
                                index,
                                token.expression,
                                context,
                                &mut input_work,
                            )?;
                            (
                                *syntax,
                                expression.value.value(),
                                token.allocation_epoch,
                                context,
                                token.expression,
                            )
                        }
                        Some(ArgumentSource::Default(id)) => {
                            require(
                                !preparation.supplied.contains_key(&(index as u32)),
                                "call input default slot borrowed a supplied token",
                            )?;
                            let default = self
                                .facts
                                .default_uses
                                .get(id.0 as usize)
                                .filter(|default| default.id == *id)
                                .ok_or_else(|| {
                                    "call input default identity is missing".to_owned()
                                })?;
                            require(
                                default.origin == DefaultOrigin::Call(event.id)
                                    && default.target == Some(call.target)
                                    && default.parameter as usize == index
                                    && default.caller == context
                                    && default.entered.contains(&call.id)
                                    && default.evaluation_complete
                                    && default.status == CopyInvocationStatus::Completed,
                                "call input default borrowed another event, target, parameter or completed body",
                            )?;
                            let syntax = function.syntax.parameters[index]
                                .default
                                .as_ref()
                                .ok_or_else(|| {
                                    "call input default has no genuine declared expression"
                                        .to_owned()
                                })?;
                            require(
                                default.span == syntax.span,
                                "call input default source differs from its real parameter",
                            )?;
                            let snapshot = default.result.as_ref().ok_or_else(|| {
                                "call input default has no original result snapshot".to_owned()
                            })?;
                            (
                                syntax,
                                &snapshot.value,
                                default.result_allocation_epoch.ok_or_else(|| {
                                    "call input default has no actual completion epoch".to_owned()
                                })?,
                                InvocationContext {
                                    owner: default.owner,
                                    default_use: Some(*id),
                                    ..default.caller
                                },
                                default.result_expression.ok_or(
                                    "call input default lost its physical result observation",
                                )?,
                            )
                        }
                        _ => {
                            return Err(
                                "call input full-source slot is missing its physical input source"
                                    .into(),
                            );
                        }
                    };
                    self.input_value_transport(
                        original,
                        entry.value(),
                        epoch,
                        call.entry.allocation_epoch,
                    )?;
                    if let Some(actual) = self.input_source_reception_schema(
                        expected,
                        reception::InputSourceOccurrence {
                            expression: syntax,
                            value: original,
                            context: source_context,
                            observation,
                        },
                        &sites,
                        &mut input_work,
                    )? {
                        let (raw, _) = schemas.raw[index]
                            .as_ref()
                            .ok_or("call input lost its original source header")?;
                        self.input_row_graph_equations(
                            raw,
                            &actual.0,
                            &schemas.selected,
                            call.target,
                            &mut input_work,
                        )?;
                    }
                }
                Ok(())
            };
            run().map_err(|message| (call.span, None, message))?;
        }
        Ok(())
    }

    fn public_input_sources(
        &self,
        event: &super::super::copy_contract::CopyCallEvent,
        syntax: &Expr,
        callee: &Value,
        context: InvocationContext,
        sites: &super::explicit_named::SourceSites<'_>,
        work: &mut usize,
    ) -> Check {
        let application = AstApplication::from_ast(syntax)
            .ok_or_else(|| "public callable input has no actual application".to_owned())?;
        let callee_syntax = application.callee;
        let arguments = &application.operands;
        let parameters = self.public_input_source_schemas(
            callee_syntax,
            callee,
            context,
            sites,
            event.callee_expression,
            work,
        )?;
        let required = parameters
            .iter()
            .map(|(_, source)| {
                source.as_ref().map_or(Ok(false), |(schema, _)| {
                    self.input_graph_required(schema, work)
                })
            })
            .collect::<Check<Vec<_>>>()?;
        if required.iter().all(|required| !required) {
            return Ok(());
        }
        let preparation = self.input_preparation(event.id, work)?;
        require(
            preparation.target == event.target
                && preparation.evaluation_complete
                && preparation.slots.len() == parameters.len(),
            "public callable preparation changed its target, arity or completion",
        )?;
        let mut written = BTreeMap::new();
        source_scan_work(work, parameters.len() + arguments.len())?;
        let labels = crate::sema::builtin_sources::parameter_labels(callee, parameters.len());
        let mapping = crate::hir::application::bind_slots(
            &labels,
            arguments.iter().map(|argument| argument.label),
        );
        for (argument, slot) in arguments.iter().zip(mapping) {
            let slot = slot.map_err(|code| {
                format!(
                    "public callable Source label/position is outside its actual signature: {code}"
                )
            })?;
            require(
                written.insert(slot, argument.expression).is_none(),
                "public callable Source supplies one slot twice",
            )?;
        }
        require(
            preparation.supplied.len() == written.len(),
            "public callable Source lost or added a supplied operand",
        )?;
        for (slot, (_, expected)) in parameters.iter().enumerate() {
            let Some((expected, _)) = expected else {
                continue;
            };
            if !required[slot] {
                continue;
            }
            let (actual_syntax, value, actual_context, observation) = match preparation
                .slots
                .get(slot)
            {
                Some(ArgumentSource::Supplied) => {
                    let actual_syntax = written.get(&slot).ok_or_else(|| {
                        "public callable input lacks its written operand".to_owned()
                    })?;
                    let token = preparation.supplied.get(&(slot as u32)).ok_or_else(|| {
                        "public callable input lost its actual expression token".to_owned()
                    })?;
                    let value = self
                        .facts
                        .expressions
                        .get(token.expression)
                        .ok_or_else(|| {
                            "public callable input token is outside its arena".to_owned()
                        })?;
                    let row = self.observations.row(token.expression, work)?;
                    require(
                        value.source_id.is_some()
                            && value.source_id == actual_syntax.hir_id
                            && token.allocation_epoch <= self.facts.allocation_history.len()
                            && row.context == context
                            && row.argument_of == Some((event.id, slot as u32)),
                        "public callable input token borrowed another actual event or slot",
                    )?;
                    self.input_operand_interval(event, slot, token.expression, context, work)?;
                    (
                        *actual_syntax,
                        value.value.value(),
                        context,
                        token.expression,
                    )
                }
                Some(ArgumentSource::Default(id)) => {
                    let default = self
                        .facts
                        .default_uses
                        .get(id.0 as usize)
                        .filter(|default| default.id == *id)
                        .ok_or_else(|| {
                            "public callable input lost its actual default".to_owned()
                        })?;
                    require(
                        default.origin == DefaultOrigin::Call(event.id)
                            && default.target == event.target
                            && default.parameter as usize == slot
                            && default.caller == context
                            && default.evaluation_complete
                            && default.status == CopyInvocationStatus::Completed
                            && default
                                .result_allocation_epoch
                                .is_some_and(|epoch| epoch <= self.facts.allocation_history.len())
                            && !preparation.supplied.contains_key(&(slot as u32)),
                        "public callable input default belongs to another occurrence or incomplete evaluation",
                    )?;
                    if matches!(default.owner, Some(CallableOwner::Lambda(_))) {
                        source_scan_work(
                            work,
                            self.facts
                                .closure_invocations
                                .len()
                                .checked_mul(16)
                                .ok_or("default closure entry lookup exceeds its work bound")?,
                        )?;
                        let mut entries = self.facts.closure_invocations.iter().filter(|call| {
                            self.facts
                                .closures
                                .get(call.closure)
                                .is_some_and(|closure| {
                                    crate::sema::default_uses::closure_entry_uses(
                                        default, call, closure,
                                    )
                                })
                        });
                        require(
                            entries
                                .next()
                                .is_some_and(|call| call.status == CopyInvocationStatus::Completed)
                                && entries
                                    .all(|call| call.status == CopyInvocationStatus::Completed),
                            "public callable default lacks its actual completed closure entry",
                        )?;
                    }
                    let actual_syntax = callee
                        .signature
                        .as_ref()
                        .and_then(|parameters| parameters.get(slot))
                        .and_then(|parameter| parameter.default.as_ref())
                        .ok_or_else(|| {
                            "public callable default lacks its original signature Source".to_owned()
                        })?;
                    require(
                        actual_syntax.span == default.span,
                        "public callable default changed its actual declaration",
                    )?;
                    let value = default
                        .result
                        .as_ref()
                        .ok_or_else(|| "public callable default lost its result".to_owned())?;
                    (
                        actual_syntax,
                        &value.value,
                        InvocationContext {
                            owner: default.owner,
                            default_use: Some(*id),
                            ..default.caller
                        },
                        default.result_expression.ok_or(
                            "public callable default lost its physical result observation",
                        )?,
                    )
                }
                _ => return Err("public callable input lacks a full-source operand".into()),
            };
            self.input_source_reception_schema(
                expected,
                reception::InputSourceOccurrence {
                    expression: actual_syntax,
                    value,
                    context: actual_context,
                    observation,
                },
                sites,
                work,
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_operand_sources_never_hide_missing_occurrences_or_exhausted_work() {
        for case in [
            "tests/regressions/source-observations.ril::matching-variable-replacement",
            "tests/conformance/collections.ril::literal-and-lookup",
        ] {
            let source = ril_test::case_source(case);
            let program = crate::Session::new(source.as_bytes().to_vec())
                .verify()
                .unwrap();
            let facts = program.facts();
            let sources = OriginalOperandSources::new(facts).unwrap();
            let (observation, source) = facts
                .expressions
                .iter()
                .enumerate()
                .find_map(|(index, fact)| {
                    let source = fact.source_id?;
                    let syntax = sources.sites.expressions.get(&source)?;
                    match &syntax.kind {
                        ExprKind::Array(items) if items.is_empty() => Some((index, source)),
                        ExprKind::Map(items) if items.is_empty() => Some((index, source)),
                        _ => None,
                    }
                })
                .expect("fixture must evaluate a real empty collection");
            sources.observed(source, observation).unwrap();
            for initial in [0, 1] {
                let mut work = initial;
                assert!(
                    sources
                        .observed_with_work(source, observation, &mut work)
                        .is_err(),
                    "{case}: empty construction cannot waive its observation work"
                );
                assert_eq!(work, 0);
            }
            let mut changed = facts.clone();
            changed
                .invocation_expressions
                .retain(|row| row.expression != observation);
            let missing = OriginalOperandSources::new(&changed).unwrap();
            assert!(
                missing.observed(source, observation).is_err(),
                "{case}: erased element type cannot replace the missing physical occurrence"
            );
        }
    }

    #[test]
    fn unknown_creation_source_still_requires_its_actual_observation_and_valid_evidence() {
        let source = ril_test::case_source(
            "tests/regressions/source-observations.ril::closure-captured-step",
        );
        let program = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let facts = program.facts();
        let row = facts
            .binding_sources
            .iter()
            .find(|row| facts.bindings[row.binding].name == "callback")
            .unwrap();
        assert!(facts.source_types.binding_type(row.binding).is_none());
        let replay = Replay::new(facts).unwrap();
        let sites = super::super::explicit_named::source_sites_base(facts).unwrap();
        let syntax = sites
            .bindings
            .iter()
            .find(|site| site.binding.pattern.hir_id == Some(row.declaration))
            .map(|site| &site.binding.value)
            .unwrap();
        assert!(
            OriginalOperandSources::new(facts)
                .unwrap()
                .observed(syntax.hir_id.unwrap(), row.initializer.expression)
                .unwrap()
                .0
                .is_none()
        );
        assert!(
            replay
                .original_observed_source_key_if_known(
                    syntax,
                    row.initializer.expression,
                    row.context,
                    &sites,
                )
                .unwrap()
                .is_none()
        );
        assert!(
            replay
                .original_observed_source_key(
                    syntax,
                    row.initializer.expression,
                    row.context,
                    &sites,
                )
                .is_err()
        );
        assert!(
            replay
                .original_source_key_inner_if_known(
                    syntax,
                    &facts.expressions[row.initializer.expression].value,
                    row.context,
                    &sites,
                    &mut 0,
                    SourceVisit {
                        depth: 0,
                        observation: Some(row.initializer.expression),
                    },
                )
                .is_err()
        );
        let mut changed = facts.clone();
        changed.expressions[row.initializer.expression].source_id = None;
        assert!(
            Replay::new(&changed)
                .and_then(|replay| {
                    replay.original_observed_source_key_if_known(
                        syntax,
                        row.initializer.expression,
                        row.context,
                        &sites,
                    )
                })
                .is_err()
        );
        let mut changed = facts.clone();
        let mut witness = facts
            .expressions
            .iter()
            .find_map(|fact| fact.value.source_type_witness.as_deref())
            .unwrap()
            .clone();
        witness.key.push_str("invalid");
        changed.expressions[row.initializer.expression]
            .value
            .corrupt_value(&mut 1_000_000)
            .unwrap()
            .source_type_witness = Some(std::sync::Arc::new(witness));
        assert!(
            Replay::new(&changed)
                .and_then(|replay| {
                    replay.original_observed_source_key_if_known(
                        syntax,
                        row.initializer.expression,
                        row.context,
                        &sites,
                    )
                })
                .is_err()
        );
    }

    #[test]
    fn source_interval_rejects_a_later_real_operand_even_after_structure_is_calibrated() {
        let source = ril_test::case_source(
            "tests/regressions/evaluation-identity.ril::application-repeated-source-interval",
        );
        let program = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let facts = program.facts();
        let replay = Replay::new(facts).unwrap();
        let take = facts
            .functions
            .iter()
            .find(|function| function.syntax.name == "take")
            .unwrap()
            .definition;
        let mut candidates = vec![];
        for invocation in &facts.copy_invocations {
            if invocation.target != take {
                continue;
            }
            let Some(id) = invocation.source_event else {
                continue;
            };
            let event = &facts.copy_call_events[id.0 as usize];
            let prep = facts
                .call_arguments
                .iter()
                .find(|row| row.source_event == id)
                .unwrap();
            let token = prep.supplied[&0];
            let context = replay
                .observations
                .row(token.expression, &mut 4096)
                .unwrap()
                .context;
            candidates.push((event, token, context));
        }
        let (earlier, later) = candidates
            .iter()
            .flat_map(|left| candidates.iter().map(move |right| (left, right)))
            .find(|(left, right)| {
                left.0.id != right.0.id
                    && left.2 == right.2
                    && left
                        .0
                        .result_expression
                        .is_some_and(|end| end < right.1.expression)
            })
            .expect(
                "real fixed-point repetitions must share a context but retain distinct intervals",
            );
        replay
            .input_operand_interval(later.0, 0, later.1.expression, later.2, &mut 4096)
            .unwrap();
        let mut shortened = later.0.clone();
        shortened.result_expression = earlier.0.result_expression;
        let error = replay
            .input_operand_interval(&shortened, 0, later.1.expression, later.2, &mut 4096)
            .unwrap_err();
        assert_eq!(
            error,
            "call input operand belongs to another actual invocation interval"
        );
    }

    fn binder(index: usize) -> ArgumentKey {
        ArgumentKey::Binder {
            identity: format!("budget:{index}"),
            sort: StaticBinderSort::Type,
        }
    }

    #[test]
    fn bounded_input_substitution_stops_before_exponential_expansion() {
        let mut selected = BTreeMap::new();
        for index in 0..24 {
            selected.insert(
                format!("budget:{index}"),
                ArgumentKey::Tuple(vec![binder(index + 1), binder(index + 1)]),
            );
        }
        selected.insert(
            "budget:24".into(),
            ArgumentKey::Name {
                name: "int".into(),
                arguments: vec![],
            },
        );
        let error = input_select_key(&binder(0), &selected, 0).unwrap_err();
        assert!(error.contains("budget"), "{error}");
    }

    #[test]
    fn input_row_composition_preserves_open_uid_and_field_modes() {
        let key = ArgumentKey::Record {
            fields: vec![("head".into(), false, binder(0))],
            row: Some(Box::new(binder(1))),
        };
        let selected = BTreeMap::from([(
            "budget:1".into(),
            ArgumentKey::Record {
                fields: vec![("tail".into(), true, binder(2))],
                row: Some(Box::new(binder(3))),
            },
        )]);
        let result = input_select_key(&key, &selected, 0).unwrap();
        assert_eq!(
            result,
            ArgumentKey::Record {
                fields: vec![
                    ("head".into(), false, binder(0)),
                    ("tail".into(), true, binder(2))
                ],
                row: Some(Box::new(binder(3))),
            }
        );
    }
}
