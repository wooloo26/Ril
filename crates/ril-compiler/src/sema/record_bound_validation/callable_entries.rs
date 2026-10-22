//! Original callable inputs are replayed from physical observations and value
//! derivations. An entry snapshot alone cannot invent an input Source schema.
use super::*;
use crate::sema::{
    application_effect::{CallableEntry, EntryArgument, EntryOrigin, InputOrigin},
    copy_contract::CopyInvocation,
    effect_identity::ClosureInvocation,
};
use ril_compiler_core::ids::ExprId;

trait Arguments {
    fn len(&self) -> usize;
    fn argument(&self, slot: usize) -> Option<(ril_syntax::ast::ParameterMode, &Value)>;
}

impl Arguments for std::sync::Arc<Vec<EntryArgument>> {
    fn len(&self) -> usize {
        self.as_ref().len()
    }

    fn argument(&self, slot: usize) -> Option<(ril_syntax::ast::ParameterMode, &Value)> {
        self.as_ref()
            .get(slot)
            .map(|(mode, value, _)| (*mode, value))
    }
}

impl Arguments for Vec<(crate::sema::model::Mode, CopyValueSnapshot)> {
    fn len(&self) -> usize {
        self.as_slice().len()
    }

    fn argument(&self, slot: usize) -> Option<(ril_syntax::ast::ParameterMode, &Value)> {
        use crate::sema::model::Mode;
        use ril_syntax::ast::ParameterMode;
        self.as_slice().get(slot).map(|(mode, value)| {
            (
                match mode {
                    Mode::Read => ParameterMode::Read,
                    Mode::Write => ParameterMode::Mut,
                    Mode::Retain => ParameterMode::SharedMut,
                },
                &value.value,
            )
        })
    }
}

enum Input {
    Physical {
        source: ExprId,
        observation: usize,
        copy: Option<crate::sema::copy_contract::CopyBoundaryId>,
    },
    Scalar(crate::sema::application_effect::ScalarInput),
}

#[derive(Clone, Copy)]
enum Target {
    Closure(usize),
    Named(DefinitionId),
}

struct EntrySource<'a, 'p, A> {
    entry: &'a CallableEntry<A>,
    caller_activation: Option<crate::sema::facts::ScopeId>,
    target: Target,
    slot: usize,
    sites: &'a super::super::explicit_named::SourceSites<'p>,
    depth: usize,
}

impl Target {
    fn matches(self, callable: &crate::sema::model::Callable, facts: &SemanticFacts) -> bool {
        match (self, callable) {
            (Self::Closure(expected), crate::sema::model::Callable::Closure(actual)) => {
                expected == *actual
            }
            (Self::Named(expected), crate::sema::model::Callable::Named(actual)) => facts
                .functions
                .get(*actual)
                .is_some_and(|function| function.definition == expected),
            _ => false,
        }
    }
}

impl Replay<'_> {
    fn signature_entry_graph<A: Arguments>(
        &self,
        entry: &CallableEntry<A>,
        work: &mut usize,
    ) -> Check {
        let EntryOrigin::SignatureProbe(source) = &entry.origin else {
            return Ok(());
        };
        let scope = super::reception::environment_scope(&source.environment, work)?;
        let (root, _) =
            self.source_type_header_raw(&source.header, &scope, source.environment.clone(), work)?;
        let parameters = super::graph_sources::schema_work(work, |budget| {
            root.project_steps(&source.path, budget)?
                .callable_parameters(budget)
        })?;
        require(
            parameters.len() == entry.arguments.len(),
            "signature entry changed its original graph arity",
        )?;
        for (slot, (mode, _)) in parameters.iter().enumerate() {
            require(
                entry
                    .arguments
                    .argument(slot)
                    .is_some_and(|(actual, _)| actual == *mode),
                "signature entry changed its original graph parameter mode",
            )?;
        }
        Ok(())
    }

    pub(in crate::sema::record_bound_validation) fn inferred_lambda_receipt(
        &self,
        call: &ClosureInvocation,
        slot: usize,
        value: &Value,
        observation: usize,
        work: &mut usize,
    ) -> Check {
        use crate::sema::facts::{Participant, Permission};
        use ril_syntax::ast::ParameterMode;
        let &binding_id = value
            .sources
            .first()
            .ok_or("inferred formal has no original binding")?;
        let binding = self
            .facts
            .bindings
            .get(binding_id)
            .ok_or("inferred formal binding is absent")?;
        let (mode, original, _) = call
            .entry
            .arguments
            .get(slot)
            .ok_or("inferred formal has no actual input")?;
        let epoch = self.facts.expressions[observation].allocation_epoch;
        let origins = transported_origins(
            self.facts,
            &original.origins,
            call.entry.allocation_epoch,
            epoch,
            work,
        )?;
        require(
            value.sources == BTreeSet::from([binding_id])
                && binding.forwarded == original.sources
                && value.origins == origins
                && value.callables == original.callables
                && value.publication
                    == if *mode == ParameterMode::Read {
                        original.publication
                    } else {
                        Publication::Live
                    },
            "inferred formal changed its actual input or receiving scope",
        )?;
        if *mode == ParameterMode::Read {
            *work = work
                .checked_sub(original.participants.len() + 1)
                .ok_or("inferred read reception exceeds its work bound")?;
            let mut participants = original.participants.clone();
            if participants.is_empty() {
                participants.insert(Participant::Root(binding.root));
            }
            require(
                value.permission == Permission::Read
                    && !value.construction
                    && !value.marker
                    && value.participants == participants,
                "inferred formal recovered authority while receiving a read input",
            )?;
        } else {
            *work = work
                .checked_sub(self.facts.invocation_loan_starts.len())
                .ok_or("inferred loan reception exceeds its work bound")?;
            let mut loans = self.facts.invocation_loan_starts.iter().filter(|loan| {
                loan.closure == Some(call.id)
                    && loan.parameter as usize == slot
                    && loan.activation == binding.owner
                    && loan.bindings.contains(&binding_id)
            });
            let loan = loans
                .next()
                .ok_or("inferred formal has no original invocation loan")?;
            require(
                loans.next().is_none()
                    && loan.retained == (*mode == ParameterMode::SharedMut)
                    && value.permission == Permission::Write
                    && value.participants == BTreeSet::from([Participant::Loan(loan.loan)]),
                "inferred formal changed its actual loan or parameter mode",
            )?;
            self.input_value_transport(
                original,
                &loan.source,
                call.entry.allocation_epoch,
                loan.allocation_epoch,
            )?;
        }
        Ok(())
    }

    fn entry_input<A: Arguments>(
        &self,
        entry: &CallableEntry<A>,
        caller_activation: Option<crate::sema::facts::ScopeId>,
        target: Target,
        slot: usize,
        work: &mut usize,
    ) -> Check<Input> {
        *work = work
            .checked_sub(1)
            .ok_or("callable input replay exceeds its work bound")?;
        let (_, argument) = entry
            .arguments
            .argument(slot)
            .ok_or("callable entry lost its input slot")?;
        let input = match &entry.origin {
            EntryOrigin::Application(id) => {
                *work = work
                    .checked_sub(self.facts.call_arguments.len())
                    .ok_or("callable preparation lookup exceeds its work bound")?;
                let mut rows = self
                    .facts
                    .call_arguments
                    .iter()
                    .filter(|row| row.source_event == *id);
                let row = rows
                    .next()
                    .ok_or("callable input has no physical preparation")?;
                require(
                    rows.next().is_none() && row.evaluation_complete,
                    "callable input preparation is incomplete or duplicated",
                )?;
                let token = match row.slots.get(slot) {
                    Some(ArgumentSource::Supplied) => row
                        .supplied
                        .get(&(slot as u32))
                        .map(|token| token.expression),
                    Some(ArgumentSource::Default(id)) => self
                        .facts
                        .default_uses
                        .get(id.0 as usize)
                        .filter(|receipt| {
                            receipt.id == *id
                                && receipt.origin == DefaultOrigin::Call(row.source_event)
                                && receipt.parameter as usize == slot
                        })
                        .and_then(|receipt| receipt.result_expression),
                    _ => None,
                }
                .ok_or("callable input lost its exact supplied/default observation")?;
                let fact = self
                    .facts
                    .expressions
                    .get(token)
                    .ok_or("callable input is outside its value arena")?;
                let evaluation = self
                    .facts
                    .evaluations
                    .get(token)
                    .ok_or("callable input has no actual evaluation")?;
                let parent = entry
                    .parent
                    .and_then(|id| self.facts.activations.get(id.0 as usize))
                    .ok_or("callable input has no owning activation")?;
                require(
                    evaluation.context
                        == if let Some(ArgumentSource::Default(id)) = row.slots.get(slot) {
                            let receipt = &self.facts.default_uses[id.0 as usize];
                            InvocationContext {
                                owner: receipt.owner,
                                default_use: Some(*id),
                                ..receipt.caller
                            }
                        } else {
                            entry.caller_context
                        }
                        && token >= parent.start_expression
                        && Some(token) < parent.result.map(|id| id.0 as usize),
                    "callable input borrowed another activation's observation",
                )?;
                self.input_value_transport(
                    &fact.value,
                    argument,
                    fact.allocation_epoch,
                    entry.allocation_epoch,
                )?;
                require(
                    fact.value.callables == argument.callables
                        && fact.value.permission == argument.permission
                        && fact.value.publication == argument.publication
                        && fact.value.participants == argument.participants,
                    "callable input changed its original authority or callable targets",
                )?;
                Input::Physical {
                    source: fact.source_id.ok_or("callable input lost its HIR source")?,
                    observation: token,
                    copy: None,
                }
            }
            EntryOrigin::Generated {
                anchor,
                callee,
                inputs,
            } => {
                let parent = self
                    .facts
                    .activations
                    .get(anchor.0 as usize)
                    .ok_or("generated call has no actual anchor")?;
                let hir = self
                    .facts
                    .semantic_hir
                    .as_deref()
                    .ok_or("generated call has no original HIR")?;
                let root = parent
                    .source
                    .and_then(|id| hir.expression(id))
                    .ok_or("generated call has no original operation")?;
                if !matches!(root.kind, crate::hir::nodes::ExprKind::Binary { .. })
                    || !matches!(&root.kind, crate::hir::nodes::ExprKind::Binary { right, .. }
                        if matches!(hir.expression(*right).map(|expression| &expression.kind), Some(crate::hir::nodes::ExprKind::Derive { base: None, .. })))
                {
                    return self.generated_record_input(
                        entry,
                        caller_activation,
                        target,
                        slot,
                        work,
                    );
                }
                let crate::hir::nodes::ExprKind::Binary {
                    operator,
                    left,
                    right,
                } = &root.kind
                else {
                    return Err(
                        "generated invocation needs its original operation input contract".into(),
                    );
                };
                let Some(crate::hir::nodes::Expr {
                    kind: crate::hir::nodes::ExprKind::Derive { base: None, recipe },
                    ..
                }) = hir.expression(*right)
                else {
                    return Err("generated invocation lost its original recipe".into());
                };
                require(
                    matches!(operator.as_str(), "|>" | "!>")
                        && slot == 0
                        && inputs.len() == 1
                        && entry.arguments.len() == 1
                        && entry.arguments.argument(0).map(|(mode, _)| mode)
                            == Some(ril_syntax::ast::ParameterMode::Mut),
                    "generated invocation changed its declared input contract",
                )?;
                let callee_fact = self
                    .facts
                    .expressions
                    .get(callee.0 as usize)
                    .ok_or("generated callee is outside its arena")?;
                let callee_evaluation = self
                    .facts
                    .evaluations
                    .get(callee.0 as usize)
                    .ok_or("generated callee has no evaluation")?;
                let callee_activation = callee_evaluation
                    .identity
                    .and_then(|identity| self.facts.activations.get(identity.activation.0 as usize))
                    .ok_or("generated callee lost its activation")?;
                require(
                    callee_fact.source_id == Some(*recipe)
                        && callee_evaluation.context == entry.caller_context
                        && callee_activation.parent == Some(*anchor)
                        && callee_fact
                            .value
                            .callables
                            .iter()
                            .any(|actual| target.matches(actual, self.facts)),
                    "generated invocation borrowed another physical recipe or callable",
                )?;
                let InputOrigin::Copied {
                    observation,
                    boundary,
                } = inputs[0]
                else {
                    return Err("generated draft has no actual copying derivation".into());
                };
                let token = observation.0 as usize;
                let fact = self
                    .facts
                    .expressions
                    .get(token)
                    .ok_or("generated input is outside its arena")?;
                let evaluation = self
                    .facts
                    .evaluations
                    .get(token)
                    .ok_or("generated input has no evaluation")?;
                let activation = evaluation
                    .identity
                    .and_then(|identity| self.facts.activations.get(identity.activation.0 as usize))
                    .ok_or("generated input lost its actual activation")?;
                require(
                    fact.source_id == Some(*left)
                        && evaluation.context == entry.caller_context
                        && activation.parent == Some(*anchor)
                        && observation.0 < callee.0,
                    "generated input borrowed another physical operation operand",
                )?;
                let proof = self
                    .facts
                    .copy_boundaries
                    .get(boundary.0 as usize)
                    .filter(|proof| proof.id == boundary)
                    .ok_or("generated input copy boundary is absent")?;
                require(
                    Some(proof.activation) == caller_activation
                        && proof.mode == crate::sema::copy_contract::CopyMode::Mutable
                        && proof.source.ty == fact.value.ty
                        && proof.source.callables == fact.value.callables,
                    "generated input copy changed its source or activation",
                )?;
                self.input_view_transport(
                    &fact.value,
                    &proof.source,
                    fact.allocation_epoch,
                    proof.input_allocation_epoch,
                )?;
                if proof.source.cause != fact.value.cause {
                    require(
                        fact.value.construction
                            && proof.source.publication == Publication::Immutable
                            && proof.source.permission == crate::sema::facts::Permission::Read
                            && self
                                .facts
                                .explanations
                                .causes
                                .get(proof.source.cause.0 as usize)
                                .is_some_and(|cause| cause.parents == [fact.value.cause]),
                        "generated input lost its original construction reception",
                    )?;
                }
                let output = proof
                    .output
                    .as_ref()
                    .ok_or("generated input has no established copy output")?;
                let epoch = proof
                    .output_allocation_epoch
                    .ok_or("generated input copy output has no birth epoch")?;
                require(
                    proof.input_allocation_epoch <= epoch
                        && output.callables == argument.callables
                        && output.permission == argument.permission
                        && output.publication == argument.publication,
                    "generated input changed its copying epoch or output authority",
                )?;
                self.input_value_transport(output, argument, epoch, entry.allocation_epoch)?;
                Input::Physical {
                    source: *left,
                    observation: token,
                    copy: Some(boundary),
                }
            }
            _ => {
                return Err(
                    "inferred callable input needs its actual receiving Source origin".into(),
                );
            }
        };
        Ok(input)
    }

    fn generated_record_input<A: Arguments>(
        &self,
        entry: &CallableEntry<A>,
        caller_activation: Option<crate::sema::facts::ScopeId>,
        target: Target,
        slot: usize,
        work: &mut usize,
    ) -> Check<Input> {
        use crate::sema::application_effect::ScalarInput;
        use ril_syntax::ast::ParameterMode;
        let EntryOrigin::Generated {
            anchor,
            callee,
            inputs,
        } = &entry.origin
        else {
            unreachable!()
        };
        let parent = self
            .facts
            .activations
            .get(anchor.0 as usize)
            .ok_or("record callback anchor is absent")?;
        *work = work
            .checked_sub(self.facts.copy_call_events.len() + self.facts.call_arguments.len())
            .ok_or("record callback operation lookup exceeds its work bound")?;
        let mut events = self.facts.copy_call_events.iter().filter(|event| {
            event.source_id == parent.source
                && event.result_expression == parent.result.map(|id| id.0 as usize)
        });
        let event = events
            .next()
            .ok_or("record callback lost its actual operation")?;
        require(
            events.next().is_none(),
            "record callback operation is ambiguous",
        )?;
        let operation = event
            .callee_expression
            .and_then(|id| self.facts.expressions.get(id))
            .ok_or("record callback has no actual operation callee")?;
        let [crate::sema::model::Callable::Builtin(name)] = operation.value.callables.as_slice()
        else {
            return Err("record callback is not an original primitive operation".into());
        };
        let contract = crate::sema::application_effect::record_callback(name)
            .ok_or("generated call requires its declared primitive input contract")?;
        let read = contract.field == "read";
        let mut rows = self
            .facts
            .call_arguments
            .iter()
            .filter(|row| row.source_event == event.id);
        let row = rows
            .next()
            .ok_or("record callback lost its argument preparation")?;
        require(
            rows.next().is_none()
                && row.evaluation_complete
                && event.owner == entry.caller_context.owner
                && event.parent == entry.caller_context.invocation
                && inputs.len() == 2
                && entry.arguments.len() == 2
                && slot < 2
                && entry.arguments.argument(0).map(|(mode, _)| mode) == Some(ParameterMode::Mut)
                && entry.arguments.argument(1).map(|(mode, _)| mode) == Some(ParameterMode::Read),
            "record callback changed its original modes, context or preparation",
        )?;
        let receiver = row
            .supplied
            .get(&contract.receiver)
            .ok_or("record callback receiver is absent")?
            .expression;
        let ops = row
            .supplied
            .get(&contract.operations)
            .ok_or("record callback operations are absent")?
            .expression;
        require(
            inputs[0]
                == InputOrigin::Widened(ril_compiler_core::ids::EvaluationOccurrenceId(
                    receiver as u32,
                )),
            "record callback borrowed another receiver observation",
        )?;
        let ops_fact = self
            .facts
            .expressions
            .get(ops)
            .ok_or("record callback operations are outside the arena")?;
        let ops_activation = self
            .facts
            .evaluations
            .get(ops)
            .and_then(|record| record.identity)
            .ok_or("record callback operations lost their activation")?
            .activation;
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("record callback has no original HIR")?;
        let field = crate::sema::application_effect::record_field_source(
            hir,
            ops_fact
                .source_id
                .ok_or("record callback operations lost their source")?,
            contract.field,
            work,
        )
        .ok_or("record callback lost its physical field operand")?;
        let callee_fact = self
            .facts
            .expressions
            .get(callee.0 as usize)
            .ok_or("record callback callee is absent")?;
        let callee_evaluation = self
            .facts
            .evaluations
            .get(callee.0 as usize)
            .ok_or("record callback callee evaluation is absent")?;
        let callee_activation = callee_evaluation
            .identity
            .and_then(|id| self.facts.activations.get(id.activation.0 as usize))
            .ok_or("record callback callee activation is absent")?;
        *work = work
            .checked_sub(callee_fact.value.callables.len())
            .ok_or("record callback targets exceed their work bound")?;
        require(
            callee_fact.source_id == Some(field)
                && callee_evaluation.context == entry.caller_context
                && callee_activation.parent == Some(ops_activation)
                && callee_fact
                    .value
                    .callables
                    .iter()
                    .any(|callable| target.matches(callable, self.facts)),
            "record callback borrowed another field or callable target",
        )?;
        let (_, argument) = entry
            .arguments
            .argument(slot)
            .ok_or("record callback input is absent")?;
        if slot == 0 {
            let original = self
                .facts
                .expressions
                .get(receiver)
                .ok_or("record callback receiver is outside its arena")?;
            let mut origins = transported_origins(
                self.facts,
                &original.value.origins,
                original.allocation_epoch,
                entry.allocation_epoch,
                work,
            )?;
            origins.choices.clear();
            require(
                origins == argument.origins
                    && original.value.ty == argument.ty
                    && original.value.cause == argument.cause
                    && original.value.sources == argument.sources
                    && original.value.source_type_witness == argument.source_type_witness
                    && original.value.results == argument.results
                    && original.value.outer_results == argument.outer_results
                    && original.value.permission == argument.permission
                    && original.value.publication == argument.publication
                    && original.value.participants == argument.participants
                    && original.value.callables == argument.callables
                    && argument.temporary
                    && argument.constant.is_none(),
                "record callback receiver changed during widening or borrowing",
            )?;
            require(
                Some(parent.scope) == caller_activation,
                "record callback borrowed another caller scope",
            )?;
            Ok(Input::Physical {
                source: original
                    .source_id
                    .ok_or("record callback receiver lost its source")?,
                observation: receiver,
                copy: None,
            })
        } else {
            let kind = match contract.scalar_source {
                crate::sema::application_effect::ScalarSource::PositiveInt => {
                    ScalarInput::PositiveInt
                }
                crate::sema::application_effect::ScalarSource::ByteSuffix(slot) => {
                    ScalarInput::ByteSuffix(ril_compiler_core::ids::EvaluationOccurrenceId(
                        row.supplied
                            .get(&slot)
                            .ok_or("record callback byte source is absent")?
                            .expression as u32,
                    ))
                }
                crate::sema::application_effect::ScalarSource::BufferedBytes(slot) => {
                    ScalarInput::BufferedBytes(ril_compiler_core::ids::EvaluationOccurrenceId(
                        row.supplied
                            .get(&slot)
                            .ok_or("record callback buffer source is absent")?
                            .expression as u32,
                    ))
                }
            };
            if let ScalarInput::ByteSuffix(source) = kind {
                let input = self
                    .facts
                    .expressions
                    .get(source.0 as usize)
                    .ok_or("byte suffix source is absent")?;
                require(
                    input.value.ty == Ty::Bytes && input.value.cause == argument.cause,
                    "byte suffix borrowed another input cause or type",
                )?;
            }
            require(
                inputs[1] == InputOrigin::Scalar(kind)
                    && argument.ty
                        == if read {
                            Ty::Int("int".into())
                        } else {
                            Ty::Bytes
                        }
                    && argument.origins.nodes.is_empty()
                    && argument.sources.is_empty()
                    && argument.callables.is_empty()
                    && argument.participants.is_empty()
                    && argument.results.is_empty()
                    && argument.outer_results.is_empty()
                    && argument.scoped.is_empty()
                    && argument.constant.is_none()
                    && !argument.construction
                    && !argument.marker,
                "record callback changed its declared generated scalar",
            )?;
            Ok(Input::Scalar(kind))
        }
    }

    pub(in crate::sema::record_bound_validation) fn closure_entry_source_schema_if_known(
        &self,
        call: &ClosureInvocation,
        slot: usize,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        depth: usize,
    ) -> Check<Option<OriginalSource>> {
        if matches!(call.entry.origin, EntryOrigin::SignatureProbe(_)) {
            let hir = self
                .facts
                .semantic_hir
                .as_deref()
                .ok_or("signature closure input has no original HIR")?;
            let auth = super::graph_sources::schema_work(work, |budget| {
                crate::sema::application_effect::closure_signature_assumption(
                    call,
                    slot,
                    hir,
                    &self.facts.bindings,
                    self.facts.allocation_history.len(),
                    budget,
                )
            })?;
            let scope = super::reception::environment_scope(auth.environment, work)?;
            let (root, environment) =
                self.source_type_header_raw(auth.header, &scope, auth.environment.clone(), work)?;
            let parameter = super::graph_sources::schema_work(work, |budget| {
                auth.parameter_schema(&root, budget)
            })?;
            let selected = self.source_selected_schemas(&environment, work)?;
            return self
                .source_substitute_schema(parameter, environment, &selected, work)
                .map(Some);
        }
        self.entry_source_schema_if_known(
            EntrySource {
                entry: &call.entry,
                caller_activation: Some(call.caller_activation),
                target: Target::Closure(call.closure),
                slot,
                sites,
                depth,
            },
            work,
        )
    }

    pub(super) fn named_entry_source_schema(
        &self,
        call: &CopyInvocation,
        slot: usize,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
    ) -> Check<OriginalSource> {
        self.function(call.target)?;
        self.entry_source_schema(
            &call.entry,
            call.caller_activation,
            Target::Named(call.target),
            slot,
            sites,
            work,
            0,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn entry_source_schema<A: Arguments>(
        &self,
        entry: &CallableEntry<A>,
        caller_activation: Option<crate::sema::facts::ScopeId>,
        target: Target,
        slot: usize,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        depth: usize,
    ) -> Check<OriginalSource> {
        self.entry_source_schema_if_known(
            EntrySource {
                entry,
                caller_activation,
                target,
                slot,
                sites,
                depth,
            },
            work,
        )?
        .ok_or_else(|| "callable input has no complete original graph".into())
    }

    fn entry_source_schema_if_known<A: Arguments>(
        &self,
        source: EntrySource<'_, '_, A>,
        work: &mut usize,
    ) -> Check<Option<OriginalSource>> {
        let EntrySource {
            entry,
            caller_activation,
            target,
            slot,
            sites,
            depth,
        } = source;
        require(
            depth < 64,
            "callable input Source ancestry exceeds its bound",
        )?;
        let input = self.entry_input(entry, caller_activation, target, slot, work)?;
        let Input::Physical {
            source,
            observation,
            copy,
        } = input
        else {
            let Input::Scalar(kind) = input else {
                unreachable!()
            };
            return self
                .source_header_schema(
                    &ArgumentKey::Name {
                        name: match kind {
                            crate::sema::application_effect::ScalarInput::PositiveInt => "int",
                            crate::sema::application_effect::ScalarInput::ByteSuffix(_)
                            | crate::sema::application_effect::ScalarInput::BufferedBytes(_) => {
                                "bytes"
                            }
                        }
                        .into(),
                        arguments: vec![],
                    },
                    FrozenEnvironment::default(),
                    work,
                )
                .map(Some);
        };
        let syntax = sites
            .expressions
            .get(&source)
            .ok_or("callable input lost its original indexed expression")?;
        let fact = &self.facts.expressions[observation];
        let context = self.observations.row(observation, work)?.context;
        let Some((schema, environment)) = self.original_source_schema_inner(
            syntax,
            &fact.value,
            context,
            sites,
            work,
            SourceVisit {
                depth: depth + 1,
                observation: Some(observation),
            },
        )?
        else {
            return Ok(None);
        };
        if let Some(id) = copy {
            super::graph_sources::schema_work(work, |budget| {
                schema.copy_view(self.facts.copy_boundaries[id.0 as usize].mode, budget)
            })
            .map(|schema| Some((schema, environment)))
        } else {
            Ok(Some((schema, environment)))
        }
    }

    pub(in crate::sema::record_bound_validation) fn callable_inputs(&self) -> Check {
        let mut work = 16_000_000usize;
        let sites = super::super::explicit_named::source_sites_base(self.facts)?;
        work = work
            .checked_sub(self.facts.bindings.len())
            .ok_or("inferred formal coverage work exhausted")?;
        for (binding, info) in self.facts.bindings.iter().enumerate() {
            if info.parameter {
                self.inferred_closure_parameter_schema(binding, &sites, &mut work)?;
            }
        }
        for call in &self.facts.closure_invocations {
            self.signature_entry_graph(&call.entry, &mut work)?;
            if !matches!(
                call.entry.origin,
                EntryOrigin::Application(_) | EntryOrigin::Generated { .. }
            ) {
                continue;
            }
            for slot in 0..call.entry.arguments.len() {
                self.entry_input(
                    &call.entry,
                    Some(call.caller_activation),
                    Target::Closure(call.closure),
                    slot,
                    &mut work,
                )?;
            }
        }
        for call in &self.facts.copy_invocations {
            self.signature_entry_graph(&call.entry, &mut work)?;
            if !matches!(
                call.entry.origin,
                EntryOrigin::Application(_) | EntryOrigin::Generated { .. }
            ) {
                continue;
            }
            self.function(call.target)?;
            for slot in 0..call.entry.arguments.len() {
                self.entry_input(
                    &call.entry,
                    call.caller_activation,
                    Target::Named(call.target),
                    slot,
                    &mut work,
                )?;
            }
        }
        Ok(())
    }
}

fn transported_origins(
    facts: &SemanticFacts,
    original: &crate::sema::model::Origins,
    from: usize,
    to: usize,
    work: &mut usize,
) -> Check<crate::sema::model::Origins> {
    require(
        from <= to && to <= facts.allocation_history.len(),
        "formal input transport changed its birth epoch",
    )?;
    *work = work
        .checked_sub(original.nodes.len() + original.choices.len())
        .ok_or("formal input origin clone exceeds its work bound")?;
    let mut sets = 1usize;
    for branches in original.choices.values() {
        *work = work
            .checked_sub(branches.len())
            .ok_or("formal input choice clone exceeds its work bound")?;
        sets = sets
            .checked_add(branches.len())
            .ok_or("formal input choice count overflow")?;
        for branch in branches {
            *work = work
                .checked_sub(branch.len())
                .ok_or("formal input branch clone exceeds its work bound")?;
        }
    }
    *work = work
        .checked_sub(
            (to - from)
                .checked_mul(sets)
                .ok_or("formal input transport work overflow")?,
        )
        .ok_or("formal input epoch transport exceeds its work bound")?;
    let mut origins = original.clone();
    for &(recent, older) in &facts.allocation_history[from..to] {
        origins.remap(recent, older);
    }
    Ok(origins)
}
