//! Borrowed authentication of generated entries, before any input Source query.
//! The index is rebuilt from original records and never retained as evidence.
use super::{ActivationKind, CallableEntry, EntryArgument, EntryOrigin, InputOrigin, ScalarInput};
use crate::sema::{
    ExpressionFact, SemanticFacts,
    copy_contract::{CopyBoundary, CopyCallEvent, CopyCallEventId, CopyValueSnapshot},
    copy_templates::InstanceId,
    default_uses::CallArguments,
    effect_identity::{ClosureInvocationId, InvocationContext},
    facts::ScopeId,
    model::{Callable, Mode, Value},
};
use ril_compiler_core::ids::{ActivationEpochId, DefinitionId, EvaluationOccurrenceId, ExprId};
use ril_syntax::ast::ParameterMode;
use std::{collections::BTreeMap, sync::Arc};

type Check<T> = Result<T, String>;

fn charge(work: &mut usize, amount: usize) -> Check<()> {
    *work = work
        .checked_sub(amount)
        .ok_or("generated entry authentication exceeds its work bound")?;
    Ok(())
}

fn require(condition: bool, message: &str) -> Check<()> {
    condition.then_some(()).ok_or_else(|| message.to_owned())
}

pub(crate) trait EntryArguments {
    fn len(&self) -> usize;
    fn argument(&self, slot: usize) -> Option<(ParameterMode, &Value)>;
}

impl EntryArguments for Arc<Vec<EntryArgument>> {
    fn len(&self) -> usize {
        self.as_ref().len()
    }

    fn argument(&self, slot: usize) -> Option<(ParameterMode, &Value)> {
        self.as_ref()
            .get(slot)
            .map(|(mode, value, _)| (*mode, value))
    }
}

impl EntryArguments for Vec<(Mode, CopyValueSnapshot)> {
    fn len(&self) -> usize {
        self.as_slice().len()
    }

    fn argument(&self, slot: usize) -> Option<(ParameterMode, &Value)> {
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

impl EntryArguments for () {
    fn len(&self) -> usize {
        0
    }

    fn argument(&self, _: usize) -> Option<(ParameterMode, &Value)> {
        None
    }
}

pub(crate) struct EntryView<'a> {
    pub origin: &'a EntryOrigin,
    pub parent: Option<ActivationEpochId>,
    pub caller_activation: Option<ScopeId>,
    pub caller_context: InvocationContext,
    pub allocation_epoch: usize,
    pub arguments: &'a dyn EntryArguments,
}

impl<'a> EntryView<'a> {
    pub(crate) fn callable<A: EntryArguments>(
        entry: &'a CallableEntry<A>,
        caller_activation: Option<ScopeId>,
    ) -> Self {
        Self {
            origin: &entry.origin,
            parent: entry.parent,
            caller_activation,
            caller_context: entry.caller_context,
            allocation_epoch: entry.allocation_epoch,
            arguments: &entry.arguments,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GeneratedTarget {
    Closure(usize),
    Named(DefinitionId),
    Operation(u64),
}

impl GeneratedTarget {
    fn matches(self, callable: &Callable, facts: &SemanticFacts) -> bool {
        match (self, callable) {
            (Self::Closure(expected), Callable::Closure(actual)) => expected == *actual,
            (Self::Named(expected), Callable::Named(actual)) => facts
                .functions
                .get(*actual)
                .is_some_and(|function| function.definition == expected),
            _ => false,
        }
    }
}

/// Coordinates only. Input value transport and Source reconstruction remain
/// independent consumers of the authenticated original operation.
#[derive(Clone, Copy)]
pub(crate) enum GeneratedInput<'a> {
    Copied {
        source: ExprId,
        observation: usize,
        boundary: &'a CopyBoundary,
    },
    Widened {
        source: ExprId,
        observation: usize,
        original: &'a ExpressionFact,
    },
    Scalar(ScalarInput),
}

pub(crate) struct AuthenticatedGeneratedEntry<'a> {
    inputs: Vec<GeneratedInput<'a>>,
}

impl<'a> AuthenticatedGeneratedEntry<'a> {
    pub(crate) fn input(&self, slot: usize) -> Check<GeneratedInput<'a>> {
        self.inputs
            .get(slot)
            .copied()
            .ok_or_else(|| "generated entry lost its authenticated input slot".into())
    }
}

/// Read-only indexes over the actual event/preparation arenas. In particular,
/// an original HIR node alone cannot select one of its dynamic applications.
pub(crate) struct GeneratedEntryRecords<'a> {
    facts: &'a SemanticFacts,
    events: BTreeMap<(ExprId, usize), Vec<&'a CopyCallEvent>>,
    preparations: BTreeMap<CopyCallEventId, Vec<&'a CallArguments>>,
}

impl<'a> GeneratedEntryRecords<'a> {
    pub(crate) fn new(facts: &'a SemanticFacts, work: &mut usize) -> Check<Self> {
        charge(work, facts.copy_call_events.len())?;
        charge(work, facts.call_arguments.len())?;
        let mut events = BTreeMap::<_, Vec<_>>::new();
        for (ordinal, event) in facts.copy_call_events.iter().enumerate() {
            require(
                event.id.0 as usize == ordinal,
                "generated operation events have misplaced identities",
            )?;
            if let (Some(source), Some(result)) = (event.source_id, event.result_expression) {
                events.entry((source, result)).or_default().push(event);
            }
        }
        let mut preparations = BTreeMap::<_, Vec<_>>::new();
        for row in &facts.call_arguments {
            preparations.entry(row.source_event).or_default().push(row);
        }
        Ok(Self {
            facts,
            events,
            preparations,
        })
    }

    fn event(
        &self,
        parent: &super::EvaluationActivation,
        context: InvocationContext,
        work: &mut usize,
    ) -> Check<&'a CopyCallEvent> {
        charge(work, 1)?;
        let source = parent
            .source
            .ok_or("generated operation has no original HIR")?;
        let result = parent
            .result
            .ok_or("generated operation has no actual root result")?;
        let events = self
            .events
            .get(&(source, result.0 as usize))
            .ok_or("generated operation lost its physical application")?;
        let [event] = events.as_slice() else {
            return Err("generated operation application is ambiguous".into());
        };
        require(
            event.owner == context.owner && event.parent == context.invocation,
            "generated operation changed its original application context",
        )?;
        Ok(event)
    }

    fn observation(
        &self,
        id: EvaluationOccurrenceId,
        context: InvocationContext,
        entry_epoch: usize,
        work: &mut usize,
    ) -> Check<(
        &'a ExpressionFact,
        &'a super::EvaluationRecord,
        &'a super::EvaluationActivation,
    )> {
        charge(work, 3)?;
        let fact = self
            .facts
            .expressions
            .get(id.0 as usize)
            .ok_or("generated observation is outside its value arena")?;
        let record = self
            .facts
            .evaluations
            .get(id.0 as usize)
            .ok_or("generated observation lost its evaluation")?;
        let identity = record
            .identity
            .ok_or("generated observation has no original identity")?;
        let activation = self
            .facts
            .activations
            .get(identity.activation.0 as usize)
            .ok_or("generated observation lost its actual activation")?;
        charge(work, 1)?;
        let source = self
            .facts
            .semantic_hir
            .as_deref()
            .and_then(|hir| hir.expression(identity.source))
            .ok_or("generated observation lost its original HIR")?;
        let kind = if matches!(
            source.kind,
            crate::hir::nodes::ExprKind::Control {
                operation: ril_syntax::ast::ControlOperation::Resume,
                ..
            }
        ) {
            ActivationKind::ControlTransfer
        } else {
            ActivationKind::Expression
        };
        require(
            record.id == id
                && fact.source_id == Some(identity.source)
                && activation.id == identity.activation
                && activation.source == Some(identity.source)
                && activation.result == Some(id)
                && activation.kind == kind
                && record.scope == activation.scope
                && record.context == context
                && activation.context == context
                && record.allocation_epoch == fact.allocation_epoch
                && record.allocation_epoch <= entry_epoch,
            "generated observation borrowed another identity, context or epoch",
        )?;
        Ok((fact, record, activation))
    }

    pub(crate) fn authenticate(
        &self,
        entry: EntryView<'a>,
        target: GeneratedTarget,
        work: &mut usize,
    ) -> Check<Option<AuthenticatedGeneratedEntry<'a>>> {
        charge(work, 1)?;
        let EntryOrigin::Generated {
            anchor,
            callee,
            inputs,
        } = entry.origin
        else {
            return Ok(None);
        };
        charge(work, inputs.len())?;
        charge(work, entry.arguments.len())?;
        let parent = self
            .facts
            .activations
            .get(anchor.0 as usize)
            .ok_or("generated entry has no actual anchor")?;
        require(
            parent.id == *anchor
                && entry.parent == Some(*anchor)
                && parent.kind == ActivationKind::Expression
                && Some(parent.scope) == entry.caller_activation
                && parent.context == entry.caller_context
                && entry.allocation_epoch <= self.facts.allocation_history.len(),
            "generated entry borrowed another parent, scope, context or epoch",
        )?;
        let (callee_fact, _, callee_activation) =
            self.observation(*callee, entry.caller_context, entry.allocation_epoch, work)?;
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("generated entry has no original HIR")?;
        let root = parent
            .source
            .and_then(|id| hir.expression(id))
            .ok_or("generated entry lost its original operation")?;

        if let GeneratedTarget::Operation(operation) = target {
            let event = self.event(parent, entry.caller_context, work)?;
            require(
                operation == u64::MAX - 1
                    && inputs.is_empty()
                    && entry.arguments.len() == 0
                    && event.callee_expression == Some(callee.0 as usize)
                    && callee_activation.parent == Some(*anchor)
                    && matches!(callee_fact.value.callables.as_slice(), [Callable::Builtin(name)] if name == "Div::budget"),
                "generated operation lost its actual budget application",
            )?;
            return Ok(Some(AuthenticatedGeneratedEntry { inputs: Vec::new() }));
        }

        charge(work, callee_fact.value.callables.len())?;
        require(
            callee_fact
                .value
                .callables
                .iter()
                .any(|actual| target.matches(actual, self.facts)),
            "generated entry borrowed another actual callable target",
        )?;

        if let crate::hir::nodes::ExprKind::Binary {
            operator,
            left,
            right,
        } = &root.kind
            && let Some(crate::hir::nodes::Expr {
                kind: crate::hir::nodes::ExprKind::Derive { base: None, recipe },
                ..
            }) = hir.expression(*right)
        {
            require(
                matches!(operator.as_str(), "|>" | "!>")
                    && inputs.len() == 1
                    && entry.arguments.len() == 1
                    && entry
                        .arguments
                        .argument(0)
                        .is_some_and(|(mode, _)| mode == ParameterMode::Mut)
                    && callee_fact.source_id == Some(*recipe)
                    && callee_activation.parent == Some(*anchor),
                "generated derive changed its original recipe, arity or modes",
            )?;
            let InputOrigin::Copied {
                observation,
                boundary,
            } = inputs[0]
            else {
                return Err("generated draft has no actual copying derivation".into());
            };
            let (fact, _, activation) = self.observation(
                observation,
                entry.caller_context,
                entry.allocation_epoch,
                work,
            )?;
            require(
                fact.source_id == Some(*left)
                    && activation.parent == Some(*anchor)
                    && observation.0 < callee.0,
                "generated input borrowed another physical operation operand",
            )?;
            charge(work, 1)?;
            let proof = self
                .facts
                .copy_boundaries
                .get(boundary.0 as usize)
                .filter(|proof| proof.id == boundary)
                .ok_or("generated input copy boundary is absent")?;
            require(
                Some(proof.activation) == entry.caller_activation
                    && proof.mode == crate::sema::copy_contract::CopyMode::Mutable,
                "generated input copy changed its original activation or mode",
            )?;
            return Ok(Some(AuthenticatedGeneratedEntry {
                inputs: vec![GeneratedInput::Copied {
                    source: *left,
                    observation: observation.0 as usize,
                    boundary: proof,
                }],
            }));
        }

        let event = self.event(parent, entry.caller_context, work)?;
        charge(work, 1)?;
        let operation = event
            .callee_expression
            .ok_or("record callback lost its actual primitive callee")?;
        let (operation, _, operation_activation) = self.observation(
            EvaluationOccurrenceId(operation as u32),
            entry.caller_context,
            entry.allocation_epoch,
            work,
        )?;
        let [Callable::Builtin(name)] = operation.value.callables.as_slice() else {
            return Err("record callback is not an original primitive operation".into());
        };
        require(
            operation_activation.parent == Some(*anchor),
            "record callback borrowed another primitive activation",
        )?;
        let contract = super::record_callback(name)
            .ok_or("generated entry needs its original operation input contract")?;
        let rows = self
            .preparations
            .get(&event.id)
            .ok_or("record callback lost its argument preparation")?;
        let [row] = rows.as_slice() else {
            return Err("record callback preparation is ambiguous".into());
        };
        require(
            row.evaluation_complete
                && inputs.len() == 2
                && entry.arguments.len() == 2
                && entry
                    .arguments
                    .argument(0)
                    .is_some_and(|(mode, _)| mode == ParameterMode::Mut)
                && entry
                    .arguments
                    .argument(1)
                    .is_some_and(|(mode, _)| mode == ParameterMode::Read),
            "record callback changed its original arity, modes or preparation",
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
            inputs[0] == InputOrigin::Widened(EvaluationOccurrenceId(receiver as u32)),
            "record callback borrowed another receiver observation",
        )?;
        let (ops_fact, ops_record, _) = self.observation(
            EvaluationOccurrenceId(ops as u32),
            entry.caller_context,
            entry.allocation_epoch,
            work,
        )?;
        let field = super::record_field_source(
            hir,
            ops_fact
                .source_id
                .ok_or("record callback operations lost their source")?,
            contract.field,
            work,
        )
        .ok_or("record callback lost its physical field operand")?;
        require(
            callee_fact.source_id == Some(field)
                && callee_activation.parent
                    == ops_record.identity.map(|identity| identity.activation),
            "record callback borrowed another physical field operand",
        )?;
        let (original, _, _) = self.observation(
            EvaluationOccurrenceId(receiver as u32),
            entry.caller_context,
            entry.allocation_epoch,
            work,
        )?;
        let scalar = match contract.scalar_source {
            super::ScalarSource::PositiveInt => ScalarInput::PositiveInt,
            super::ScalarSource::ByteSuffix(slot) => {
                ScalarInput::ByteSuffix(EvaluationOccurrenceId(
                    row.supplied
                        .get(&slot)
                        .ok_or("record callback byte source is absent")?
                        .expression as u32,
                ))
            }
            super::ScalarSource::BufferedBytes(slot) => {
                ScalarInput::BufferedBytes(EvaluationOccurrenceId(
                    row.supplied
                        .get(&slot)
                        .ok_or("record callback buffer source is absent")?
                        .expression as u32,
                ))
            }
        };
        require(
            inputs[1] == InputOrigin::Scalar(scalar),
            "record callback changed its generated scalar recipe",
        )?;
        Ok(Some(AuthenticatedGeneratedEntry {
            inputs: vec![
                GeneratedInput::Widened {
                    source: original
                        .source_id
                        .ok_or("record callback receiver lost its source")?,
                    observation: receiver,
                    original,
                },
                GeneratedInput::Scalar(scalar),
            ],
        }))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum GeneratedEntryKey {
    Closure(ClosureInvocationId),
    Named(InstanceId),
}

pub(crate) struct GeneratedEntryIndex<'a> {
    entries: BTreeMap<GeneratedEntryKey, AuthenticatedGeneratedEntry<'a>>,
}

impl<'a> GeneratedEntryIndex<'a> {
    pub(crate) fn new(facts: &'a SemanticFacts, work: &mut usize) -> Check<Self> {
        charge(work, facts.closure_invocations.len())?;
        charge(work, facts.copy_invocations.len())?;
        let records = GeneratedEntryRecords::new(facts, work)?;
        let mut entries = BTreeMap::new();
        for call in &facts.closure_invocations {
            if let Some(proof) = records.authenticate(
                EntryView::callable(&call.entry, Some(call.caller_activation)),
                GeneratedTarget::Closure(call.closure),
                work,
            )? {
                require(
                    entries
                        .insert(GeneratedEntryKey::Closure(call.id), proof)
                        .is_none(),
                    "generated closure entries have duplicate identities",
                )?;
            }
        }
        for call in &facts.copy_invocations {
            if let Some(proof) = records.authenticate(
                EntryView::callable(&call.entry, call.caller_activation),
                GeneratedTarget::Named(call.target),
                work,
            )? {
                require(
                    entries
                        .insert(GeneratedEntryKey::Named(call.id), proof)
                        .is_none(),
                    "generated named entries have duplicate identities",
                )?;
            }
        }
        Ok(Self { entries })
    }

    pub(crate) fn get(
        &self,
        key: GeneratedEntryKey,
        work: &mut usize,
    ) -> Check<&AuthenticatedGeneratedEntry<'a>> {
        charge(work, 1)?;
        self.entries
            .get(&key)
            .ok_or_else(|| "generated entry has no authenticated original operation".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_argument_budget_entries_authenticate_before_input_queries_and_obey_work() {
        let program = crate::Session::new(
            ril_test::case_bytes("tests/conformance/totality.ril::zero-one-budget").to_vec(),
        )
        .verify()
        .unwrap();
        let facts = program.facts();
        let entry = facts
            .scopes
            .records()
            .find_map(|record| match &record.origin {
                crate::sema::scopes::ScopeOrigin::Operation(entry)
                    if matches!(entry.origin, EntryOrigin::Generated { .. }) =>
                {
                    Some(entry)
                }
                _ => None,
            })
            .expect("the real zero-allowance recovery must retain its entered origin");
        assert!(GeneratedEntryRecords::new(facts, &mut 0).is_err());
        let mut index_work = 65_536;
        let records = GeneratedEntryRecords::new(facts, &mut index_work).unwrap();
        let view = || EntryView {
            origin: &entry.origin,
            parent: entry.parent,
            caller_activation: entry
                .parent
                .and_then(|id| facts.activations.get(id.0 as usize))
                .map(|parent| parent.scope),
            caller_context: entry.caller_context,
            allocation_epoch: entry.allocation_epoch,
            arguments: &(),
        };
        for mut available in [0, 1, 2] {
            assert!(
                records
                    .authenticate(
                        view(),
                        GeneratedTarget::Operation(entry.operation),
                        &mut available,
                    )
                    .is_err(),
                "an empty argument vector cannot bypass entry admission"
            );
        }
        let mut work = 65_536;
        let proof = records
            .authenticate(
                view(),
                GeneratedTarget::Operation(entry.operation),
                &mut work,
            )
            .unwrap()
            .unwrap();
        assert!(work < 65_536);
        assert!(proof.input(0).is_err());
        drop(records);
        assert!(proof.input(0).is_err(), "proofs borrow the original facts");
    }
}
