//! Reconstruct entered formal calls from physical application observations.
//! Invocation summaries cannot invent, drop, or borrow another activation's use.
use super::{SemanticFacts, facts::ScopeId, model::Callable};
use ril_compiler_core::ids::EvaluationOccurrenceId;
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn validate(facts: &SemanticFacts) -> Result<(), String> {
    let summaries: Vec<_> = facts
        .invocations
        .iter()
        .chain(
            facts
                .definition_checks
                .iter()
                .map(|check| &check.invocation),
        )
        .collect();
    let roots: BTreeSet<_> = summaries
        .iter()
        .filter_map(|summary| summary.activation)
        .collect();
    let represented: BTreeSet<_> = summaries
        .iter()
        .filter_map(|summary| Some((summary.activation?, summary.context?.invocation?)))
        .collect();
    let mut expected = BTreeMap::<ScopeId, BTreeSet<EvaluationOccurrenceId>>::new();
    let preparations: BTreeMap<_, _> = facts
        .call_arguments
        .iter()
        .map(|preparation| (preparation.source_event, preparation))
        .collect();
    let mut remaining = 1_000_000usize;
    for event in &facts.copy_call_events {
        remaining = remaining
            .checked_sub(1)
            .ok_or("symbolic call coverage exceeds its work bound")?;
        let Some(index) = event.callee_expression else {
            continue;
        };
        let Some(callee) = facts.expressions.get(index) else {
            return Err("symbolic call lost its physical callee".into());
        };
        if !callee
            .value
            .callables
            .iter()
            .any(|callable| matches!(callable, Callable::Symbolic(..)))
            || !callee.value.callback_parameters.iter().any(|id| {
                facts
                    .bindings
                    .get(*id)
                    .is_some_and(|binding| binding.parameter)
            })
            || preparations
                .get(&event.id)
                .is_none_or(|preparation| !preparation.evaluation_complete)
        {
            continue;
        }
        let record = facts
            .evaluations
            .get(index)
            .ok_or("symbolic call has no evaluation identity")?;
        if record.context.budget_validation {
            continue;
        }
        let mut scope = record.scope;
        let mut visited = BTreeSet::new();
        let mut named_summary = false;
        loop {
            remaining = remaining
                .checked_sub(1)
                .ok_or("symbolic call ancestry exceeds its work bound")?;
            if !visited.insert(scope) {
                return Err("symbolic call ancestry contains a cycle".into());
            }
            if roots.contains(&scope) {
                expected
                    .entry(scope)
                    .or_default()
                    .insert(EvaluationOccurrenceId(index as u32));
            }
            named_summary |= record
                .context
                .invocation
                .is_some_and(|invocation| represented.contains(&(scope, invocation)));
            let Some(parent) = facts.scope_parents.get(&scope) else {
                break;
            };
            scope = *parent;
        }
        // A lambda's creation-time body probe is not an entered dependency of
        // its surrounding named call. Actual closure entries have their own
        // recorded invocation; declaration probes of named bodies still count.
        let entered = if let Some(id) = record.context.closure_invocation {
            !facts
                .closure_invocations
                .get(id.0 as usize)
                .ok_or("symbolic call has no actual closure context")?
                .probe
        } else {
            matches!(
                record.context.owner,
                Some(ril_compiler_core::ids::CallableOwner::Function(_))
            )
        };
        if entered && record.context.invocation.is_some() && !named_summary {
            return Err("entered symbolic call lost its named invocation summary".into());
        }
    }
    for summary in summaries {
        let wanted = summary
            .activation
            .and_then(|activation| expected.get(&activation));
        if wanted.map_or(!summary.symbolic_uses.is_empty(), |wanted| {
            *wanted != summary.symbolic_uses
        }) {
            return Err("invocation symbolic uses differ from its entered formal calls".into());
        }
    }
    Ok(())
}
