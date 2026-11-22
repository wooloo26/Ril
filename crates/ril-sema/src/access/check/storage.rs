use std::collections::{BTreeMap, BTreeSet};

use ril_base::span::Span;

use super::{Analyzer, Datum, DefinitionCheck, Ledger, Region, Replacement, collect};
use crate::ty::TypedProgram;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct CallStorage {
    pub formals: Vec<Option<Span>>,
    pub via: BTreeSet<Span>,
    pub updates: BTreeMap<Region, Replacement>,
    pub result: Option<Datum>,
    pub normal_exit: bool,
}

impl CallStorage {
    pub(super) fn updates_of(function: &DefinitionCheck) -> Self {
        Self {
            formals: function.formals.clone(),
            via: function.via.clone(),
            updates: function.updates.clone(),
            normal_exit: function.normal_exit,
            result: None,
        }
    }

    fn join(self, other: Self) -> Self {
        if !self.normal_exit {
            return other;
        }
        if !other.normal_exit {
            return self;
        }
        Self {
            updates: Ledger::join_updates(vec![&self.updates, &other.updates]),
            result: self
                .result
                .into_iter()
                .chain(other.result)
                .reduce(Datum::joined),
            ..self
        }
    }

    fn values(&self) -> impl Iterator<Item = &Datum> {
        self.updates
            .values()
            .map(|update| &update.value)
            .chain(&self.result)
    }

    fn clear_activation_choices(&mut self) {
        let values = self
            .updates
            .values_mut()
            .map(|update| &mut update.value)
            .chain(&mut self.result);
        for value in values {
            value.transform(&mut |origin| origin.branches.clear());
        }
    }

    fn representable(&self, depth: usize) -> bool {
        self.updates
            .keys()
            .all(|target| target.selection.len() <= depth)
            && self.values().all(|value| {
                value_depth(value) <= depth
                    && value
                        .origins()
                        .all(|origin| origin.callback_result.is_none())
            })
    }
}

fn value_depth(value: &Datum) -> usize {
    let paths = value
        .roots
        .iter()
        .map(|root| root.region.selection.len().max(root.reception.len()));
    paths
        .chain(value.members.values().map(|member| 1 + value_depth(member)))
        .max()
        .unwrap_or_default()
}

fn function_depth(function: &DefinitionCheck) -> usize {
    function
        .updates
        .iter()
        .map(|(target, update)| target.selection.len().max(value_depth(&update.value)))
        .chain(function.returns.iter().map(value_depth))
        .max()
        .unwrap_or_default()
}

// The base point for recursive calls has no finite normal execution. Each pass
// adds the continuations justified by the previous pass and repeats the ordinary
// ledger transfer, so sites following a call see the stabilized values.
pub(super) fn solve_recursive_storage(program: &TypedProgram) -> Analyzer<'_> {
    let discovery = collect(program, BTreeMap::new());
    let mut targets = discovery.recursive_calls.clone();
    if targets.is_empty() {
        return discovery;
    }
    let mut opaque = BTreeSet::new();
    loop {
        let mut summaries: BTreeMap<_, _> = targets
            .difference(&opaque)
            .map(|&owner| (owner, CallStorage::default()))
            .collect();
        if summaries.is_empty() {
            return discovery;
        }
        // Allow compositions of the tracked paths. A recursively growing heap
        // path or an invocation-local callback ID needs an opaque call model.
        let depth = discovery
            .functions
            .iter()
            .map(function_depth)
            .max()
            .unwrap_or_default()
            .saturating_add(targets.len());
        loop {
            let pass = collect(program, summaries.clone());
            let old_len = targets.len();
            targets.extend(pass.recursive_calls.iter().copied());
            if old_len != targets.len() {
                break;
            }
            let mut next = BTreeMap::new();
            for (&owner, previous) in &summaries {
                let Some(function) = pass
                    .functions
                    .iter()
                    .find(|function| function.owner == owner)
                else {
                    next.insert(owner, previous.clone());
                    continue;
                };
                let mut current = CallStorage::updates_of(function);
                current.result = function.returns.iter().cloned().reduce(Datum::joined);
                current.clear_activation_choices();
                let expanded = previous.clone().join(current);
                if !expanded.representable(depth) {
                    opaque.insert(owner);
                }
                next.insert(owner, expanded);
            }
            if next.keys().any(|owner| opaque.contains(owner)) {
                // An opaque callee may add normal paths. Restart its callers
                // from the base point before relying on any write guarantees.
                break;
            }
            if next == summaries {
                return pass;
            }
            summaries = next;
        }
    }
}
