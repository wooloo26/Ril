use std::collections::{BTreeMap, BTreeSet};

use ril_base::span::Span;

use super::{Analyzer, Datum, DefinitionCheck, Ledger, Region, Replacement, collect};
use crate::access::flow::{Coordinate, InvocationSite, StorageFlow};
use crate::ty::TypedProgram;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum ReadSite {
    Source(Span, Coordinate),
    Derive(Span),
    Clone(Span),
    Imported(Span, usize),
    Forwarded(Span, Vec<InvocationSite>, usize),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum ReplaySite {
    Callback(Span),
    Derive(usize),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct CallStorage {
    pub formals: Vec<Option<Span>>,
    pub via: BTreeSet<Span>,
    pub updates: BTreeMap<Region, Replacement>,
    pub flow: Option<StorageFlow>,
    pub result: Option<Datum>,
    pub normal_exit: bool,
}

impl CallStorage {
    pub(super) fn updates_of(function: &DefinitionCheck) -> Self {
        Self {
            formals: function.formals.clone(),
            via: function.via.clone(),
            updates: function.updates.clone(),
            flow: function.storage_flow.clone(),
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
            flow: join_flows([(&self.updates, &self.flow), (&other.updates, &other.flow)]),
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
            .chain(self.flow.iter().flat_map(StorageFlow::values))
    }

    fn clear_activation_choices(&mut self) {
        let values = self
            .updates
            .values_mut()
            .map(|update| &mut update.value)
            .chain(&mut self.result);
        let values = values.chain(self.flow.iter_mut().flat_map(StorageFlow::values_mut));
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

pub(super) struct StorageExit {
    pub updates: BTreeMap<Region, Replacement>,
    pub flow: Option<StorageFlow>,
}

impl StorageExit {
    pub(super) fn join(exits: &[Self]) -> Self {
        Self {
            updates: Ledger::join_updates(exits.iter().map(|exit| &exit.updates).collect()),
            flow: join_flows(exits.iter().map(|exit| (&exit.updates, &exit.flow))),
        }
    }
}

fn join_flows<'a>(
    paths: impl IntoIterator<Item = (&'a BTreeMap<Region, Replacement>, &'a Option<StorageFlow>)>,
) -> Option<StorageFlow> {
    let paths: Vec<_> = paths.into_iter().collect();
    paths.iter().any(|(_, flow)| flow.is_some()).then(|| {
        StorageFlow::join(paths.into_iter().map(|(updates, flow)| {
            flow.clone()
                .unwrap_or_else(|| StorageFlow::writes(updates.clone()))
        }))
    })
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
        .chain(
            function
                .storage_flow
                .iter()
                .flat_map(StorageFlow::values)
                .map(value_depth),
        )
        .max()
        .unwrap_or_default()
}

// The base point for recursive calls has no finite normal execution. Each pass
// adds the continuations justified by the previous pass and repeats the ordinary
// ledger transfer, so sites following a call see the stabilized values.
pub(super) fn solve_recursive_storage(program: &TypedProgram) -> Analyzer<'_> {
    let discovery = collect(program, BTreeMap::new(), BTreeMap::new());
    let mut targets = discovery.recursive_calls.clone();
    if targets.is_empty() {
        return discovery;
    }
    let mut opaque = BTreeSet::new();
    let mut reads = discovery.storage_read_sites.clone();
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
            let pass = collect(program, summaries.clone(), reads);
            reads = pass.storage_read_sites.clone();
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
