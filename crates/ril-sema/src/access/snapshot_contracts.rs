use std::collections::BTreeSet;

use super::{SnapshotCall, SnapshotGraph, SnapshotInput, SnapshotOrigin, Summary};

type ProviderPairs = BTreeSet<(usize, usize)>;

pub(super) fn subsumes(baseline: &Summary, revision: &Summary) -> bool {
    if !inputs_subsume(&baseline.snapshot_inputs, &revision.snapshot_inputs) {
        return false;
    }
    if revision.snapshot_calls.is_empty() {
        return true;
    }

    // A recursive provider table is compatible when all its calls can be
    // matched by the old table under the same relation. Start with the pairs
    // allowed by the direct requirements and remove disproved pairs.
    let old = &baseline.snapshot_providers;
    let new = &revision.snapshot_providers;
    let mut pairs: ProviderPairs = old
        .iter()
        .enumerate()
        .flat_map(|(i, left)| {
            new.iter().enumerate().filter_map(move |(j, right)| {
                (left.via_parameters == right.via_parameters
                    && inputs_subsume(&left.inputs, &right.inputs))
                .then_some((i, j))
            })
        })
        .collect();
    loop {
        let next: ProviderPairs = pairs
            .iter()
            .copied()
            .filter(|&(i, j)| {
                old.get(i)
                    .zip(new.get(j))
                    .is_some_and(|(left, right)| calls_subsume(&left.calls, &right.calls, &pairs))
            })
            .collect();
        if next.len() == pairs.len() {
            break;
        }
        pairs = next;
    }
    calls_subsume(&baseline.snapshot_calls, &revision.snapshot_calls, &pairs)
}

fn inputs_subsume(old: &[SnapshotInput], new: &[SnapshotInput]) -> bool {
    new.iter()
        .all(|required| old.iter().any(|allowed| allowed.permits(required)))
}

fn calls_subsume(old: &[SnapshotCall], new: &[SnapshotCall], pairs: &ProviderPairs) -> bool {
    new.iter().all(|call| {
        old.iter().any(|allowed| {
            allowed.receiver == call.receiver
                && allowed.recursive_path == call.recursive_path
                && allowed.arguments.len() == call.arguments.len()
                && allowed
                    .arguments
                    .iter()
                    .zip(&call.arguments)
                    .all(|(left, right)| {
                        left.position == right.position
                            && left.mode == right.mode
                            && left.whole_graph == right.whole_graph
                            && graphs_subsume(&left.graph, &right.graph, pairs)
                    })
        })
    })
}

fn graphs_subsume(old: &SnapshotGraph, new: &SnapshotGraph, pairs: &ProviderPairs) -> bool {
    old.owned == new.owned
        && old.environment == new.environment
        && old.replaced == new.replaced
        && new.roots.iter().all(|root| {
            old.roots
                .iter()
                .any(|allowed| origins_subsume(allowed, root, pairs))
        })
        && old.members.len() == new.members.len()
        && old
            .members
            .iter()
            .zip(&new.members)
            .all(|((left, old), (right, new))| left == right && graphs_subsume(old, new, pairs))
}

fn origins_subsume(old: &SnapshotOrigin, new: &SnapshotOrigin, pairs: &ProviderPairs) -> bool {
    old.source == new.source
        && old.access == new.access
        && old.new == new.new
        && old.borrowed == new.borrowed
        && old.forwarded == new.forwarded
        && match (old.provider, new.provider) {
            (None, None) => true,
            (Some(old), Some(new)) => pairs.contains(&(old, new)),
            _ => false,
        }
}
