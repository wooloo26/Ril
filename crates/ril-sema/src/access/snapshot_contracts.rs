use std::collections::BTreeSet;

use super::{
    SnapshotArgument, SnapshotCall, SnapshotGraph, SnapshotInput, SnapshotOrigin,
    SnapshotProjection, Summary,
};

type ProviderPairs = BTreeSet<(usize, usize)>;

pub(super) fn subsumes(baseline: &Summary, revision: &Summary) -> bool {
    if !inputs_subsume(&baseline.snapshot_inputs, &revision.snapshot_inputs) {
        return false;
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
                old.get(i).zip(new.get(j)).is_some_and(|(left, right)| {
                    calls_subsume(&left.calls, &right.calls, &pairs)
                        && (!left.returns_new || right.returns_new)
                        && projections_subsume(&left.returns, &right.returns, &pairs)
                        && callback_returns_subsume(
                            &left.callback_returns,
                            &right.callback_returns,
                            &pairs,
                        )
                })
            })
            .collect();
        if next.len() == pairs.len() {
            break;
        }
        pairs = next;
    }
    calls_subsume(&baseline.snapshot_calls, &revision.snapshot_calls, &pairs)
        && callback_returns_subsume(
            &baseline.callback_returns,
            &revision.callback_returns,
            &pairs,
        )
        && projections_subsume(
            &baseline.snapshot_returns,
            &revision.snapshot_returns,
            &pairs,
        )
        && revision.storage_updates.iter().all(|update| {
            baseline.storage_updates.iter().any(|old| {
                old.permits(update)
                    && callback_returns_subsume(
                        &old.callback_returns,
                        &update.callback_returns,
                        &pairs,
                    )
                    && projections_subsume(
                        &old.snapshot_projections,
                        &update.snapshot_projections,
                        &pairs,
                    )
            })
        })
}

fn callback_returns_subsume(
    old: &[super::CallbackReturn],
    new: &[super::CallbackReturn],
    pairs: &ProviderPairs,
) -> bool {
    new.iter().all(|result| {
        old.iter()
            .any(|offered| callback_return_subsumes(offered, result, pairs))
    })
}

fn callback_return_subsumes(
    old: &super::CallbackReturn,
    new: &super::CallbackReturn,
    pairs: &ProviderPairs,
) -> bool {
    old.invocation == new.invocation
        && old.receiver == new.receiver
        && old.receiver_path == new.receiver_path
        && old.source_path == new.source_path
        && old.result_path == new.result_path
        && old.cap == new.cap
        && old.arguments.len() == new.arguments.len()
        && old
            .arguments
            .iter()
            .zip(&new.arguments)
            .all(|(left, right)| {
                left.position == right.position
                    && left.modes == right.modes
                    && left.sources == right.sources
                    && left.allocations == right.allocations
                    && left.constructs == right.constructs
                    && projections_subsume(
                        &left.snapshot_projections,
                        &right.snapshot_projections,
                        pairs,
                    )
                    && left.callback_returns.len() == right.callback_returns.len()
                    && left
                        .callback_returns
                        .iter()
                        .zip(&right.callback_returns)
                        .all(|(left, right)| callback_return_subsumes(left, right, pairs))
            })
}

fn projections_subsume(
    old: &[SnapshotProjection],
    new: &[SnapshotProjection],
    pairs: &ProviderPairs,
) -> bool {
    new.iter().all(|required| {
        old.iter().any(|allowed| {
            allowed.path == required.path
                && allowed.qualified == required.qualified
                && allowed.allocation == required.allocation
                && origins_subsume(&allowed.origin, &required.origin, pairs)
        })
    })
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
                && allowed.factory_steps.len() == call.factory_steps.len()
                && allowed
                    .factory_steps
                    .iter()
                    .zip(&call.factory_steps)
                    .all(|(left, right)| {
                        left.path == right.path
                            && left.cap == right.cap
                            && arguments_subsume(&left.arguments, &right.arguments, pairs)
                    })
                && arguments_subsume(&allowed.arguments, &call.arguments, pairs)
        })
    })
}

fn arguments_subsume(
    old: &[SnapshotArgument],
    new: &[SnapshotArgument],
    pairs: &ProviderPairs,
) -> bool {
    old.len() == new.len()
        && old.iter().zip(new).all(|(left, right)| {
            left.position == right.position
                && left.mode == right.mode
                && left.whole_graph == right.whole_graph
                && graphs_subsume(&left.graph, &right.graph, pairs)
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
