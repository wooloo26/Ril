use ril_base::span::Span;
use ril_frontend::syntax::Mode;

use super::{
    Access, Analyzer, CallEntry, CallEnvironment, CallStorage, Datum, Ledger, StorageAction,
    StorageFlow, StorageTarget, snapshot_invocations::known_provider,
};
use crate::access::flow::{Coordinate, Replacement};

impl Analyzer<'_> {
    pub(super) fn derived_snapshot(
        &mut self,
        ledger: &Ledger,
        base: &Datum,
        callback: &Datum,
        span: Span,
    ) -> Datum {
        let base = ledger.snapshot_for_draft(base);
        let arguments = [(0, Mode::Mut, base.clone())];
        let entry = CallEntry {
            arguments: &arguments,
            spans: &[span],
            ledger,
            span,
            invocation: &[],
            environment: None,
        };
        let mut alternatives = Vec::new();
        for origin in &callback.roots {
            let Some(owner) = known_provider(origin) else {
                alternatives.push(base.clone());
                continue;
            };
            if let Some(closure) = self.closure_modes.get(&owner).cloned() {
                let captures = Self::closure_captures(ledger, callback, origin, &closure);
                let storage = CallStorage {
                    formals: closure.formals,
                    via: closure.via,
                    updates: closure.updates,
                    flow: closure.storage_flow,
                    ..CallStorage::default()
                };
                let entry = CallEntry {
                    environment: Some(CallEnvironment {
                        owner,
                        bindings: Some(&captures),
                    }),
                    ..entry
                };
                alternatives.push(self.replay_draft_storage(&base, &entry, &storage));
            } else if let Some(call) = self.provider_storage_call((owner, origin, callback), &entry)
            {
                let entry = CallEntry {
                    arguments: &call.arguments,
                    spans: &call.spans,
                    ..entry
                };
                alternatives.push(self.replay_draft_storage(&base, &entry, &call.storage));
            } else {
                if let Some(function) = self
                    .definition(owner)
                    .and_then(|id| self.function_syntax(id))
                    && function.body.is_some()
                {
                    self.function(function, ledger);
                }
                let storage = self
                    .functions
                    .iter()
                    .find(|fun| fun.owner == owner)
                    .map(CallStorage::updates_of)
                    .or_else(|| self.imported_draft_storage(owner, &entry));
                alternatives.push(storage.map_or_else(
                    || base.clone(),
                    |storage| self.replay_draft_storage(&base, &entry, &storage),
                ));
            }
        }
        let mut result = alternatives
            .into_iter()
            .reduce(Datum::join_draft_results)
            .unwrap_or(base);
        result.freeze();
        result
    }

    fn replay_draft_storage(
        &mut self,
        base: &Datum,
        entry: &CallEntry<'_>,
        storage: &CallStorage,
    ) -> Datum {
        let Some(formal) = storage.formals.first().copied().flatten() else {
            return base.clone();
        };
        // A draft path follows the current working value even when two
        // paths originally referred to the same immutable object.
        if let Some(StorageFlow::Paths(paths)) = &storage.flow
            && paths
                .iter()
                .flatten()
                .all(|step| !matches!(step, StorageAction::Invoke(_)))
        {
            return paths
                .iter()
                .map(|steps| {
                    let mut working = base.clone();
                    let mut samples = entry.ledger.clone();
                    for step in steps {
                        let ledger = entry.ledger.with_storage_samples(&samples);
                        let observed = CallEntry {
                            ledger: &ledger,
                            ..*entry
                        };
                        match step {
                            StorageAction::Write(StorageTarget::Entry(target), update)
                                if target.source == formal =>
                            {
                                self.replay_draft_store(
                                    &mut working,
                                    &observed,
                                    storage,
                                    &target.selection,
                                    update,
                                );
                            }
                            StorageAction::Read {
                                index,
                                base,
                                coordinate,
                                mode,
                            } => {
                                let mut base = base.clone();
                                if base.roots.iter().all(|root| root.region.source == formal) {
                                    // Keep data from the working graph, including writes
                                    // already replayed at more precise array positions.
                                    base.members.clear();
                                }
                                let mut arguments = entry.arguments.to_vec();
                                if let Some((_, _, draft)) =
                                    arguments.iter_mut().find(|(position, ..)| *position == 0)
                                {
                                    *draft = working.clone();
                                }
                                let access = CallEntry {
                                    arguments: &arguments,
                                    ..observed
                                };
                                let root = self.instantiate_return(
                                    &storage.formals,
                                    &storage.via,
                                    &access,
                                    &base,
                                    &mut Vec::new(),
                                );
                                let selected =
                                    root.project(coordinate.clone(), Access::from_mode(*mode));
                                samples.sample_storage(
                                    (entry.span, entry.invocation.to_vec(), *index),
                                    selected,
                                );
                            }
                            _ => {}
                        }
                    }
                    working
                })
                .reduce(Datum::join_draft_results)
                .unwrap_or_else(|| base.clone());
        }
        let mut working = base.clone();
        for (target, update) in &storage.updates {
            if target.source == formal {
                self.replay_draft_store(&mut working, entry, storage, &target.selection, update);
            }
        }
        working
    }

    fn replay_draft_store(
        &mut self,
        working: &mut Datum,
        entry: &CallEntry<'_>,
        storage: &CallStorage,
        path: &[Coordinate],
        update: &Replacement,
    ) {
        let stored = self.instantiate_return(
            &storage.formals,
            &storage.via,
            entry,
            &update.value,
            &mut path.to_vec(),
        );
        let mut stored = entry.ledger.snapshot_for_draft(&stored);
        stored.freeze();
        working.apply_draft_update(path, &stored, update.definite);
    }
}
