use std::collections::BTreeMap;

use super::{
    Analyzer, Datum, ProviderReferences, PublishedValue, Span, Summary, Ty,
    normalize_capture_sources, visit_callback_projections,
};
use crate::access::check::storage::ReadSite;
use crate::access::{
    CallbackArgument, Input, InvocationMode, SnapshotProjection, StorageObservation, StorageStep,
    StorageTransfer, StorageUpdate,
    flow::{
        DeferredStorageCall, Region, Replacement, StorageAction, StorageFlow, StorageRead,
        StorageTarget,
    },
};
use ril_frontend::syntax::Mode;

impl Analyzer<'_> {
    pub(in crate::access::check::calls::snapshot_invocations) fn register_storage_observations(
        &mut self,
        owner: Span,
        summary: &Summary,
    ) {
        for flow in summary.storage_flow.iter().chain(
            summary
                .snapshot_providers
                .iter()
                .filter_map(|provider| provider.storage_flow.as_ref()),
        ) {
            let paths = match flow {
                StorageTransfer::Paths(paths) => paths.as_slice(),
                StorageTransfer::Interleaved(steps) => std::slice::from_ref(steps),
            };
            for step in paths.iter().flatten() {
                if let StorageStep::Read { index, .. }
                | StorageStep::Derive { index, .. }
                | StorageStep::Clone { index, .. } = step
                {
                    self.storage_read_index(ReadSite::Imported(owner, *index));
                }
            }
        }
    }

    pub(super) fn imported_storage_observation(&self, owner: Span, index: usize) -> Option<usize> {
        self.storage_read_sites
            .get(&ReadSite::Imported(owner, index))
            .copied()
    }

    pub(in crate::access::check::calls::snapshot_invocations) fn publish_provider_flow(
        &self,
        owner: Span,
        references: &mut ProviderReferences,
    ) -> Option<StorageTransfer> {
        if let Some(closure) = self.closure_modes.get(&owner) {
            let mut formals = closure.formals.clone();
            formals.extend(closure.captures.iter().map(|&(binding, _)| Some(binding)));
            return Some(self.publish_storage_flow(
                owner,
                &formals,
                closure.storage_flow.as_ref()?,
                references,
            ));
        }
        let imported = self.snapshot_providers.imported_storage.get(&owner)?;
        let mut flow = imported.flow.clone()?;
        visit_observations(&mut flow, &mut |index| {
            let local = self
                .imported_storage_observation(imported.owner, *index)
                .unwrap_or(*index);
            *index = references.rebase_observation(local);
        });
        visit_projections(&mut flow, &mut |projections| {
            self.globalize_projections(imported.owner, projections);
            references.rebase_projections(projections);
        });
        Some(flow)
    }

    pub(in crate::access::check::calls::snapshot_invocations) fn publish_storage_flow(
        &self,
        owner: Span,
        formals: &[Option<Span>],
        flow: &StorageFlow,
        references: &mut ProviderReferences,
    ) -> StorageTransfer {
        let operand = |position, mode, mut value: Datum| {
            normalize_capture_sources(&mut value, owner, formals);
            let projections =
                self.snapshot_projections(formals, &Ty::Unknown, &[], std::slice::from_ref(&value));
            let mut operand = self.describe_callback_operand(formals, &(position, mode, value));
            operand.snapshot_projections = projections;
            operand
        };
        let describe = |action: &StorageAction| match action {
            StorageAction::Write(StorageTarget::Entry(target), update) => {
                let mut update = update.clone();
                normalize_capture_sources(&mut update.value, owner, formals);
                let projections = self.snapshot_projections(
                    formals,
                    &Ty::Unknown,
                    &target.selection,
                    std::slice::from_ref(&update.value),
                );
                let mut contract = self
                    .describe_storage_updates(formals, &BTreeMap::from([(target.clone(), update)]))
                    .pop()?;
                contract.snapshot_projections = projections;
                Some(StorageStep::Write(contract))
            }
            StorageAction::Write(StorageTarget::Observed { parent, member }, update) => {
                Some(StorageStep::WriteObserved {
                    parent: StorageObservation {
                        index: parent.index,
                        path: parent.path.clone(),
                    },
                    member: member.clone(),
                    value: operand(0, Mode::Via, update.value.clone()),
                    definite: update.definite,
                })
            }
            StorageAction::Invoke(call) => Some(StorageStep::Invoke {
                receiver: operand(0, Mode::Via, call.receiver.clone()),
                arguments: call
                    .arguments
                    .iter()
                    .map(|(position, mode, value)| operand(*position, *mode, value.clone()))
                    .collect(),
            }),
            StorageAction::Read {
                index,
                base,
                coordinate,
                mode,
            } => Some(StorageStep::Read {
                index: *index,
                base: operand(0, Mode::Via, base.clone()),
                coordinate: coordinate.clone(),
                mode: Input::from_mode(*mode),
            }),
            StorageAction::Derive {
                index,
                base,
                updater,
            } => Some(StorageStep::Derive {
                index: *index,
                base: operand(0, Mode::Plain, base.clone()),
                updater: operand(1, Mode::Via, updater.clone()),
            }),
            StorageAction::Clone { index, base } => Some(StorageStep::Clone {
                index: *index,
                base: operand(0, Mode::Via, base.clone()),
            }),
        };
        let mut contract = match flow {
            StorageFlow::Paths(paths) => StorageTransfer::Paths(
                paths
                    .iter()
                    .map(|path| path.iter().filter_map(describe).collect())
                    .collect(),
            ),
            StorageFlow::Interleaved(actions) => {
                StorageTransfer::Interleaved(actions.iter().filter_map(describe).collect())
            }
        };
        visit_observations(&mut contract, &mut |index| {
            *index = references.rebase_observation(*index);
        });
        visit_projections(&mut contract, &mut |projections| {
            references.rebase_projections(projections);
        });
        contract
    }

    pub(in crate::access::check::calls) fn load_storage_flow(
        &mut self,
        (owner, identity): (Span, Span),
        formals: &[Option<Span>],
        contract: &StorageTransfer,
        target: impl Fn(&StorageUpdate) -> Option<Region>,
    ) -> StorageFlow {
        let mut ordinal = 0;
        let mut decode = |step: &StorageStep| {
            ordinal += 1;
            match step {
                StorageStep::Write(update) => Some(StorageAction::Write(
                    StorageTarget::Entry(target(update)?),
                    self.decode_storage_write(owner, formals, update),
                )),
                StorageStep::WriteObserved {
                    parent,
                    member,
                    value,
                    definite,
                } => Some(StorageAction::Write(
                    StorageTarget::Observed {
                        parent: StorageRead {
                            index: self.imported_storage_observation(owner, parent.index)?,
                            path: parent.path.clone(),
                        },
                        member: member.clone(),
                    },
                    Replacement {
                        value: self.decode_storage_operand(owner, formals, value),
                        definite: *definite,
                    },
                )),
                StorageStep::Invoke {
                    receiver,
                    arguments,
                } => {
                    let receiver = self.decode_storage_operand(owner, formals, receiver);
                    let arguments: Vec<_> = arguments
                        .iter()
                        .map(|argument| {
                            let mode = match argument.modes.as_slice() {
                                [InvocationMode::Input(input)] => input.mode(),
                                _ => Mode::Via,
                            };
                            (
                                argument.position,
                                mode,
                                self.decode_storage_operand(owner, formals, argument),
                            )
                        })
                        .collect();
                    // The ordinal distinguishes call steps within this summary.
                    // Diagnostics use the caller's source span.
                    let site = Span::new(identity.file, identity.start, usize::MAX - ordinal);
                    Some(StorageAction::Invoke(DeferredStorageCall {
                        site,
                        receiver,
                        spans: vec![owner; arguments.len()],
                        arguments,
                    }))
                }
                StorageStep::Read {
                    index,
                    base,
                    coordinate,
                    mode,
                } => Some(StorageAction::Read {
                    index: self.imported_storage_observation(owner, *index)?,
                    base: self.decode_storage_operand(owner, formals, base),
                    coordinate: coordinate.clone(),
                    mode: mode.map_or(Mode::Via, Input::mode),
                }),
                StorageStep::Derive {
                    index,
                    base,
                    updater,
                } => Some(StorageAction::Derive {
                    index: self.imported_storage_observation(owner, *index)?,
                    base: self.decode_storage_operand(owner, formals, base),
                    updater: self.decode_storage_operand(owner, formals, updater),
                }),
                StorageStep::Clone { index, base } => Some(StorageAction::Clone {
                    index: self.imported_storage_observation(owner, *index)?,
                    base: self.decode_storage_operand(owner, formals, base),
                }),
            }
        };
        match contract {
            StorageTransfer::Paths(paths) => StorageFlow::Paths(
                paths
                    .iter()
                    .map(|path| path.iter().filter_map(&mut decode).collect())
                    .collect(),
            ),
            StorageTransfer::Interleaved(actions) => {
                StorageFlow::Interleaved(actions.iter().filter_map(decode).collect())
            }
        }
    }

    pub(super) fn decode_storage_write(
        &mut self,
        owner: Span,
        formals: &[Option<Span>],
        update: &StorageUpdate,
    ) -> Replacement {
        let value = self.exported_value(
            owner,
            formals,
            PublishedValue {
                sources: &update.sources,
                callbacks: &update.callback_returns,
                projections: &update.snapshot_projections,
                allocations: &update.allocations,
                constructs: update.constructs,
            },
            &Ty::Unknown,
        );
        Replacement {
            value,
            definite: update.definite,
        }
    }

    fn decode_storage_operand(
        &mut self,
        owner: Span,
        formals: &[Option<Span>],
        argument: &CallbackArgument,
    ) -> Datum {
        self.exported_value(
            owner,
            formals,
            PublishedValue {
                sources: &argument.sources,
                callbacks: &argument.callback_returns,
                projections: &argument.snapshot_projections,
                allocations: &argument.allocations,
                constructs: argument.constructs,
            },
            &Ty::Unknown,
        )
    }
}

fn visit_projections(
    flow: &mut StorageTransfer,
    visit: &mut impl FnMut(&mut [SnapshotProjection]),
) {
    let (paths, actions) = match flow {
        StorageTransfer::Paths(paths) => (Some(paths), None),
        StorageTransfer::Interleaved(actions) => (None, Some(actions)),
    };
    for step in paths
        .into_iter()
        .flatten()
        .flatten()
        .chain(actions.into_iter().flatten())
    {
        match step {
            StorageStep::Write(update) => {
                visit(&mut update.snapshot_projections);
                visit_callback_projections(&mut update.callback_returns, visit);
            }
            StorageStep::Invoke {
                receiver,
                arguments,
            } => {
                for argument in std::iter::once(receiver).chain(arguments) {
                    visit(&mut argument.snapshot_projections);
                    visit_callback_projections(&mut argument.callback_returns, visit);
                }
            }
            StorageStep::Read { base, .. }
            | StorageStep::Clone { base, .. }
            | StorageStep::WriteObserved { value: base, .. } => {
                visit(&mut base.snapshot_projections);
                visit_callback_projections(&mut base.callback_returns, visit);
            }
            StorageStep::Derive { base, updater, .. } => {
                for operand in [base, updater] {
                    visit(&mut operand.snapshot_projections);
                    visit_callback_projections(&mut operand.callback_returns, visit);
                }
            }
        }
    }
}

fn visit_observations(flow: &mut StorageTransfer, visit: &mut impl FnMut(&mut usize)) {
    let paths = match flow {
        StorageTransfer::Paths(paths) => paths.as_mut_slice(),
        StorageTransfer::Interleaved(steps) => std::slice::from_mut(steps),
    };
    for step in paths.iter_mut().flatten() {
        match step {
            StorageStep::Read { index, .. }
            | StorageStep::Derive { index, .. }
            | StorageStep::Clone { index, .. } => visit(index),
            StorageStep::WriteObserved { parent, .. } => visit(&mut parent.index),
            _ => {}
        }
    }
}
