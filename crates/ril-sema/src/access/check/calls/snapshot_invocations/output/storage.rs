use std::collections::BTreeMap;

use super::{
    Analyzer, Datum, ProviderReferences, PublishedValue, Span, Ty, normalize_capture_sources,
    visit_callback_projections,
};
use crate::access::{
    CallbackArgument, InvocationMode, SnapshotProjection, StorageStep, StorageTransfer,
    StorageUpdate,
    flow::{DeferredStorageCall, Region, Replacement, StorageAction, StorageFlow},
};
use ril_frontend::syntax::Mode;

impl Analyzer<'_> {
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
            StorageAction::Write(target, update) => {
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
            StorageAction::Invoke(call) => Some(StorageStep::Invoke {
                receiver: operand(0, Mode::Via, call.receiver.clone()),
                arguments: call
                    .arguments
                    .iter()
                    .map(|(position, mode, value)| operand(*position, *mode, value.clone()))
                    .collect(),
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
                    target(update)?,
                    self.decode_storage_write(owner, formals, update),
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
        }
    }
}
