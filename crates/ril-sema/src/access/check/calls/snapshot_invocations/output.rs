use std::collections::BTreeSet;

use super::{
    Analyzer, CallEntry, Datum, Provider, ProviderReferences, Span, axis, known_provider,
    visit_callback_projections,
};
use crate::access::check::calls::{ProviderStorageCall, imported::PublishedValue};
use crate::{
    access::{
        Access, Coordinate, SnapshotOrigin, SnapshotProjection, StorageObservation,
        StorageTransfer, StorageUpdate, Summary,
        check::{DefinitionCheck, storage::CallStorage},
        flow::{Origin, Region, StorageRead},
    },
    ty::{Ty, TypedProgram},
};

mod storage;

#[derive(Clone)]
pub(super) struct ImportedResult {
    pub(super) owner: Span,
    pub(super) signature: Provider,
    pub(super) result: ProviderResult,
}

#[derive(Clone)]
pub(super) struct ImportedStorage {
    pub(super) owner: Span,
    pub(super) signature: Provider,
    pub(super) captures: Vec<Option<Span>>,
    pub(super) slots: Vec<bool>,
    pub(super) updates: Vec<StorageUpdate>,
    pub(super) flow: Option<StorageTransfer>,
}

#[derive(Clone, Default)]
pub(super) struct ProviderResult {
    pub(super) projections: Vec<SnapshotProjection>,
    pub(super) callbacks: Vec<crate::access::CallbackReturn>,
    pub(super) constructs: bool,
}

impl Analyzer<'_> {
    pub(super) fn publish_provider_storage(
        &self,
        owner: Span,
        references: &mut ProviderReferences,
    ) -> (Vec<bool>, Vec<StorageUpdate>) {
        let (slots, mut updates) = if let Some(closure) = self.closure_modes.get(&owner) {
            let mut formals = closure.formals.clone();
            formals.extend(closure.captures.iter().map(|&(binding, _)| Some(binding)));
            let mut normalized = closure.updates.clone();
            for update in normalized.values_mut() {
                normalize_capture_sources(&mut update.value, owner, &formals);
            }
            let mut updates = self.describe_storage_updates(&formals, &normalized);
            for update in &mut updates {
                let Some(binding) = formals.get(update.formal).copied().flatten() else {
                    continue;
                };
                let mut target = Region::root(binding);
                target.selection.clone_from(&update.path);
                if let Some(source) = normalized.get(&target) {
                    update.snapshot_projections = self.snapshot_projections(
                        &formals,
                        &Ty::Unknown,
                        &update.path,
                        std::slice::from_ref(&source.value),
                    );
                }
            }
            let slots = closure.captures.iter().map(|&(_, slot)| slot).collect();
            (slots, updates)
        } else if let Some(imported) = self.snapshot_providers.imported_storage.get(&owner) {
            let mut updates = imported.updates.clone();
            for update in &mut updates {
                let mut rebase = |projections: &mut [SnapshotProjection]| {
                    self.globalize_projections(imported.owner, projections);
                };
                rebase(&mut update.snapshot_projections);
                visit_callback_projections(&mut update.callback_returns, &mut rebase);
            }
            (imported.slots.clone(), updates)
        } else {
            return (Vec::new(), Vec::new());
        };
        for update in &mut updates {
            references.rebase_projections(&mut update.snapshot_projections);
            references.rebase_callback_returns(&mut update.callback_returns);
        }
        (slots, updates)
    }

    fn globalize_projections(&self, owner: Span, projections: &mut [SnapshotProjection]) {
        for projection in projections {
            projection.origin.provider = projection.origin.provider.and_then(|index| {
                let provider = self.snapshot_providers.imported.get(&owner)?.get(index)?;
                self.snapshot_providers.sources.binary_search(provider).ok()
            });
            if let Some(read) = &mut projection.observation {
                read.index = self
                    .imported_storage_observation(owner, read.index)
                    .unwrap_or(read.index);
            }
        }
    }

    pub(in crate::access::check::calls) fn has_imported_provider_storage(
        &self,
        owner: Span,
    ) -> bool {
        self.snapshot_providers
            .imported_storage
            .get(&owner)
            .is_some_and(|storage| !storage.updates.is_empty() || storage.flow.is_some())
    }

    pub(in crate::access::check::calls) fn replay_provider_storage(
        &mut self,
        ctx: &super::Context,
        (provider, root, receiver): (Span, &Origin, &Datum),
        entry: &CallEntry<'_>,
        ledger: &mut super::Ledger,
    ) {
        let Some(call) = self.provider_storage_call((provider, root, receiver), entry) else {
            return;
        };
        let entry = CallEntry {
            arguments: &call.arguments,
            spans: &call.spans,
            ..*entry
        };
        self.apply_callable_storage(ctx, call.storage, &entry, ledger, true);
    }

    pub(in crate::access::check::calls) fn provider_storage_call(
        &mut self,
        (provider, root, receiver): (Span, &Origin, &Datum),
        entry: &CallEntry<'_>,
    ) -> Option<ProviderStorageCall> {
        let storage = self
            .snapshot_providers
            .imported_storage
            .get(&provider)
            .cloned()?;
        let parameter_count = storage.signature.formals.len();
        let mut formals = storage.signature.formals;
        formals.extend(&storage.captures);
        // Reify the environment as hidden call inputs. A store to a captured
        // slot itself selects an environment position through the receiver.
        let receiver_index = formals.len();
        formals.push(Some(provider));
        let mut receiver = receiver.clone();
        receiver.retain_compatible_origins(&root.branches);
        receiver.roots.retain(|origin| origin == root);
        let mut arguments = entry.arguments.to_vec();
        let mut spans = entry.spans.to_vec();
        for (index, &binding) in storage.captures.iter().enumerate() {
            let Some(binding) = binding else { continue };
            let mut value =
                entry
                    .ledger
                    .project(&receiver, Coordinate::Index(index.to_string()), Access::Mut);
            if storage.slots.get(index) == Some(&true) {
                value = entry
                    .ledger
                    .project(&value, Coordinate::Index("0".into()), Access::Mut);
            }
            arguments.push((parameter_count + index, super::Mode::Mut, value));
            spans.push(binding);
        }
        arguments.push((receiver_index, super::Mode::Mut, receiver));
        spans.push(provider);
        let capture_target = |update: &StorageUpdate| {
            let source = formals.get(update.formal).copied().flatten()?;
            let mut target = Region::root(source);
            if update.path.is_empty() {
                let index = update.formal.checked_sub(parameter_count)?;
                if storage.slots.get(index) != Some(&true) {
                    return None;
                }
                target = Region::root(provider);
                target.selection.push(Coordinate::Index(index.to_string()));
                target.selection.push(Coordinate::Index("0".into()));
            } else {
                target.selection.clone_from(&update.path);
            }
            Some(target)
        };
        let updates = storage
            .updates
            .iter()
            .filter_map(|update| {
                let target = capture_target(update)?;
                Some((
                    target,
                    self.decode_storage_write(storage.owner, &formals, update),
                ))
            })
            .collect();
        let flow = storage.flow.as_ref().map(|flow| {
            self.load_storage_flow((storage.owner, provider), &formals, flow, capture_target)
        });
        let storage = CallStorage {
            formals,
            via: storage.signature.via,
            updates,
            flow,
            ..CallStorage::default()
        };
        Some(ProviderStorageCall {
            storage,
            arguments,
            spans,
        })
    }

    pub(in crate::access::check::calls) fn snapshot_argument_providers(
        &self,
        formals: &[Option<Span>],
        value: &Datum,
    ) -> Vec<SnapshotProjection> {
        self.snapshot_projections(formals, &Ty::Unknown, &[], std::slice::from_ref(value))
            .into_iter()
            .filter(|projection| {
                projection.origin.provider.is_some() || projection.observation.is_some()
            })
            .collect()
    }

    pub(super) fn prepare_snapshot_provider_results(&mut self) {
        let named = self.functions.iter().map(|function| {
            (
                function.owner,
                self.describe_provider_result(
                    &function.formals,
                    &function.declared.result,
                    &function.returns,
                    function.returned_new,
                ),
            )
        });
        let closures = self.closure_modes.iter().filter_map(|(&owner, closure)| {
            let Ty::Callable(signature) = self.ty(owner) else {
                return None;
            };
            let new = !closure.returns.is_empty()
                && closure.returns.iter().all(|value| value.requires_new);
            Some((
                owner,
                self.describe_provider_result(
                    &closure.formals,
                    &signature.result,
                    &closure.returns,
                    new,
                ),
            ))
        });
        let imported = self
            .snapshot_providers
            .imported_results
            .iter()
            .map(|(&id, result)| {
                let mut value = result.result.clone();
                let mut rebase = |projections: &mut [SnapshotProjection]| {
                    self.globalize_projections(result.owner, projections);
                };
                rebase(&mut value.projections);
                visit_callback_projections(&mut value.callbacks, &mut rebase);
                (id, value)
            });
        self.snapshot_providers.returns = named.chain(closures).chain(imported).collect();
    }

    fn describe_provider_result(
        &self,
        formals: &[Option<Span>],
        ty: &Ty,
        values: &[Datum],
        constructs: bool,
    ) -> ProviderResult {
        if !crate::access::check::higher_order::carries_callable(self.program, ty) {
            return ProviderResult::default();
        }
        ProviderResult {
            projections: self.snapshot_projections(formals, ty, &[], values),
            callbacks: values
                .iter()
                .flat_map(|value| self.callback_return_contracts(formals, value))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect(),
            constructs,
        }
    }

    pub(in crate::access::check::calls) fn replay_snapshot_provider_result(
        &mut self,
        provider: Span,
        entry: &CallEntry<'_>,
    ) -> Option<Datum> {
        let result = self
            .snapshot_providers
            .imported_results
            .get(&provider)?
            .clone();
        if !self.resolving_interface_results.insert(provider) {
            return None;
        }
        let value = self.exported_value(
            result.owner,
            &result.signature.formals,
            PublishedValue {
                sources: &[],
                callbacks: &result.result.callbacks,
                allocations: &[],
                projections: &result.result.projections,
                constructs: result.result.constructs,
            },
            self.ty(entry.span),
        );
        let value = self.instantiate_return(
            &result.signature.formals,
            &result.signature.via,
            entry,
            &value,
            &mut Vec::new(),
        );
        self.resolving_interface_results.remove(&provider);
        Some(value)
    }
    pub(super) fn publish_snapshot_projections(
        &self,
        function: &DefinitionCheck,
        summary: &mut Summary,
        references: &mut ProviderReferences,
    ) {
        if let Some(result) = self.snapshot_providers.returns.get(&function.owner) {
            summary.snapshot_returns.clone_from(&result.projections);
        }
        references.rebase_projections(&mut summary.snapshot_returns);

        for update in &mut summary.storage_updates {
            let Some(formal) = function.formals.get(update.formal).copied().flatten() else {
                continue;
            };
            let Some(parameter) = function.declared.parameters.get(update.formal) else {
                continue;
            };
            if let Some((_, source)) = function
                .updates
                .iter()
                .find(|(region, _)| region.source == formal && region.selection == update.path)
            {
                update.snapshot_projections = self.snapshot_projections(
                    &function.formals,
                    &parameter.ty,
                    &update.path,
                    std::slice::from_ref(&source.value),
                );
                references.rebase_projections(&mut update.snapshot_projections);
            }
        }
    }

    fn snapshot_projections(
        &self,
        formals: &[Option<Span>],
        ty: &Ty,
        prefix: &[Coordinate],
        values: &[Datum],
    ) -> Vec<SnapshotProjection> {
        let mut projections = BTreeSet::new();
        for value in values {
            value.visit_nodes(&mut Vec::new(), &mut |path, node| {
                let carries_callable = || {
                    let path = [prefix, path].concat();
                    carries_callable_at(self.program, ty, &path, &mut BTreeSet::new())
                };
                for origin in &node.roots {
                    let provider = known_provider(origin).and_then(|owner| {
                        self.snapshot_providers.sources.binary_search(&owner).ok()
                    });
                    let observation = origin.storage_read.as_ref().map(|read| StorageObservation {
                        index: read.index,
                        path: read.path.clone(),
                    });
                    let source = axis(formals, origin)
                        .filter(|_| observation.is_some() || carries_callable());
                    if provider.is_none()
                        && source.is_none()
                        && observation.is_none()
                        && !node.live_callable_state
                    {
                        continue;
                    }
                    projections.insert(SnapshotProjection {
                        path: path.to_vec(),
                        qualified: node.requires_new,
                        live_callable_state: node.live_callable_state,
                        allocation: origin.return_allocation.map(|identity| identity.index),
                        observation,
                        origin: SnapshotOrigin {
                            source,
                            provider,
                            access: origin.mode,
                            new: origin.new,
                            call_scoped: origin.call_scoped_access,
                            forwarded: origin.inherits_mode,
                            detached: origin.detached_snapshot,
                        },
                    });
                }
            });
        }
        projections.into_iter().collect()
    }

    pub(in crate::access::check::calls) fn restore_snapshot_projection(
        &self,
        owner: Span,
        formals: &[Option<Span>],
        node: &mut Datum,
        projection: &SnapshotProjection,
        preserve_unobserved: bool,
    ) {
        node.live_callable_state |= projection.live_callable_state;
        let origin = &projection.origin;
        let storage_read = projection.observation.as_ref().and_then(|read| {
            Some(StorageRead {
                index: self.imported_storage_observation(owner, read.index)?,
                path: read.path.clone(),
            })
        });
        let provider = origin.provider.and_then(|index| {
            self.snapshot_providers
                .imported
                .get(&owner)?
                .get(index)
                .copied()
        });
        if provider.is_some_and(|id| {
            self.snapshot_providers
                .imported_storage
                .get(&id)
                .is_some_and(|storage| !storage.slots.is_empty())
        }) {
            node.environments.insert(owner);
        }
        if let Some(allocation) = projection.allocation
            && let Some(root) = node.roots.iter_mut().find(|root| {
                root.return_allocation
                    .is_some_and(|identity| identity.index == allocation)
                    && (root.storage_read == storage_read
                        || !preserve_unobserved && root.storage_read.is_none())
            })
        {
            root.snapshot_provider = provider;
            root.detached_snapshot |= origin.detached;
            if storage_read.is_some() {
                root.storage_read = storage_read;
            }
            return;
        }
        let source = origin
            .source
            .as_ref()
            .and_then(|axis| formals.get(axis.parameter).copied().flatten());
        if let (Some(source), Some(axis)) = (source, &origin.source)
            && let Some(root) = node.roots.iter_mut().find(|root| {
                root.region.source == source
                    && root.region.selection == axis.path
                    && (root.storage_read == storage_read
                        || !preserve_unobserved && root.storage_read.is_none())
            })
        {
            if provider.is_some() {
                root.snapshot_provider = provider;
            }
            root.detached_snapshot |= origin.detached;
            if storage_read.is_some() {
                root.storage_read = storage_read;
            }
            return;
        }
        if source.is_none() && provider.is_none() && storage_read.is_none() {
            return;
        }
        let local = Span::new(owner.file, owner.start, owner.start);
        let mut value = Datum::source(source.unwrap_or(local), origin.access, origin.new);
        for root in &mut value.roots {
            root.snapshot_provider = provider;
            root.call_scoped_access = origin.call_scoped;
            root.inherits_mode = origin.forwarded;
            root.detached_snapshot = origin.detached;
            root.storage_read = storage_read.clone();
            if let Some(source) = &origin.source {
                root.region.selection.clone_from(&source.path);
            }
        }
        node.roots.extend(value.roots);
        node.roots.sort_unstable();
        node.roots.dedup();
        node.requires_new = (node.requires_new || projection.qualified)
            && node.roots.iter().all(|origin| origin.new);
    }
}

fn normalize_capture_sources(value: &mut Datum, owner: Span, formals: &[Option<Span>]) {
    let mut sources = BTreeSet::new();
    let mut definite = false;
    if value.roots.iter().all(|root| !root.detached_snapshot) {
        for (path, &exact) in &value.capture_paths {
            if path.owner == owner && formals.contains(&Some(path.region.source)) {
                definite |= exact;
                sources.extend(value.roots.iter().map(|root| {
                    let mut source = root.clone();
                    source.region = path.region.clone();
                    source.snapshot_provider = None;
                    source.callback_result = None;
                    source.return_allocation = None;
                    source
                }));
            }
        }
    }
    if definite && !sources.is_empty() {
        value.roots.clear();
        value.members.clear();
    }
    value.roots.extend(sources);
    for member in value.members.values_mut() {
        normalize_capture_sources(member, owner, formals);
    }
}

fn carries_callable_at(
    program: &TypedProgram,
    ty: &Ty,
    path: &[Coordinate],
    seen: &mut BTreeSet<(ril_frontend::hir::DefinitionId, usize)>,
) -> bool {
    let Some((member, rest)) = path.split_first() else {
        return crate::access::check::higher_order::carries_callable(program, ty);
    };
    match (ty, member) {
        (Ty::Adt(adt), _) => {
            let point = (adt.definition, path.len());
            if !seen.insert(point) {
                return false;
            }
            let result = program.nominal_layout(adt).map_or_else(
                || adt.kind != crate::ty::AdtKind::Foreign,
                |layout| carries_callable_at(program, &layout, path, seen),
            );
            seen.remove(&point);
            result
        }
        (Ty::Record(fields, open), Coordinate::Field(name)) => {
            fields.get(name).map_or(*open, |field| {
                carries_callable_at(program, &field.ty, rest, seen)
            })
        }
        (Ty::Tuple(fields), Coordinate::Index(index)) => index
            .parse::<usize>()
            .ok()
            .and_then(|index| fields.get(index))
            .is_some_and(|field| carries_callable_at(program, &field.ty, rest, seen)),
        (Ty::Map(key, _), Coordinate::MapKey) => carries_callable_at(program, key, rest, seen),
        (Ty::Array(item) | Ty::Map(_, item), _) => {
            carries_callable_at(program, &item.ty, rest, seen)
        }
        (Ty::Option(item) | Ty::Set(item), _) => carries_callable_at(program, item, rest, seen),
        (Ty::Result(ok, error), _) => {
            carries_callable_at(program, ok, rest, seen)
                || carries_callable_at(program, error, rest, seen)
        }
        (Ty::Param(_) | Ty::Infer(_) | Ty::Projection(..) | Ty::Unknown, _) => true,
        _ => false,
    }
}
