use std::collections::BTreeSet;

use super::{
    Analyzer, CallEntry, Datum, Provider, ProviderReferences, Span, axis, known_provider,
    visit_callback_projections,
};
use crate::access::check::calls::imported::PublishedValue;
use crate::{
    access::{Coordinate, SnapshotOrigin, SnapshotProjection, Summary, check::DefinitionCheck},
    ty::{Ty, TypedProgram},
};

#[derive(Clone)]
pub(super) struct ImportedResult {
    pub(super) owner: Span,
    pub(super) signature: Provider,
    pub(super) result: ProviderResult,
}

#[derive(Clone, Default)]
pub(super) struct ProviderResult {
    pub(super) projections: Vec<SnapshotProjection>,
    pub(super) callbacks: Vec<crate::access::CallbackReturn>,
    pub(super) constructs: bool,
}

impl Analyzer<'_> {
    pub(in crate::access::check::calls) fn snapshot_argument_providers(
        &self,
        formals: &[Option<Span>],
        value: &Datum,
    ) -> Vec<SnapshotProjection> {
        self.snapshot_projections(formals, &Ty::Unknown, &[], std::slice::from_ref(value))
            .into_iter()
            .filter(|projection| projection.origin.provider.is_some())
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
                    for projection in projections {
                        projection.origin.provider = projection.origin.provider.and_then(|index| {
                            let owner = self
                                .snapshot_providers
                                .imported
                                .get(&result.owner)?
                                .get(index)?;
                            self.snapshot_providers.sources.binary_search(owner).ok()
                        });
                    }
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
                    let source = axis(formals, origin).filter(|_| carries_callable());
                    if provider.is_none() && source.is_none() {
                        continue;
                    }
                    projections.insert(SnapshotProjection {
                        path: path.to_vec(),
                        qualified: node.requires_new,
                        allocation: origin.return_allocation.map(|identity| identity.index),
                        origin: SnapshotOrigin {
                            source,
                            provider,
                            access: origin.mode,
                            new: origin.new,
                            borrowed: origin.call_borrow,
                            forwarded: origin.inherits_mode,
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
    ) {
        let origin = &projection.origin;
        let provider = origin.provider.and_then(|index| {
            self.snapshot_providers
                .imported
                .get(&owner)?
                .get(index)
                .copied()
        });
        if let Some(allocation) = projection.allocation
            && let Some(root) = node.roots.iter_mut().find(|root| {
                root.return_allocation
                    .is_some_and(|identity| identity.index == allocation)
            })
        {
            root.snapshot_provider = provider;
            return;
        }
        let source = origin
            .source
            .as_ref()
            .and_then(|axis| formals.get(axis.parameter).copied().flatten());
        if let (Some(source), Some(axis)) = (source, &origin.source)
            && let Some(root) = node
                .roots
                .iter_mut()
                .find(|root| root.region.source == source && root.region.selection == axis.path)
        {
            if provider.is_some() {
                root.snapshot_provider = provider;
            }
            return;
        }
        if source.is_none() && provider.is_none() {
            return;
        }
        let local = Span::new(owner.file, owner.start, owner.start);
        let mut value = Datum::source(source.unwrap_or(local), origin.access, origin.new);
        for root in &mut value.roots {
            root.snapshot_provider = provider;
            root.call_borrow = origin.borrowed;
            root.inherits_mode = origin.forwarded;
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
