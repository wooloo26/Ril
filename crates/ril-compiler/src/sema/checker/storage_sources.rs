//! Immutable declaration views and physical receipts for storage reception.
//! The current value of a mutable binding is never its declaration schema.
use super::*;
use crate::sema::{
    effect_identity::ArgumentKey,
    source_reception,
    storage_sources::{BindingSource, StorageDestination, StorageObservation, StorageWrite},
};

#[derive(Default)]
pub(super) struct State {
    bindings: Vec<BindingSource>,
    writes: Vec<StorageWrite>,
    by_binding: BTreeMap<BindingId, usize>,
    types: crate::sema::source_types::LiveSourceTypes,
}

impl State {
    pub(super) fn into_parts(
        self,
    ) -> (
        Vec<BindingSource>,
        Vec<StorageWrite>,
        crate::sema::source_types::SourceTypeIndex,
    ) {
        (self.bindings, self.writes, self.types.freeze())
    }
}

pub(super) struct PreparedBindingSource {
    context: crate::sema::effect_identity::InvocationContext,
    activation: ScopeId,
    root: Option<ArgumentKey>,
    environment: crate::sema::context::FrozenEnvironment,
}

pub(super) struct StoreReception<'a> {
    pub target: &'a Expr,
    pub operator: &'a str,
    pub rhs_syntax: &'a Expr,
    pub rhs: StorageObservation,
    pub destination: StorageDestination,
    pub receiver: Option<&'a Value>,
}

impl Checker {
    /// Static constraint lookup only. This projects the immutable declaration
    /// view, never the binding's current value, heap contents or numeric data.
    pub(super) fn declared_operand_source(
        &mut self,
        syntax: &Expr,
        frame: &Frame,
    ) -> Option<ArgumentKey> {
        let mut path = Vec::new();
        let name = source_path(syntax, &mut path, &mut 4096)?;
        let id = *frame.env.get(name)?;
        if let Ok(key) = self.type_source.storage.types.projected_binding_key(
            id,
            &path,
            Some(&self.semantic_hir),
        ) {
            return Some(key);
        }
        let mut key = self.declared_formal_source(id, name)?;
        for slot in path {
            key = self.storage_projection_source_key(&key, &slot)?;
        }
        Some(key)
    }
    pub(super) fn prepare_storage_binding_source(
        &mut self,
        binding: &Binding,
        target: Option<&source_reception::Target>,
        initializer: StorageObservation,
        frame: &Frame,
    ) -> PreparedBindingSource {
        let context = self.invocation_context(frame.callable_owner);
        let environment = target
            .map(|target| target.environment.clone())
            .unwrap_or_else(|| self.capture_typing_environment_with_bindings(&frame.env));
        let original = self
            .application_effect
            .expressions
            .get(initializer.expression)
            .cloned();
        let root = if let Some(target) = target {
            target.key()
        } else {
            original.as_ref().and_then(|original| {
                self.original_source_receiving_key(&original.value, &binding.value, frame)
            })
        };
        PreparedBindingSource {
            context,
            activation: frame.owner,
            root,
            environment,
        }
    }

    pub(super) fn record_storage_binding_sources(
        &mut self,
        binding: &Binding,
        prepared: &PreparedBindingSource,
        initializer: StorageObservation,
        start: usize,
        frame: &Frame,
    ) {
        let context = prepared.context;
        let root = &prepared.root;
        let Some(declaration) = binding.pattern.hir_id else {
            self.unsupported(
                binding.pattern.span,
                "storage declaration has no original PatternId",
            );
            return;
        };
        if prepared.activation != frame.owner
            || context != self.invocation_context(frame.callable_owner)
        {
            self.unsupported(
                binding.pattern.span,
                "storage declaration changed its original elaboration context",
            );
            return;
        }
        let mut names = Vec::new();
        let _ = pattern_paths(
            &binding.pattern,
            &mut Vec::new(),
            true,
            &mut names,
            &mut 4096,
        );
        for id in start..self.bindings.len() {
            let actual = &self.bindings[id];
            if actual.parameter || actual.owner != frame.owner {
                continue;
            }
            self.bindings[id].pattern = Some(declaration);
            self.bindings[id].typing_environment = prepared.environment.clone();
            let actual = &self.bindings[id];
            let candidates: Vec<_> = names
                .iter()
                .filter(|(span, name, _, _)| *span == actual.span && *name == actual.name)
                .collect();
            let [(_, _, path, known)] = candidates.as_slice() else {
                // A real introduced binding remains an unknown declaration,
                // including guarded/rest patterns not represented by Slots.
                self.type_source
                    .storage
                    .by_binding
                    .insert(id, self.type_source.storage.bindings.len());
                self.type_source.storage.bindings.push(BindingSource {
                    binding: id,
                    context,
                    activation: frame.owner,
                    declaration,
                    declared: binding.ty.is_some(),
                    initializer,
                    path: Vec::new(),
                    key: None,
                });
                if self
                    .type_source
                    .storage
                    .types
                    .record(id, None, prepared.environment.clone())
                    .is_err()
                {
                    self.unsupported(
                        binding.pattern.span,
                        "storage source index could not record the original unknown view",
                    );
                }
                continue;
            };
            let key = if *known {
                root.as_ref().and_then(|root| {
                    crate::sema::source_types::declarations::project(
                        root,
                        path,
                        &self.semantic_hir,
                        &mut crate::sema::source_types::WorkLimit::new(4096),
                    )
                    .ok()
                })
            } else {
                None
            };
            self.type_source
                .storage
                .by_binding
                .insert(id, self.type_source.storage.bindings.len());
            if self
                .type_source
                .storage
                .types
                .record(id, key.as_ref(), prepared.environment.clone())
                .is_err()
            {
                self.unsupported(
                    binding.pattern.span,
                    "storage source graph admission exceeded its metadata budget",
                );
            }
            self.type_source.storage.bindings.push(BindingSource {
                binding: id,
                context,
                activation: frame.owner,
                declaration,
                declared: binding.ty.is_some(),
                initializer,
                path: path.clone(),
                key,
            });
        }
    }

    /// The outer option distinguishes absence of a ledger entry from an entry
    /// whose schema is unknown. The latter must not fall back to a current RHS.
    pub(super) fn storage_binding_source_key(
        &self,
        value: &Value,
        syntax: &Expr,
        _frame: &Frame,
    ) -> Option<Option<ArgumentKey>> {
        let mut path = Vec::new();
        let name = source_path(syntax, &mut path, &mut 4096)?;
        if value.sources.len() != 1 {
            return None;
        }
        let id = *value.sources.first()?;
        self.type_source
            .storage
            .bindings
            .get(*self.type_source.storage.by_binding.get(&id)?)?;
        if value.sources != BTreeSet::from([id])
            || self
                .bindings
                .get(id)
                .is_none_or(|binding| binding.name != name)
        {
            return Some(None);
        }
        Some(
            self.type_source
                .storage
                .types
                .projected_binding_key(id, &path, Some(&self.semantic_hir))
                .ok(),
        )
    }

    pub(super) fn check_storage_write_source(
        &mut self,
        reception: StoreReception<'_>,
        replacement: &mut Value,
        frame: &Frame,
    ) -> bool {
        let StoreReception {
            target,
            operator,
            rhs_syntax,
            rhs,
            destination,
            receiver,
        } = reception;
        let Some(target_id) = target.hir_id else {
            self.unsupported(target.span, "storage write has no original target ExprId");
            return false;
        };
        let expected = match &destination {
            StorageDestination::Binding(binding) => self
                .type_source
                .storage
                .types
                .projected_binding_key(*binding, &[], Some(&self.semantic_hir))
                .ok(),
            StorageDestination::Projection { slot, .. } => {
                let syntax = match &target.kind {
                    ExprKind::Field { base, .. } | ExprKind::Index { base, .. } => {
                        Some(base.as_ref())
                    }
                    _ => None,
                };
                receiver
                    .zip(syntax)
                    .and_then(|(value, syntax)| {
                        self.original_source_receiving_key(value, syntax, frame)
                    })
                    .and_then(|key| self.storage_projection_source_key(&key, slot))
            }
        };
        let context = self.invocation_context(frame.callable_owner);
        self.type_source.storage.writes.push(StorageWrite {
            target: target_id,
            context,
            activation: frame.owner,
            span: target.span,
            operator: operator.into(),
            rhs,
            destination,
            expected: expected.clone(),
            completed: true,
        });
        let observation = self
            .application_effect
            .expressions
            .get(rhs.expression)
            .cloned();
        let actual = observation.as_ref().and_then(|original| {
            self.original_source_receiving_key(&original.value, rhs_syntax, frame)
        });
        let fresh = source_reception::construction(rhs_syntax, &mut 4096);
        let answer = expected.as_ref().and_then(|expected| {
            if crate::sema::source_types::key_is_coordinate_free_with_declarations(
                expected,
                Some(&self.semantic_hir),
            ) {
                return Some(true);
            }
            // Arithmetic compound assignment is checked separately and cannot
            // create a collection/Fn Source from its numeric RHS.
            if operator != "=" {
                return Some(false);
            }
            compatible(expected, actual.as_ref(), fresh.as_ref())
        });
        match answer {
            Some(true) => {
                // Replace only the type view. Permission, publication, causes,
                // origins and all actual write obligations remain unchanged.
                replacement.source_type_witness = expected
                    .as_ref()
                    .and_then(|key| {
                        super::call_input_source::storage_closed_source_syntax(key, target.span)
                    })
                    .and_then(|syntax| self.source_type_from_frozen_syntax(&syntax));
                true
            }
            Some(false) => {
                self.error("E0301", target.span,
                    "stored input source does not fit the destination's original declaration schema",
                    [replacement.cause]);
                false
            }
            None => {
                self.unsupported(target.span,
                    "storage reception requires its original declaration and complete input source coordinates");
                false
            }
        }
    }

    /// A structural bound guarantees the Source of a named member, not a
    /// complete Source for its open parent. Select the declared member before
    /// substituting its leaves; unrelated row members remain unresolved.
    fn storage_projection_source_key(
        &self,
        source: &ArgumentKey,
        slot: &Slot,
    ) -> Option<ArgumentKey> {
        let (
            ArgumentKey::Binder {
                identity,
                sort: crate::sema::effect_identity::StaticBinderSort::Type,
            },
            Slot::Field(label),
        ) = (source, slot)
        else {
            return crate::sema::source_types::declarations::project(
                source,
                std::slice::from_ref(slot),
                &self.semantic_hir,
                &mut crate::sema::source_types::WorkLimit::new(4096),
            )
            .ok();
        };
        let binder = self.generic_binders.get(identity)?;
        let declaration = self
            .functions
            .iter()
            .find(|function| function.definition == binder.definition)?;
        let parameter = declaration.syntax.generics.get(binder.index as usize)?;
        if !crate::sema::record_bounds::certifies_type_sort(
            identity,
            binder,
            parameter,
            &self.record_bounds,
        ) {
            return None;
        }
        let bound = self
            .record_bounds
            .get(self.record_bounds_by_binder.get(identity)?.0 as usize)?;
        if bound.binder != *identity
            || bound.definition != binder.definition
            || bound.generic_index != binder.index
        {
            return None;
        }
        let fields: Vec<_> = bound
            .fields
            .iter()
            .filter(|field| field.label == *label)
            .collect();
        let [field] = fields.as_slice() else {
            return None;
        };
        self.selected_bound_key(&field.key)
    }

    pub(super) fn record_aborted_storage_write(
        &mut self,
        target: &Expr,
        operator: &str,
        rhs: StorageObservation,
        destination: StorageDestination,
        frame: &Frame,
    ) {
        let Some(target_id) = target.hir_id else {
            self.unsupported(
                target.span,
                "aborted storage write has no original target ExprId",
            );
            return;
        };
        self.type_source.storage.writes.push(StorageWrite {
            target: target_id,
            context: self.invocation_context(frame.callable_owner),
            activation: frame.owner,
            span: target.span,
            operator: operator.into(),
            rhs,
            destination,
            expected: None,
            completed: false,
        });
    }
}

fn compatible(
    expected: &ArgumentKey,
    actual: Option<&ArgumentKey>,
    fresh: Option<&source_reception::Construction>,
) -> Option<bool> {
    // A type-coordinate relation does not prove retained callable bounds.
    // Until frozen lexical row/latent certificates are attached to stores,
    // every callable coordinate (also nested) remains an obligation.
    if has_callable(expected, &mut 4096)? {
        return None;
    }
    if let Some(actual) = actual {
        return source_reception::compatible(expected, actual, fresh, &mut 4096);
    }
    match (expected, fresh) {
        (
            ArgumentKey::Array { length, element },
            Some(source_reception::Construction::Array(items)),
        ) if items.is_empty() => {
            source_reception::complete(element, &mut 4096)?;
            Some(
                length
                    .as_ref()
                    .is_none_or(|length| length == "const(int:0)"),
            )
        }
        _ => None,
    }
}

pub(in crate::sema::checker) fn has_callable(key: &ArgumentKey, work: &mut usize) -> Option<bool> {
    *work = work.checked_sub(1)?;
    let children: Vec<&ArgumentKey> = match key {
        ArgumentKey::Callable { .. } | ArgumentKey::GenericBuiltin(_) => return Some(true),
        ArgumentKey::Array { element, .. } => vec![element],
        ArgumentKey::Map { key, value } => vec![key, value],
        ArgumentKey::Name { arguments, .. } | ArgumentKey::Tuple(arguments) => {
            arguments.iter().collect()
        }
        ArgumentKey::Record { fields, row } => fields
            .iter()
            .map(|field| &field.2)
            .chain(row.iter().map(|row| row.as_ref()))
            .collect(),
        ArgumentKey::Closed(_) => return None,
        ArgumentKey::Binder { .. } => vec![],
    };
    for child in children {
        if has_callable(child, work)? {
            return Some(true);
        }
    }
    Some(false)
}

fn source_path<'a>(syntax: &'a Expr, path: &mut Vec<Slot>, work: &mut usize) -> Option<&'a str> {
    *work = work.checked_sub(1)?;
    match &syntax.kind {
        ExprKind::Name(name) => Some(name),
        ExprKind::Field { base, field, .. } => {
            let name = source_path(base, path, work)?;
            path.push(
                field
                    .parse()
                    .map(Slot::Tuple)
                    .unwrap_or_else(|_| Slot::Field(field.clone())),
            );
            Some(name)
        }
        ExprKind::Index { base, .. } => {
            let name = source_path(base, path, work)?;
            path.push(Slot::AnyIndex);
            Some(name)
        }
        _ => None,
    }
}

fn pattern_paths(
    pattern: &Pattern,
    path: &mut Vec<Slot>,
    known: bool,
    out: &mut Vec<(Span, String, Vec<Slot>, bool)>,
    work: &mut usize,
) -> Option<()> {
    *work = work.checked_sub(1)?;
    match &pattern.kind {
        PatternKind::Name(name) => out.push((pattern.span, name.clone(), path.clone(), known)),
        PatternKind::Mode { pattern, .. } => {
            pattern_paths(pattern, path, known, out, work)?;
        }
        PatternKind::Tuple(items) => {
            for (index, item) in items.iter().enumerate() {
                path.push(Slot::Tuple(index as u32));
                pattern_paths(item, path, known, out, work)?;
                path.pop();
            }
        }
        PatternKind::Record {
            fields,
            rest_binding,
            ..
        } => {
            for field in fields {
                path.push(Slot::Field(field.name.clone()));
                pattern_paths(&field.pattern, path, known, out, work)?;
                path.pop();
            }
            if let Some(name) = rest_binding {
                out.push((pattern.span, name.clone(), Vec::new(), false));
            }
        }
        PatternKind::Constructor { arguments, .. } | PatternKind::Alternative(arguments) => {
            for argument in arguments {
                pattern_paths(argument, &mut Vec::new(), false, out, work)?;
            }
        }
        PatternKind::Type {
            binder: Some(name), ..
        } => out.push((pattern.span, name.clone(), Vec::new(), false)),
        _ => {}
    }
    Some(())
}
