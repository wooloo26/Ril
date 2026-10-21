//! Declaration constraints provide a bounded structural view, never a new T.
use super::*;
use crate::sema::{
    model::rows::{OpenTail, Row, RowIdentity, RowTail},
    record_bounds::*,
};
mod dependencies;
mod rigid;
mod scoped_identity;
mod symbolic_members;

impl Checker {
    /// Only paths with actual product slots are admitted here. Collections,
    /// callable signatures and empty type-only positions need another proof.
    fn exact_record_bound_paths(ty: &Ty, binder: &str) -> Option<Vec<Vec<BoundTypeSelectionStep>>> {
        fn visit(
            ty: &Ty,
            binder: &str,
            path: &mut Vec<BoundTypeSelectionStep>,
            output: &mut Vec<Vec<BoundTypeSelectionStep>>,
            depth: usize,
            work: &mut usize,
        ) -> Option<()> {
            *work = work.checked_sub(1)?;
            if depth >= 64 {
                return None;
            }
            match ty {
                Ty::Generic(identity) if identity == binder => output.push(path.clone()),
                Ty::Tuple(items) => {
                    for (index, item) in items.iter().enumerate() {
                        path.push(BoundTypeSelectionStep::Tuple(u32::try_from(index).ok()?));
                        visit(item, binder, path, output, depth + 1, work)?;
                        path.pop();
                    }
                }
                Ty::Record(fields) | Ty::OpenRecord { fields, .. } => {
                    for (name, (_, item)) in fields {
                        path.push(BoundTypeSelectionStep::Field(name.clone()));
                        visit(item, binder, path, output, depth + 1, work)?;
                        path.pop();
                    }
                }
                _ => {}
            }
            Some(())
        }
        let mut output = Vec::new();
        visit(ty, binder, &mut Vec::new(), &mut output, 0, &mut 4096)?;
        Some(output)
    }

    fn selected_record_bound_value(
        &self,
        actual: &Value,
        path: &[BoundTypeSelectionStep],
    ) -> Option<Value> {
        let mut selected = actual.clone();
        for step in path {
            let slot = match step {
                BoundTypeSelectionStep::Tuple(index) => Slot::Tuple(*index),
                BoundTypeSelectionStep::Field(name) => Slot::Field(name.clone()),
                _ => return None,
            };
            // A branch join requires explicit correlation replay. Never join
            // here or allocate a replacement for a missing stored constituent.
            if selected.origins.nodes.len() != 1 {
                return None;
            }
            let origin = *selected.origins.nodes.first()?;
            selected = self.fields.get(&(origin, slot))?.clone();
        }
        Some(selected)
    }

    fn structural_schema_key(
        &self,
        schema: &StructuralSchema,
    ) -> Option<super::super::effect_identity::ArgumentKey> {
        use super::super::effect_identity::{ArgumentKey, StaticBinderSort};
        match &schema.source {
            StructuralSchemaSource::Closed(witness) => {
                crate::static_eval::effects::bounded_argument_key(&witness.syntax, &BTreeMap::new())
            }
            StructuralSchemaSource::CallerBound(id) => Some(ArgumentKey::Binder {
                identity: self.record_bounds.get(id.0 as usize)?.binder.clone(),
                sort: StaticBinderSort::Type,
            }),
            StructuralSchemaSource::RigidParameter { syntax, scope, .. } => {
                self.record_bound_key(syntax, scope)
            }
        }
    }

    pub(in crate::sema::checker) fn record_bound_scope(&self) -> BoundScope {
        BoundScope {
            types: self.type_source.environment.generic_context.clone(),
            rows: self.type_source.environment.bound_row_context.clone(),
        }
    }

    pub(in crate::sema::checker) fn record_bound_key(
        &self,
        syntax: &TypeExpr,
        scope: &BoundScope,
    ) -> Option<super::super::effect_identity::ArgumentKey> {
        let mut binders = scope.types.clone();
        for (name, id) in &scope.rows {
            let row = self.bound_rows.get(id.0 as usize)?;
            let RowIdentity::Binder(identity) = &row.identity else {
                return None;
            };
            if let Some(actual) = binders.get(name) {
                // A genuinely declared R keeps its own Type identity in field
                // positions. Its row-role identity is explicitly that same
                // binder, rather than a second unrelated symbolic type.
                if !matches!(&row.role, BoundRowRole::DeclaredTypeParameter { binder } if binder == actual && identity == binder)
                {
                    return None;
                }
            } else {
                binders.insert(name.clone(), identity.clone());
            }
        }
        crate::static_eval::effects::bounded_argument_key(syntax, &binders)
    }

    fn record_bound_field(
        &mut self,
        syntax: &TypeField,
        scope: &BoundScope,
    ) -> Option<RecordBoundField> {
        let normalized = self
            .source_type_from_syntax(&syntax.ty)
            .map(|witness| witness.syntax.clone())
            .unwrap_or_else(|| syntax.ty.clone());
        let key = self.record_bound_key(&normalized, scope)?;
        let ty = self.ty(&syntax.ty);
        if matches!(ty, Ty::StaticKey(_)) {
            self.error(
                "E0301",
                syntax.ty.span,
                "a static key is not an ordinary record field type",
                [],
            );
            return None;
        }
        if ty == Ty::Unknown {
            return None;
        }
        Some(RecordBoundField {
            label: syntax.name.clone(),
            mutable: syntax.mutable,
            ty,
            syntax: normalized,
            key,
        })
    }

    /// Called only after the genuine declared Type-binder context is installed.
    /// Implicit rows live in their own context; they never consume an argument
    /// index or impersonate the owning T's GenericBinder record.
    pub(super) fn declare_record_bounds(&mut self, function_id: usize) {
        let function = self.functions[function_id].syntax.clone();
        let definition = self.functions[function_id].definition;
        for (index, parameter) in function.generics.iter().enumerate() {
            let Some(TypeExpr {
                kind:
                    TypeKind::Record {
                        fields,
                        row: Some(row),
                    },
                ..
            }) = &parameter.bound
            else {
                continue;
            };
            let TypeKind::Name { path, arguments } = &row.kind else {
                continue;
            };
            if path.len() != 1 || !arguments.is_empty() {
                continue;
            }
            let name = &path[0];
            let declared = self
                .type_source
                .environment
                .generic_context
                .get(name)
                .cloned();
            if let Some(binder) = declared.as_ref() {
                let valid = self.generic_binders.get(binder).is_some_and(|binder| {
                    self.functions
                        .iter()
                        .find(|owner| owner.definition == binder.definition)
                        .and_then(|owner| owner.syntax.generics.get(binder.index as usize))
                        .is_some_and(|parameter| {
                            parameter.bound.as_ref().is_none_or(|bound| {
                                matches!(bound.kind, TypeKind::Record { .. })
                                    || matches!(&bound.kind, TypeKind::Name { path, arguments }
                                        if path == &["Type".to_owned()] && arguments.is_empty())
                            })
                        })
                });
                if !valid {
                    self.error(
                        "E0306",
                        row.span,
                        "a record row requires a Type parameter with a structural record role",
                        [],
                    );
                    continue;
                }
            }
            if declared
                .as_ref()
                .is_some_and(|id| self.generic_key_bounds.contains_key(id))
            {
                self.error(
                    "E0306",
                    row.span,
                    "a static key binder cannot serve as a record row",
                    [],
                );
                continue;
            }
            if declared.is_none() && self.types.contains_key(name) {
                continue;
            }
            let role_matches = |bound: &BoundRowDeclaration| match (&bound.role, &declared) {
                (BoundRowRole::DeclaredTypeParameter { binder }, Some(actual)) => binder == actual,
                (BoundRowRole::ImplicitResidual, None) => true,
                _ => false,
            };
            let existing = self.type_source.environment.bound_row_context.get(name).copied().filter(|id| {
                self.bound_rows.get(id.0 as usize).is_some_and(|bound| {
                    role_matches(bound)
                })
            }).or_else(|| {
                // The lexical declaration is stable across activations, even
                // after generic_scope has reinstalled only captured rows.
                self.bound_rows.iter().find(|bound| {
                    bound.definition == definition && &bound.name == name && role_matches(bound)
                        && bound.declaration_paths.iter().any(|path| {
                            path.path == [BoundPathStep::Bound, BoundPathStep::RowTail]
                                && function.generics.get(path.generic_index as usize)
                                    .and_then(|parameter| parameter.bound.as_ref())
                                    .is_some_and(|bound| matches!(&bound.kind,
                                        TypeKind::Record { row: Some(row), .. }
                                            if matches!(&row.kind, TypeKind::Name { path, arguments }
                                                if path == std::slice::from_ref(name) && arguments.is_empty())))
                        })
                }).map(|bound| bound.id)
            });
            let id = existing.unwrap_or_else(|| {
                let id = BoundRowId(self.bound_rows.len() as u32);
                let ordinal = self
                    .bound_rows
                    .iter()
                    .filter(|row| row.definition == definition)
                    .count() as u32;
                let role = declared
                    .as_ref()
                    .map_or(BoundRowRole::ImplicitResidual, |binder| {
                        BoundRowRole::DeclaredTypeParameter {
                            binder: binder.clone(),
                        }
                    });
                self.bound_rows.push(BoundRowDeclaration {
                    id,
                    definition,
                    ordinal,
                    name: name.clone(),
                    role,
                    declaration_paths: vec![],
                    identity: RowIdentity::Binder(declared.clone().unwrap_or_else(|| {
                        format!("function:{}:bound-row:{ordinal}", definition.0)
                    })),
                    lacks: BTreeSet::new(),
                    span: row.span,
                });
                self.type_source
                    .environment
                    .bound_row_context
                    .insert(name.clone(), id);
                id
            });
            self.type_source
                .environment
                .bound_row_context
                .insert(name.clone(), id);
            // An inner constraint does not add unconditional absences to a
            // captured outer row. Its own field labels remain local premises.
            if self.bound_rows[id.0 as usize].definition == definition {
                let row = &mut self.bound_rows[id.0 as usize];
                let owner_path = BoundDeclarationPath {
                    generic_index: index as u32,
                    path: vec![BoundPathStep::Bound, BoundPathStep::RowTail],
                };
                if !row.declaration_paths.contains(&owner_path) {
                    row.declaration_paths.push(owner_path);
                }
                row.lacks
                    .extend(fields.iter().map(|field| field.name.clone()));
            }
        }

        let substitutions = std::mem::take(&mut self.type_source.environment.generic_substitutions);
        let witnesses = std::mem::take(&mut self.type_source.environment.generic_type_witnesses);
        let scope = self.record_bound_scope();
        for (index, parameter) in function.generics.iter().enumerate() {
            let Some(
                syntax @ TypeExpr {
                    kind: TypeKind::Record { fields, row },
                    ..
                },
            ) = &parameter.bound
            else {
                continue;
            };
            let Some(binder) = self
                .type_source
                .environment
                .generic_context
                .get(&parameter.name)
                .cloned()
            else {
                continue;
            };
            if self.record_bounds_by_binder.contains_key(&binder) {
                continue;
            }
            let tail = match row {
                None => Some(DeclaredBoundTail::Closed),
                Some(row) => match &row.kind {
                    TypeKind::Name { path, arguments }
                        if path.len() == 1 && arguments.is_empty() =>
                    {
                        self.type_source
                            .environment
                            .bound_row_context
                            .get(&path[0])
                            .copied()
                            .map(DeclaredBoundTail::Row)
                            .or_else(|| {
                                self.record_bound_key(row, &scope).map(|key| {
                                    DeclaredBoundTail::Concrete {
                                        syntax: (**row).clone(),
                                        key,
                                    }
                                })
                            })
                    }
                    _ => {
                        self.record_bound_key(row, &scope)
                            .map(|key| DeclaredBoundTail::Concrete {
                                syntax: (**row).clone(),
                                key,
                            })
                    }
                },
            };
            let Some(tail) = tail else {
                self.unsupported(
                    syntax.span,
                    "record constraint tail needs complete scoped type evidence",
                );
                continue;
            };
            let mut labels = BTreeSet::new();
            let mut checked_fields = Vec::new();
            let mut complete = true;
            for field in fields {
                if !labels.insert(field.name.clone()) {
                    self.error(
                        "E0210",
                        field.span,
                        "record constraint field declared twice",
                        [],
                    );
                    complete = false;
                }
                match self.record_bound_field(field, &scope) {
                    Some(field) => checked_fields.push(field),
                    None => complete = false,
                }
            }
            if !complete {
                self.unsupported(
                    syntax.span,
                    "record constraint fields need complete scoped type evidence",
                );
                continue;
            }
            checked_fields.sort_by(|a, b| a.label.cmp(&b.label));
            let id = GenericBoundId(self.record_bounds.len() as u32);
            self.record_bounds.push(GenericRecordBound {
                id,
                definition,
                binder: binder.clone(),
                generic_index: index as u32,
                syntax: syntax.clone(),
                scope: scope.clone(),
                fields: checked_fields,
                tail,
                span: syntax.span,
            });
            self.record_bounds_by_binder.insert(binder, id);
        }
        self.type_source.environment.generic_substitutions = substitutions;
        self.type_source.environment.generic_type_witnesses = witnesses;
    }

    fn declared_record_bound(&self, ty: &Ty) -> Option<&GenericRecordBound> {
        let Ty::Generic(binder) = ty else { return None };
        self.record_bounds
            .get(self.record_bounds_by_binder.get(binder)?.0 as usize)
    }

    pub(super) fn record_bound_receiver_view(&self, ty: &Ty) -> Option<Ty> {
        let bound = self.declared_record_bound(ty)?;
        let fields = bound
            .fields
            .iter()
            .map(|field| (field.label.clone(), (field.mutable, field.ty.clone())))
            .collect();
        Some(match &bound.tail {
            DeclaredBoundTail::Closed => Ty::Record(fields),
            DeclaredBoundTail::Row(id) => {
                let row = self.bound_rows.get(id.0 as usize)?;
                let mut lacks = row.lacks.clone();
                lacks.extend(bound.fields.iter().map(|field| field.label.clone()));
                Ty::OpenRecord {
                    fields,
                    row: OpenTail {
                        identity: row.identity.clone(),
                        lacks,
                    },
                }
            }
            // Full concrete-tail expansion belongs to existing type-row rules;
            // unavailable proof is not a closed or empty residual.
            DeclaredBoundTail::Concrete { .. } => return None,
        })
    }

    pub(super) fn record_bound_formal_view(&self, ty: &Ty) -> Option<Ty> {
        self.record_bound_receiver_view(ty)
    }

    pub(super) fn bound_row_type(&self, name: &str) -> Option<Ty> {
        let id = self.type_source.environment.bound_row_context.get(name)?;
        if let Some(actual) = self.type_source.environment.bound_row_selections.get(id) {
            return Some(Self::row_type(actual.remainder.clone()));
        }
        let row = self.bound_rows.get(id.0 as usize)?;
        Some(Ty::OpenRecord {
            fields: BTreeMap::new(),
            row: OpenTail {
                identity: row.identity.clone(),
                lacks: row.lacks.clone(),
            },
        })
    }

    /// Formal-only reception. Actual calls use check_storage_shape instead;
    /// this declaration promise can never establish an actual object's length.
    pub(super) fn register_formal_record_schema(
        &mut self,
        function_id: usize,
        parameter_index: u32,
        value: &Value,
        frame: &mut Frame,
    ) {
        let info = self.functions[function_id].clone();
        self.promise_nested_bound_schemas(value, frame, info.syntax.span);
        let Some(syntax) = info
            .syntax
            .parameters
            .get(parameter_index as usize)
            .and_then(|parameter| parameter.ty.as_ref())
        else {
            return;
        };
        let rigid = self.nested_rigid_formal_schemas(
            info.definition,
            parameter_index,
            syntax,
            value,
            frame,
        );
        if rigid.is_empty() {
            self.rigid_record_parameters
                .remove(&(info.definition, parameter_index));
        } else {
            self.rigid_record_parameters
                .insert((info.definition, parameter_index), rigid);
        }
        let bound = self.declared_record_bound(&value.ty).cloned();
        let fields = if let Some(bound) = &bound {
            bound.fields.clone()
        } else if let TypeKind::Record { fields, .. } = &syntax.kind {
            let scope = self.record_bound_scope();
            let Some(fields) = fields
                .iter()
                .map(|field| self.record_bound_field(field, &scope))
                .collect::<Option<Vec<_>>>()
            else {
                return;
            };
            fields
        } else {
            return;
        };
        for field in &fields {
            for node in &value.origins.nodes {
                let slot = Slot::Field(field.label.clone());
                if let Some(mut child) = self.fields.get(&(*node, slot.clone())).cloned() {
                    self.ascribe_signature(&mut child, &field.syntax);
                    self.promise_array_shape(&child, &field.syntax, frame);
                    self.store_field(*node, slot, child);
                }
            }
        }
    }

    fn promise_nested_bound_schemas(&mut self, value: &Value, frame: &mut Frame, span: Span) {
        let mut pending = vec![(value.clone(), false, 0usize)];
        let mut seen = BTreeSet::new();
        let mut work = 4096usize;
        while let Some((parent, nested, depth)) = pending.pop() {
            if work == 0 || depth >= 64 {
                self.unsupported(
                    span,
                    "nested formal structural schema exceeds its finite path budget",
                );
                return;
            }
            work -= 1;
            let bound = self.declared_record_bound(&parent.ty).cloned();
            if nested && let Some(bound) = &bound {
                for field in &bound.fields {
                    for origin in &parent.origins.nodes {
                        let slot = Slot::Field(field.label.clone());
                        if let Some(mut child) = self.fields.get(&(*origin, slot.clone())).cloned()
                        {
                            self.ascribe_signature(&mut child, &field.syntax);
                            self.promise_array_shape(&child, &field.syntax, frame);
                            self.store_field(*origin, slot, child);
                        }
                    }
                }
            }
            if bound.is_some()
                || matches!(
                    parent.ty,
                    Ty::Tuple(_) | Ty::Record(_) | Ty::OpenRecord { .. }
                )
            {
                for origin in &parent.origins.nodes {
                    if seen.insert(*origin) {
                        let children: Vec<_> = self
                            .fields
                            .iter()
                            .filter(|((node, slot), _)| {
                                node == origin && matches!(slot, Slot::Tuple(_) | Slot::Field(_))
                            })
                            .map(|(_, child)| child.clone())
                            .collect();
                        pending.extend(children.into_iter().map(|child| (child, true, depth + 1)));
                    }
                }
            }
        }
    }

    /// No root is closed merely because all currently named fields are known.
    pub(super) fn structural_schema(
        &mut self,
        value: &Value,
        context: &super::super::effect_identity::InvocationContext,
        span: Span,
    ) -> Option<StructuralSchema> {
        let selected = self.call_inference_type(&value.ty);
        if let Some(bound) = self.declared_record_bound(&selected).cloned() {
            let view = self.record_bound_receiver_view(&selected)?;
            let tail = match view {
                Ty::OpenRecord { row, .. } => RowTail::Open(row),
                Ty::Record(_) => RowTail::Closed,
                _ => return None,
            };
            return Some(StructuralSchema {
                source: StructuralSchemaSource::CallerBound(bound.id),
                fields: bound.fields,
                tail,
            });
        }
        match self.collection_type(value) {
            Ty::Record(_) => {
                let syntax = self.source_composite_syntax(value, span)?;
                let TypeKind::Record { fields, row: None } = &syntax.kind else {
                    return None;
                };
                // Preserve the actual root's identity/qualification if present;
                // the separate structural field view does not replace its T.
                let witness = value
                    .source_type_witness
                    .clone()
                    .or_else(|| self.source_type_from_syntax(&syntax))?;
                let scope = self.record_bound_scope();
                let fields = fields
                    .iter()
                    .map(|field| self.record_bound_field(field, &scope))
                    .collect::<Option<_>>()?;
                Some(StructuralSchema {
                    source: StructuralSchemaSource::Closed(witness),
                    fields,
                    tail: RowTail::Closed,
                })
            }
            Ty::OpenRecord { fields, row } => {
                // A rigid parameter schema is a declaration fact, not a closed
                // SourceTypeWitness. Require this exact rigid tail and field
                // family, including complete array/callable child identities.
                let candidates: Vec<_> = self
                    .rigid_record_parameters
                    .values()
                    .flatten()
                    .filter(|schema| {
                        matches!(&schema.tail, RowTail::Open(tail) if tail.identity == row.identity)
                            && schema.fields.len() == fields.len()
                            && schema.fields.iter().all(|field| {
                                fields.get(&field.label) == Some(&(field.mutable, field.ty.clone()))
                            })
                    })
                    .cloned()
                    .collect();
                let mut selected: Option<StructuralSchema> = None;
                for candidate in candidates {
                    let symbolic_anchor = self.symbolic_schema_anchor(value, context, &candidate);
                    let candidate_scope = match &candidate.source {
                        StructuralSchemaSource::RigidParameter { scope, .. } => Some(scope),
                        _ => None,
                    };
                    let agrees = candidate.fields.iter().all(|field| {
                        value.origins.nodes.iter().all(|node| {
                            let Some(child) =
                                self.fields.get(&(*node, Slot::Field(field.label.clone())))
                            else {
                                return false;
                            };
                            child.source_type_witness.as_ref().is_some_and(|witness| {
                                crate::static_eval::effects::bounded_argument_key(
                                    &witness.syntax,
                                    &BTreeMap::new(),
                                )
                                .as_ref()
                                    == Some(&field.key)
                            }) || child.ty == field.ty
                                && (matches!(field.ty, Ty::Generic(_))
                                    || child.source_type_witness.is_none()
                                        && symbolic_anchor
                                        && candidate_scope.is_some_and(|scope| {
                                            symbolic_members::symbolic_member_candidate(
                                                &field.key, scope,
                                            )
                                        }))
                        })
                    });
                    if agrees {
                        if selected
                            .as_ref()
                            .is_some_and(|old| old.fields != candidate.fields)
                        {
                            return None;
                        }
                        selected = Some(candidate);
                    }
                }
                selected
            }
            _ => None,
        }
    }

    pub(super) fn record_bound_projection(
        &mut self,
        base: &Value,
        slot: &Slot,
        output: &Value,
        access: BoundAccess,
        frame: &Frame,
        span: Span,
    ) {
        let Some(bound) = self.declared_record_bound(&base.ty).cloned() else {
            return;
        };
        let Slot::Field(label) = slot else { return };
        if !bound.fields.iter().any(|field| &field.label == label) {
            return;
        }
        let context = self.invocation_context(frame.callable_owner);
        let check = self
            .generic_bound_checks
            .iter()
            .rev()
            .find(|check| check.required == bound.id && check.context == context)
            .map(|check| check.id);
        self.generic_bound_projections.push(GenericBoundProjection {
            required: bound.id,
            check,
            context,
            activation: frame.owner,
            allocation_epoch: self.recency_moves.len(),
            source: self.copy_value_snapshot(base),
            slot: slot.clone(),
            output: self.copy_value_snapshot(output),
            access,
            cause: output.cause,
            span,
        });
    }

    fn selected_record_bound_fields(
        &mut self,
        bound: &GenericRecordBound,
    ) -> Option<Vec<RecordBoundField>> {
        let previous = std::mem::replace(
            &mut self.type_source.environment.generic_context,
            bound.scope.types.clone(),
        );
        let previous_rows = std::mem::replace(
            &mut self.type_source.environment.bound_row_context,
            bound.scope.rows.clone(),
        );
        let result = bound
            .fields
            .iter()
            .map(|field| {
                let syntax = self
                    .instantiated_source_syntax(&field.syntax)
                    .unwrap_or_else(|| field.syntax.clone());
                let key = self.record_bound_key(&syntax, &bound.scope)?;
                let key = self.selected_bound_key(&key)?;
                Some(RecordBoundField {
                    label: field.label.clone(),
                    mutable: field.mutable,
                    ty: self.ty(&field.syntax),
                    syntax,
                    key,
                })
            })
            .collect();
        self.type_source.environment.generic_context = previous;
        self.type_source.environment.bound_row_context = previous_rows;
        result
    }

    pub(in crate::sema::checker) fn selected_bound_key(
        &self,
        key: &super::super::effect_identity::ArgumentKey,
    ) -> Option<super::super::effect_identity::ArgumentKey> {
        use crate::sema::{
            effect_identity::{ArgumentKey, StaticBinderSort},
            source_types::{SourceTypesError, WorkLimit, substitute_key_with},
        };
        use std::borrow::Cow;
        let environment = &self.type_source.environment;
        substitute_key_with(
            key,
            |identity, work| {
                if let Some(witness) = environment.generic_type_witnesses.get(identity) {
                    let key = crate::static_eval::effects::bounded_argument_key(
                        &witness.syntax,
                        &BTreeMap::new(),
                    )
                    .ok_or(SourceTypesError::Unresolved)?;
                    return Ok(Some(Cow::Owned(key)));
                }
                match environment.generic_substitutions.get(identity) {
                    Some(Ty::Generic(actual)) if actual != identity => {
                        work.charge(1 + actual.len().div_ceil(32))?;
                        Ok(Some(Cow::Owned(ArgumentKey::Binder {
                            identity: actual.clone(),
                            sort: StaticBinderSort::Type,
                        })))
                    }
                    Some(Ty::Generic(_)) | None => Ok(None),
                    // Runtime shape cannot supply missing source coordinates.
                    Some(_) => Err(SourceTypesError::Unresolved),
                }
            },
            &mut WorkLimit::new(16384),
        )
        .ok()
    }

    /// Exact products select existing values while retaining the whole actual
    /// snapshot. No fake T value is made for an empty collection or missing edge.
    pub(super) fn check_record_bound_application(
        &mut self,
        function_id: usize,
        args: &[(ParameterMode, Value, Span)],
        templates: &[Option<Ty>],
        context: super::super::effect_identity::InvocationContext,
        activation: ScopeId,
        span: Span,
    ) {
        let substitutions = self.type_source.environment.generic_substitutions.clone();
        let witnesses = self.type_source.environment.generic_type_witnesses.clone();
        let row_selections = self.type_source.environment.bound_row_selections.clone();
        let diagnostics = self.diagnostics.len();
        let unsupported = self.unsupported.len();
        let complete = self.check_record_bound_application_transaction(
            function_id,
            args,
            templates,
            context,
            activation,
            span,
        );
        if !complete
            || self.diagnostics.len() != diagnostics
            || self.unsupported.len() != unsupported
        {
            self.type_source.environment.generic_substitutions = substitutions;
            self.type_source.environment.generic_type_witnesses = witnesses;
            self.type_source.environment.bound_row_selections = row_selections;
        }
    }

    fn check_record_bound_application_transaction(
        &mut self,
        function_id: usize,
        args: &[(ParameterMode, Value, Span)],
        templates: &[Option<Ty>],
        context: super::super::effect_identity::InvocationContext,
        activation: ScopeId,
        span: Span,
    ) -> bool {
        use super::super::model::rows::Solver;
        let diagnostics = self.diagnostics.len();
        let unsupported = self.unsupported.len();
        let definition = self.functions[function_id].definition;
        let required: Vec<_> = self
            .record_bounds
            .iter()
            .filter(|bound| bound.definition == definition)
            .cloned()
            .collect();
        if required.is_empty() {
            return true;
        }
        let owned_rows: BTreeSet<_> = required
            .iter()
            .filter_map(|bound| match bound.tail {
                DeclaredBoundTail::Row(id) => Some(id),
                _ => None,
            })
            .filter(|id| {
                let row = &self.bound_rows[id.0 as usize];
                row.definition == definition
                    && match &row.role {
                        BoundRowRole::ImplicitResidual => true,
                        BoundRowRole::DeclaredTypeParameter { binder } => self
                            .generic_binders
                            .get(binder)
                            .is_some_and(|binder| binder.definition == definition),
                    }
            })
            .collect();
        let fresh: BTreeMap<_, _> = owned_rows
            .iter()
            .map(|id| {
                (
                    *id,
                    RowIdentity::Fresh {
                        owner: format!("record-bound:{context:?}"),
                        ordinal: u64::from(id.0),
                    },
                )
            })
            .collect();
        let mut solver = Solver::new("structural generic application", fresh.values().cloned());
        let mut staged = Vec::new();
        let mut selections = BTreeMap::new();
        for bound in required {
            let mut paths = Vec::new();
            for (index, template) in templates.iter().enumerate() {
                if let Some(template) = template {
                    let Some(selected) = Self::exact_record_bound_paths(template, &bound.binder)
                    else {
                        self.unsupported(
                            span,
                            "record-bound argument type path exceeds its finite budget",
                        );
                        return false;
                    };
                    paths.extend(selected.into_iter().map(|path| (index, path)));
                }
            }
            let Some((index, selection_path)) = paths.first().cloned() else {
                self.unsupported(
                    span,
                    "record-bound actual selection needs an explicit argument type path",
                );
                return false;
            };
            let Some((_, whole_actual, argument_span)) = args.get(index) else {
                self.unsupported(
                    span,
                    "record-bound application has no actual argument evidence",
                );
                return false;
            };
            let Some(actual) = self.selected_record_bound_value(whole_actual, &selection_path)
            else {
                self.unsupported(
                    *argument_span,
                    "nested record-bound selection needs its existing exact stored path",
                );
                return false;
            };
            let Some(schema) = self.structural_schema(&actual, &context, *argument_span) else {
                if matches!(
                    self.call_inference_type(&actual.ty),
                    Ty::Generic(_) | Ty::OpenRecord { .. } | Ty::Unknown
                ) {
                    self.unsupported(
                        *argument_span,
                        "record-bound implication requires the caller's structural schema",
                    );
                } else {
                    self.error(
                        "E0301",
                        *argument_span,
                        "generic argument does not satisfy the required record shape",
                        [actual.cause],
                    );
                }
                return false;
            };
            let Some(identity) = self.structural_schema_key(&schema) else {
                self.unsupported(
                    *argument_span,
                    "selected structural argument has no complete scoped identity",
                );
                return false;
            };
            for (other_index, other_path) in paths.iter().skip(1) {
                let Some((_, whole, at)) = args.get(*other_index) else {
                    self.unsupported(
                        span,
                        "another structural type occurrence has no actual argument",
                    );
                    return false;
                };
                let Some(other) = self.selected_record_bound_value(whole, other_path) else {
                    self.unsupported(
                        *at,
                        "another structural type occurrence has no exact stored path",
                    );
                    return false;
                };
                let other_identity = self
                    .structural_schema(&other, &context, *at)
                    .and_then(|schema| self.structural_schema_key(&schema));
                if other_identity.as_ref() != Some(&identity) {
                    if other_identity.as_ref().is_some_and(|key| {
                        identity.is_closed() && key.is_closed()
                            || symbolic_members::definite_member_conflict(&identity, key, 0)
                    }) {
                        self.error("E0301", *at, "one generic structural type selected different complete nested identities", [other.cause]);
                    } else {
                        self.unsupported(*at, "nested structural type occurrences need the same complete scoped identity");
                    }
                    return false;
                }
            }
            if !self.infer_bound_input_dependencies(function_id, &bound, &schema) {
                if bound.fields.iter().any(|field| {
                    schema.fields.iter().any(|actual| {
                        actual.label == field.label
                            && symbolic_members::definite_member_conflict(
                                &field.key,
                                &actual.key,
                                0,
                            )
                    })
                }) {
                    self.error(
                        "E0301",
                        *argument_span,
                        "bound input type equations disagree on complete member coordinates",
                        [actual.cause],
                    );
                } else {
                    self.unsupported(*argument_span,
                        "bound input dependency needs a complete scalar or genuine caller Type coordinate");
                }
                return false;
            }
            let Some(expected) = self.selected_record_bound_fields(&bound) else {
                self.unsupported(
                    bound.span,
                    "record-bound fields require scoped actual type evidence",
                );
                return false;
            };
            for field in &expected {
                let Some(actual_field) = schema
                    .fields
                    .iter()
                    .find(|actual| actual.label == field.label)
                else {
                    self.error(
                        "E0301",
                        *argument_span,
                        "generic argument lacks a guaranteed bound field",
                        [actual.cause],
                    );
                    return false;
                };
                if actual_field.mutable != field.mutable {
                    self.error(
                        "E0301",
                        *argument_span,
                        "generic argument does not satisfy a bound field",
                        [actual.cause],
                    );
                    return false;
                }
                if !self.compatible(&actual_field.ty, &field.ty) {
                    let mut symbolic = BTreeSet::new();
                    actual_field.ty.generic_names(&mut symbolic);
                    field.ty.generic_names(&mut symbolic);
                    if symbolic.is_empty() {
                        self.error(
                            "E0301",
                            *argument_span,
                            "generic argument does not satisfy a bound field type",
                            [actual.cause],
                        );
                    } else {
                        self.unsupported(*argument_span,
                            "record-bound field type implication requires its symbolic equality proof");
                    }
                    return false;
                }
                if actual_field.key != field.key {
                    if actual_field.key.is_closed() && field.key.is_closed()
                        || symbolic_members::definite_member_conflict(
                            &actual_field.key,
                            &field.key,
                            0,
                        )
                    {
                        self.error(
                            "E0301",
                            *argument_span,
                            "generic argument field has a different complete source type",
                            [actual.cause],
                        );
                    } else {
                        self.unsupported(*argument_span, "record-bound field identity implication needs complete dimensions and callable qualifications");
                    }
                    return false;
                }
            }
            if let RowTail::Open(tail) = &schema.tail {
                let mut lacks = tail.lacks.clone();
                if let Some(declared) = self.generic_row_lacks.get(&tail.identity) {
                    lacks.extend(declared.iter().cloned());
                }
                if solver.declare_rigid(tail.identity.clone(), lacks).is_err() {
                    self.unsupported(
                        *argument_span,
                        "record-bound caller row identity has conflicting roles",
                    );
                    return false;
                }
            }
            let residual = match &bound.tail {
                DeclaredBoundTail::Closed => None,
                DeclaredBoundTail::Row(id) => {
                    let row = &self.bound_rows[id.0 as usize];
                    let identity = fresh
                        .get(id)
                        .cloned()
                        .unwrap_or_else(|| row.identity.clone());
                    let mut lacks = row.lacks.clone();
                    lacks.extend(bound.fields.iter().map(|field| field.label.clone()));
                    if !owned_rows.contains(id)
                        && solver
                            .declare_rigid(identity.clone(), row.lacks.clone())
                            .is_err()
                    {
                        self.unsupported(bound.span, "captured record row has conflicting roles");
                        return false;
                    }
                    Some(OpenTail { identity, lacks })
                }
                DeclaredBoundTail::Concrete { .. } => {
                    self.unsupported(
                        bound.span,
                        "concrete record-bound tail requires its complete row equation",
                    );
                    return false;
                }
            };
            let required_fields: BTreeMap<_, _> = expected
                .iter()
                .map(|field| (field.label.clone(), (field.mutable, field.key.clone())))
                .collect();
            let actual_fields: BTreeMap<_, _> = schema
                .fields
                .iter()
                .map(|field| (field.label.clone(), (field.mutable, field.key.clone())))
                .collect();
            let fixed_selection = if let DeclaredBoundTail::Row(id) = &bound.tail {
                self.type_source
                    .environment
                    .bound_row_selections
                    .get(id)
                    .cloned()
                    .or_else(|| {
                        let BoundRowRole::DeclaredTypeParameter { binder } =
                            &self.bound_rows[id.0 as usize].role
                        else {
                            return None;
                        };
                        let witness = self
                            .type_source
                            .environment
                            .generic_type_witnesses
                            .get(binder)?
                            .clone();
                        let TypeKind::Record { fields, row: None } = &witness.syntax.kind else {
                            return None;
                        };
                        let scope = self.record_bound_scope();
                        let fields = fields
                            .iter()
                            .map(|field| self.record_bound_field(field, &scope))
                            .collect::<Option<Vec<_>>>()?;
                        Some(BoundRowSelection {
                            row: *id,
                            remainder: Row::closed(
                                fields
                                    .iter()
                                    .map(|field| {
                                        (field.label.clone(), (field.mutable, field.ty.clone()))
                                    })
                                    .collect(),
                            ),
                            fields,
                            source_type_witness: Some(witness),
                        })
                    })
            } else {
                None
            };
            if fixed_selection.is_none()
                && let DeclaredBoundTail::Row(id) = &bound.tail
                && let BoundRowRole::DeclaredTypeParameter { binder } =
                    &self.bound_rows[id.0 as usize].role
                && let Some(selected) = self
                    .type_source
                    .environment
                    .generic_substitutions
                    .get(binder)
            {
                if matches!(
                    self.call_inference_type(selected),
                    Ty::Record(_) | Ty::OpenRecord { .. } | Ty::Generic(_) | Ty::Unknown
                ) {
                    self.unsupported(
                        *argument_span,
                        "an already selected Type row requires its complete structural identity",
                    );
                } else {
                    self.error(
                        "E0301",
                        *argument_span,
                        "a record row argument must select a structural record type",
                        [actual.cause],
                    );
                }
                return false;
            }
            let equation = if let Some(selection) = &fixed_selection {
                let mut fields = required_fields.clone();
                let mut overlap = BTreeSet::new();
                for field in &selection.fields {
                    if fields
                        .insert(field.label.clone(), (field.mutable, field.key.clone()))
                        .is_some()
                    {
                        overlap.insert(field.label.clone());
                    }
                }
                if !overlap.is_empty() {
                    Err(super::super::model::rows::RowError::Overlap(overlap))
                } else {
                    if let RowTail::Open(tail) = &selection.remainder.tail
                        && solver
                            .declare_rigid(tail.identity.clone(), tail.lacks.clone())
                            .is_err()
                    {
                        self.unsupported(
                            *argument_span,
                            "selected record row has conflicting roles",
                        );
                        return false;
                    }
                    solver
                        .unify(
                            &Row {
                                fields,
                                tail: selection.remainder.tail.clone(),
                            },
                            &Row {
                                fields: actual_fields,
                                tail: schema.tail.clone(),
                            },
                        )
                        .map(|_| Row {
                            fields: selection
                                .fields
                                .iter()
                                .map(|field| {
                                    (field.label.clone(), (field.mutable, field.key.clone()))
                                })
                                .collect(),
                            tail: selection.remainder.tail.clone(),
                        })
                }
            } else {
                crate::sema::record_bound_shapes::entail(
                    &mut solver,
                    &required_fields,
                    residual.as_ref(),
                    &Row {
                        fields: actual_fields,
                        tail: schema.tail.clone(),
                    },
                )
            };
            let remainder = match equation {
                Ok(remainder) => remainder,
                Err(
                    super::super::model::rows::RowError::Overlap(_)
                    | super::super::model::rows::RowError::Lacks { .. },
                ) => {
                    self.error(
                        "E0212",
                        *argument_span,
                        "record-bound row overlaps a guaranteed field",
                        [actual.cause],
                    );
                    return false;
                }
                Err(
                    super::super::model::rows::RowError::UnprovedAbsence { .. }
                    | super::super::model::rows::RowError::Rigid(_)
                    | super::super::model::rows::RowError::Budget,
                ) => {
                    self.unsupported(
                        *argument_span,
                        "record-bound implication needs independently declared caller row absences",
                    );
                    return false;
                }
                Err(_) => {
                    self.error(
                        "E0301",
                        *argument_span,
                        "generic argument has inconsistent record row equations",
                        [actual.cause],
                    );
                    return false;
                }
            };
            let mut rows = Vec::new();
            if let DeclaredBoundTail::Row(id) = bound.tail {
                let fields: Vec<_> = schema
                    .fields
                    .iter()
                    .filter(|field| remainder.fields.contains_key(&field.label))
                    .cloned()
                    .collect();
                let row_ty = Row {
                    fields: fields
                        .iter()
                        .map(|field| (field.label.clone(), (field.mutable, field.ty.clone())))
                        .collect(),
                    tail: remainder.tail.clone(),
                };
                let witness = if matches!(row_ty.tail, RowTail::Closed)
                    && fields.iter().all(|field| field.key.is_closed())
                {
                    let syntax = TypeExpr {
                        hir_id: None,
                        text: String::new(),
                        span: *argument_span,
                        kind: TypeKind::Record {
                            fields: fields
                                .iter()
                                .map(|field| TypeField {
                                    name: field.label.clone(),
                                    mutable: field.mutable,
                                    ty: field.syntax.clone(),
                                    span: *argument_span,
                                })
                                .collect(),
                            row: None,
                        },
                    };
                    self.source_type_from_syntax(&syntax)
                } else {
                    None
                };
                let selection = BoundRowSelection {
                    row: id,
                    remainder: row_ty,
                    fields,
                    source_type_witness: witness,
                };
                selections.insert(id, selection.clone());
                rows.push(selection);
            }
            let mut substitutions = BTreeMap::new();
            for (binder, witness) in &self.type_source.environment.generic_type_witnesses {
                if let Some(key) = crate::static_eval::effects::bounded_argument_key(
                    &witness.syntax,
                    &BTreeMap::new(),
                ) {
                    substitutions.insert(binder.clone(), key);
                }
            }
            for (binder, selected) in &self.type_source.environment.generic_substitutions {
                if let Ty::Generic(actual) = selected {
                    substitutions.insert(
                        binder.clone(),
                        super::super::effect_identity::ArgumentKey::Binder {
                            identity: actual.clone(),
                            sort: super::super::effect_identity::StaticBinderSort::Type,
                        },
                    );
                }
            }
            if let Ty::Generic(binder) = self.call_inference_type(&actual.ty) {
                substitutions.insert(
                    bound.binder.clone(),
                    super::super::effect_identity::ArgumentKey::Binder {
                        identity: binder,
                        sort: super::super::effect_identity::StaticBinderSort::Type,
                    },
                );
            }
            let id = GenericBoundCheckId((self.generic_bound_checks.len() + staged.len()) as u32);
            staged.push(GenericBoundCheck {
                id,
                required: bound.id,
                context,
                activation,
                argument_index: index as u32,
                selection_path,
                allocation_epoch: self.recency_moves.len(),
                actual: self.copy_value_snapshot(whole_actual),
                actual_schema: schema,
                substitutions,
                rows,
                cause: actual.cause,
                span: *argument_span,
            });
        }
        if self.diagnostics.len() != diagnostics || self.unsupported.len() != unsupported {
            return false;
        }
        for (id, selection) in &selections {
            if owned_rows.contains(id)
                && let BoundRowRole::DeclaredTypeParameter { binder } =
                    &self.bound_rows[id.0 as usize].role
            {
                self.type_source
                    .environment
                    .generic_substitutions
                    .insert(binder.clone(), Self::row_type(selection.remainder.clone()));
                if let Some(witness) = &selection.source_type_witness {
                    self.type_source
                        .environment
                        .generic_type_witnesses
                        .insert(binder.clone(), witness.clone());
                }
            }
        }
        self.type_source
            .environment
            .bound_row_selections
            .extend(selections);
        self.generic_bound_checks.extend(staged);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lexical_row_ids_survive_cleared_active_and_recursive_entry_contexts() {
        let parsed = ril_syntax::parse(
            "fn both<T:{id:int,..R},U:{flag:bool,..R}>(left:T,right:U)->int{left.id}",
        );
        assert!(parsed.is_ok());
        let mut checker = Checker::new(FileId(0));
        let mut frame = checker.frame(BTreeMap::new(), false);
        checker.declarations(&parsed.program.statements, &mut frame);
        let mut lexical = None;
        for clear in [true, true, false, false, true] {
            if clear {
                checker.type_source.environment.bound_row_context.clear();
                checker.type_source.environment.bound_row_selections.clear();
            }
            checker.generic_scope(0);
            checker.declare_record_bounds(0);
            let current = checker.type_source.environment.bound_row_context["R"];
            assert_eq!(*lexical.get_or_insert(current), current);
            assert_eq!(checker.bound_rows.len(), 1);
            assert_eq!(checker.record_bounds.len(), 2);
            assert_eq!(checker.bound_rows[0].declaration_paths.len(), 2);
            assert!(checker.record_bounds.iter().all(|bound| {
                bound.scope.rows.get("R") == Some(&current)
                    && bound.tail == DeclaredBoundTail::Row(current)
            }));
        }
        assert!(checker.diagnostics.is_empty(), "{:?}", checker.diagnostics);
    }
}
