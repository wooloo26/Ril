//! Existing nested rigid formal reception; no replacement objects are made.
use super::*;

impl Checker {
    /// A declaration can promise types and fixed storage only for its existing
    /// formal values. This walk does not allocate a replacement constituent.
    pub(super) fn nested_rigid_formal_schemas(
        &mut self,
        definition: DefinitionId,
        parameter_index: u32,
        syntax: &TypeExpr,
        value: &Value,
        frame: &mut Frame,
    ) -> Vec<StructuralSchema> {
        let scope = self.record_bound_scope();
        let scope_cost = scope
            .types
            .iter()
            .fold(0usize, |cost, (name, identity)| {
                cost.saturating_add(name.len())
                    .saturating_add(identity.len())
                    .saturating_add(128)
            })
            .saturating_add(scope.rows.keys().fold(0usize, |cost, name| {
                cost.saturating_add(name.len()).saturating_add(64)
            }));
        let mut retained = 0usize;
        let mut pending = vec![(syntax, value.clone(), 0usize)];
        let mut output = Vec::new();
        let mut work = 4096usize;
        while let Some((syntax, value, depth)) = pending.pop() {
            if depth >= 64 || work == 0 {
                self.unsupported(
                    syntax.span,
                    "rigid formal product schema exceeds its finite declaration budget",
                );
                return Vec::new();
            }
            work -= 1;
            match &syntax.kind {
                TypeKind::Tuple(items) => {
                    let Ty::Tuple(types) = self.collection_type(&value) else {
                        continue;
                    };
                    if types.len() != items.len() {
                        continue;
                    }
                    for (index, child) in items.iter().enumerate() {
                        let Ok(index) = u32::try_from(index) else {
                            continue;
                        };
                        if let Some(stored) = self.selected_record_bound_value(
                            &value,
                            &[BoundTypeSelectionStep::Tuple(index)],
                        ) {
                            pending.push((child, stored, depth + 1));
                        }
                    }
                }
                TypeKind::Record { fields, row } => {
                    let receiver = self.collection_type(&value);
                    let (known, tail) = match receiver {
                        Ty::Record(fields) => (fields, None),
                        Ty::OpenRecord { fields, row } => (fields, Some(row)),
                        _ => continue,
                    };
                    if value.origins.nodes.len() != 1 {
                        continue;
                    }
                    let Some(mut declared) = fields
                        .iter()
                        .map(|field| self.record_bound_field(field, &scope))
                        .collect::<Option<Vec<_>>>()
                    else {
                        continue;
                    };
                    // Match the same transparent semantic aliases that the
                    // actual collection view expands. Complete dimensions,
                    // callable modes and qualifications remain in field.key.
                    for field in &mut declared {
                        field.ty = self.call_inference_type(&field.ty);
                    }
                    if !declared.iter().all(|field| {
                        known.get(&field.label) == Some(&(field.mutable, field.ty.clone()))
                    }) {
                        continue;
                    }
                    // Promise only the children that already occur in this
                    // formal product. No actual invocation uses this method.
                    for field in &declared {
                        for origin in &value.origins.nodes {
                            let slot = Slot::Field(field.label.clone());
                            if let Some(mut child) =
                                self.fields.get(&(*origin, slot.clone())).cloned()
                            {
                                self.ascribe_signature(&mut child, &field.syntax);
                                self.promise_array_shape(&child, &field.syntax, frame);
                                self.store_field(*origin, slot, child);
                            }
                        }
                    }
                    if known.len() == fields.len()
                        && let (Some(row_syntax), Some(tail)) = (row, tail)
                        && let Some(super::super::super::effect_identity::ArgumentKey::Binder {
                            identity,
                            ..
                        }) = self.record_bound_key(row_syntax, &scope)
                        && tail.identity == RowIdentity::Binder(identity)
                    {
                        retained = retained
                            .saturating_add(scope_cost)
                            .saturating_add(syntax.text.len().saturating_mul(256));
                        if output.len() >= 256 || retained > 16 * 1024 * 1024 {
                            self.unsupported(
                                syntax.span,
                                "rigid formal schema retention exceeds its finite metadata budget",
                            );
                            return Vec::new();
                        }
                        output.push(StructuralSchema {
                            source: StructuralSchemaSource::RigidParameter {
                                definition,
                                parameter_index,
                                syntax: syntax.clone(),
                                scope: scope.clone(),
                            },
                            fields: declared,
                            tail: RowTail::Open(tail),
                        });
                    }
                    for child in fields {
                        if let Some(stored) = self.selected_record_bound_value(
                            &value,
                            &[BoundTypeSelectionStep::Field(child.name.clone())],
                        ) {
                            pending.push((&child.ty, stored, depth + 1));
                        }
                    }
                }
                // Type-only positions, aliases, collections and opaque rows
                // have no exact product path in this reception contract.
                _ => {}
            }
        }
        output
    }
}
