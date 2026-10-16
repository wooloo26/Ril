//! A generic receiving position transports a callable's actual invocation
//! interface. A written callable annotation supplies a view. Neither operation
//! changes producer identities, tags, or inspection facts.
use super::*;
use generic_receiving::{Slot, child};

type Mask<'a> = Option<(&'a TypeExpr, &'a BTreeSet<String>)>;

fn marker(mask: Mask<'_>) -> bool {
    matches!(generic_receiving::transparent(mask), Some((TypeExpr { kind: TypeKind::Name { path, arguments }, .. }, markers))
        if path.len() == 1 && arguments.is_empty() && markers.contains(&path[0]))
}

impl Value {
    pub(super) fn contextual_type(self, ty: &Ty, span: Span) -> std::result::Result<Self, Problem> {
        // Selecting a literal's representation is not a source-written
        // callable ascription. Nested targets keep their actual defaults.
        self.receive_type_inner(ty, None, true, span, 0, &mut 0)
    }

    pub(super) fn receive_type(
        self,
        ty: &Ty,
        mask: Mask<'_>,
        span: Span,
    ) -> std::result::Result<Self, Problem> {
        self.receive_type_inner(ty, mask, false, span, 0, &mut 0)
    }

    fn receive_type_inner(
        mut self,
        ty: &Ty,
        mask: Mask<'_>,
        inherited: bool,
        span: Span,
        depth: usize,
        nodes: &mut usize,
    ) -> std::result::Result<Self, Problem> {
        *nodes += 1;
        if depth >= 64 || *nodes > 4096 {
            return Err(incomplete(
                span,
                "static receiving graph exceeds its finite allowance",
            ));
        }
        let preserve = inherited || marker(mask);
        if self.ty != *ty {
            self.source_type = None;
        }
        let mut receive = |value: Value, ty: &Ty, slot| {
            value.receive_type_inner(ty, child(mask, slot), preserve, span, depth + 1, nodes)
        };
        match (&mut self.shape, ty) {
            (Shape::Result { ok, error, .. }, Ty::Result(ok_ty, error_ty)) => {
                **ok = receive((**ok).clone(), ok_ty, Slot::Success)?;
                **error = receive((**error).clone(), error_ty, Slot::Error)?;
            }
            (Shape::Optional { payload, .. }, Ty::Optional(inner)) => {
                **payload = receive((**payload).clone(), inner, Slot::Optional)?;
            }
            (Shape::Tuple(items), Ty::Tuple(types)) => {
                for (index, (item, ty)) in items.iter_mut().zip(types).enumerate() {
                    *item = receive(item.clone(), ty, Slot::Tuple(index))?;
                }
            }
            (Shape::Array(items), Ty::Array(inner, _)) => {
                for item in items {
                    *item = receive(item.clone(), inner, Slot::Element)?;
                }
            }
            (Shape::Map(items), Ty::Map(key, value)) => {
                for (item_key, item_value) in items {
                    *item_key = receive(item_key.clone(), key, Slot::MapKey)?;
                    *item_value = receive(item_value.clone(), value, Slot::MapValue)?;
                }
            }
            (Shape::Record(fields) | Shape::BoundRecord { fields, .. }, Ty::Record(types)) => {
                for (name, value) in fields {
                    if let Some((_, ty)) = types.get(name) {
                        *value = receive(value.clone(), ty, Slot::Field(name))?;
                    }
                }
            }
            (Shape::Callable(target), Ty::Callable(_, output, interfaces))
                if !preserve && interfaces.len() == 1 =>
            {
                *target = Rc::new(Callable::View {
                    target: target.clone(),
                    parameters: interfaces[0].clone(),
                    output: output.clone(),
                });
            }
            (Shape::Integer(_), Ty::Number(name)) if matches!(name.as_str(), "f32" | "f64") => {
                // A contextual IEEE selection cannot retain the unrounded
                // integer as a proof of a subsequent branch condition.
                self.shape = Shape::Plain;
            }
            _ => {}
        }
        self.ty = ty.clone();
        Ok(self)
    }
}

/// Keep the complete source interface at actual generic leaves. The canonical
/// key must still agree with the selected type; value shape is never used to
/// invent fixed dimensions or callable modes.
pub(super) fn received_source(
    value: &Value,
    declared: Arc<crate::sema::model::SourceTypeWitness>,
    mask: Mask<'_>,
    span: Span,
) -> std::result::Result<Arc<crate::sema::model::SourceTypeWitness>, Problem> {
    fn overlay(
        value: &Value,
        syntax: &mut TypeExpr,
        mask: Mask<'_>,
        span: Span,
        depth: usize,
        nodes: &mut usize,
    ) -> std::result::Result<(), Problem> {
        *nodes += 1;
        if depth >= 64 || *nodes > 4096 {
            return Err(incomplete(
                span,
                "static receiving schema exceeds its finite allowance",
            ));
        }
        if marker(mask) {
            if let Some(actual) = &value.source_type
                && actual.key == normalized_argument_key(syntax)
            {
                *syntax = actual.syntax.clone();
            }
            return Ok(());
        }
        let mut visit = |value: &Value, syntax: &mut TypeExpr, slot| {
            overlay(value, syntax, child(mask, slot), span, depth + 1, nodes)
        };
        match (&value.shape, &mut syntax.kind) {
            (Shape::Tuple(values), TypeKind::Tuple(types)) => {
                for (index, (value, ty)) in values.iter().zip(types).enumerate() {
                    visit(value, ty, Slot::Tuple(index))?;
                }
            }
            (Shape::Array(values), TypeKind::Array { element, .. }) => {
                // Every element has the same selected type. Different callable
                // interfaces are retained by the values rather than guessed
                // from the first element for the container schema.
                if let Some(value) = values.first()
                    && values
                        .iter()
                        .all(|other| match (&other.source_type, &value.source_type) {
                            (Some(left), Some(right)) => left.syntax == right.syntax,
                            (None, None) => true,
                            _ => false,
                        })
                {
                    visit(value, element, Slot::Element)?;
                }
            }
            (
                Shape::Record(values) | Shape::BoundRecord { fields: values, .. },
                TypeKind::Record { fields, .. },
            ) => {
                for field in fields {
                    if let Some(value) = values.get(&field.name) {
                        visit(value, &mut field.ty, Slot::Field(&field.name))?;
                    }
                }
            }
            (Shape::Optional { payload, .. }, TypeKind::Optional(inner)) => {
                visit(payload, inner, Slot::Optional)?;
            }
            (Shape::Optional { payload, .. }, TypeKind::Name { path, arguments })
                if path.as_slice() == ["Option"] && arguments.len() == 1 =>
            {
                visit(payload, &mut arguments[0], Slot::Optional)?;
            }
            (Shape::Result { ok, error, .. }, TypeKind::Name { path, arguments })
                if path.as_slice() == ["Result"] && arguments.len() == 2 =>
            {
                visit(ok, &mut arguments[0], Slot::Success)?;
                visit(error, &mut arguments[1], Slot::Error)?;
            }
            _ => {}
        }
        Ok(())
    }
    let mut witness = (*declared).clone();
    overlay(value, &mut witness.syntax, mask, span, 0, &mut 0)?;
    if witness.key != normalized_argument_key(&witness.syntax) || !witness.validate_closed() {
        return Err(incomplete(
            span,
            "static receiving schema lost its selected type identity",
        ));
    }
    Ok(Arc::new(witness))
}
