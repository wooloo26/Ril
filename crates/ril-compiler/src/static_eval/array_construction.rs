//! A fresh array constructor can receive a written fixed representation. An
//! existing handle's current cardinality never changes its declared schema.
use super::*;
impl Evaluator {
    pub(super) fn receive_array_constructor(
        &self,
        value: StaticValue,
        expected: Option<&TypeExpr>,
    ) -> Result<StaticValue> {
        let Some(
            expected @ TypeExpr {
                kind: TypeKind::Array { length, .. },
                ..
            },
        ) = expected
        else {
            return Ok(value);
        };
        let StaticValue::Array(items) = &value else {
            return Ok(value);
        };
        let mut witness = self.source_type_witness(expected.clone())?;
        if witness.is_none()
            && let Some(actual) = source_types::view(&value)
            && let TypeKind::Array { element, .. } = &actual.syntax.kind
        {
            witness = self.source_type_witness(TypeExpr {
                hir_id: None,
                text: String::new(),
                span: expected.span,
                kind: TypeKind::Array {
                    element: element.clone(),
                    length: length.clone(),
                },
            })?;
        }
        let Some(witness) = witness else {
            return Ok(value);
        };
        if let TypeKind::Array {
            length: Some(length),
            ..
        } = &witness.syntax.kind
        {
            let ExprKind::Literal(Literal::Integer(text)) = &length.kind else {
                return Err(Failure::Unsupported(
                    "fixed static constructor length has no closed integer syntax".into(),
                ));
            };
            let selected = numeric_contexts::selected(
                text,
                false,
                false,
                Some(crate::numeric_literals::NumberType::Int),
                self.layout,
            )?;
            let StaticValue::Integer(length) = selected else {
                return Err(Failure::Unsupported(
                    "fixed static constructor length has no target int value".into(),
                ));
            };
            if usize::try_from(length).ok() != Some(items.len()) {
                return Err(Failure::Diagnostic(
                    "E0301",
                    "fresh static array does not have its declared fixed length".into(),
                ));
            }
        }
        self.receive_source_type(value, &witness.syntax)
    }
}
