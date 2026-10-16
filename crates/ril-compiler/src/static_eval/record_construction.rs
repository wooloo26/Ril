//! A newly allocated shell receives slot declarations independently of its
//! retained children's identities and permissions.
use super::*;

impl Evaluator {
    pub(super) fn receive_record_constructor(
        &self,
        mut value: StaticValue,
        expected: Option<&TypeExpr>,
        span: Span,
    ) -> Result<StaticValue> {
        let Some(TypeExpr {
            kind: TypeKind::Record { fields, .. },
            ..
        }) = expected
        else {
            return Ok(value);
        };
        let StaticValue::Record(record) = &mut value else {
            return Ok(value);
        };
        for field in fields {
            if record.storage.values.contains_key(&field.name) {
                if field.mutable {
                    record.mutable_fields.insert(field.name.clone());
                } else {
                    record.mutable_fields.remove(&field.name);
                }
            }
        }
        // The old witness described the constructor's default slot modes.
        // Re-derive its complete schema from the same immutable child handles.
        record.storage.source_type = None;
        self.infer_source_type(value, span)
    }
}
