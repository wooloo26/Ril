//! An exact finite map lookup transports the existing payload. Looking up a
//! key or observing presence cannot inspect, clone or discharge its Result.
use super::*;

impl Engine<'_> {
    pub(super) fn map_index(
        &mut self,
        map: &Value,
        index: &Value,
        span: Span,
    ) -> std::result::Result<Value, Problem> {
        let (Shape::Map(entries), Ty::Map(_, value_type)) = (&map.shape, &map.ty) else {
            return Err(incomplete(
                span,
                "static Result map lookup has no complete finite source",
            ));
        };
        let mut selected = None;
        for (key, value) in entries {
            self.step(span)?;
            match equal_values(key, index) {
                Some(true) => {
                    selected = Some(value.clone());
                    break;
                }
                Some(false) => {}
                None => {
                    return Err(incomplete(
                        span,
                        "static Result map lookup has no exact key-equality proof",
                    ));
                }
            }
        }
        // Map construction has already checked key uniqueness. A selected
        // value retains its own full source interface and producer identities;
        // the typed wrapper does not replace it with another member's graph.
        Ok(Value {
            source_type: None,
            ty: Ty::Optional(value_type.clone()),
            shape: Shape::Optional {
                tag: Some(selected.is_some()),
                choice: None,
                payload: Box::new(selected.unwrap_or_else(Value::unit)),
            },
        })
    }
}
