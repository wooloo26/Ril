use super::*;

fn cursor_type() -> Ty {
    Ty::Record(
        [
            ("data".into(), (false, Ty::Bytes)),
            ("offset".into(), (true, integer("int"))),
        ]
        .into(),
    )
}
fn binary_signature(name: &str) -> Option<(Vec<Ty>, bool, Output)> {
    let operation = name.strip_prefix("Binary::")?;
    let error = Ty::Named("Binary::BinaryError".into());
    let order = Ty::Named("Binary::ByteOrder".into());
    Some(match operation {
        "cursor" => (vec![Ty::Bytes], false, Output::Value(cursor_type())),
        "remaining" => (vec![cursor_type()], false, Output::Value(integer("int"))),
        "read_bytes" => (
            vec![cursor_type(), integer("int")],
            true,
            Output::Result(Ty::Bytes, error),
        ),
        "read_uleb128" => (
            vec![cursor_type()],
            true,
            Output::Result(integer("u64"), error),
        ),
        "write_bytes" => (
            vec![Ty::Array(Box::new(integer("u8"))), Ty::Bytes],
            true,
            Output::Value(Ty::Unit),
        ),
        "write_uleb128" => (
            vec![Ty::Array(Box::new(integer("u8"))), integer("u64")],
            true,
            Output::Value(Ty::Unit),
        ),
        _ => {
            if let Some(suffix) = operation.strip_prefix("read_") {
                let ty = numeric(suffix)?;
                if matches!(suffix, "int" | "bigint") {
                    return None;
                }
                let mut parameters = vec![cursor_type()];
                if !matches!(suffix, "u8" | "i8") {
                    parameters.push(order);
                }
                (parameters, true, Output::Result(ty, error))
            } else {
                let suffix = operation.strip_prefix("write_")?;
                let ty = numeric(suffix)?;
                if matches!(suffix, "int" | "bigint") {
                    return None;
                }
                let mut parameters = vec![Ty::Array(Box::new(integer("u8"))), ty];
                if !matches!(suffix, "u8" | "i8") {
                    parameters.push(order);
                }
                (parameters, true, Output::Value(Ty::Unit))
            }
        }
    })
}
pub(super) fn is_binary_builtin(name: &str) -> bool {
    binary_signature(name).is_some()
}

impl Checker {
    pub(super) fn standard_binary_builtin(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        let (parameters, writes, output) = binary_signature(name)?;
        if args.len() != parameters.len() {
            self.error("E0314", span, "binary operation argument count differs", []);
        }
        for (index, ((mode, value, argument_span), expected)) in
            args.iter().zip(parameters).enumerate()
        {
            let expected_mode = if index == 0 && writes {
                ParameterMode::Mut
            } else {
                ParameterMode::Read
            };
            if *mode != expected_mode {
                self.error(
                    "E0405",
                    *argument_span,
                    "binary operation argument mode differs",
                    [value.cause],
                );
            }
            self.require_type(value, &expected, *argument_span);
            if unknown_type(&value.ty) {
                self.unsupported(*argument_span, "binary argument type remains unresolved");
            }
            if index == 0 && writes {
                if value.permission != Permission::Write {
                    self.error(
                        "E0520",
                        *argument_span,
                        "binary receiver is read-only",
                        [value.cause],
                    );
                }
                if name.starts_with("Binary::write_") {
                    self.standard_binary_output_write(value, *argument_span, frame);
                } else {
                    self.access(
                        value,
                        Some(Slot::Field("offset".into())),
                        Mode::Write,
                        *argument_span,
                        frame,
                    );
                    self.access(
                        value,
                        Some(Slot::Field("data".into())),
                        Mode::Read,
                        *argument_span,
                        frame,
                    );
                }
            } else if !value.ty.scalar() {
                self.access(value, None, Mode::Read, *argument_span, frame);
            }
        }
        Some(match output {
            Output::Value(ty) => self.standard_value(ty, span, frame.owner, 0),
            Output::Result(ok, error) => self.standard_result(ok, error, span, frame.owner),
            _ => unreachable!(),
        })
    }
    fn standard_binary_output_write(&mut self, value: &Value, span: Span, frame: &mut Frame) {
        for active in &self.active_iterations {
            if !self.origins_disjoint(active, &value.origins) {
                self.error(
                    "E0526",
                    span,
                    "binary append invalidates active output traversal",
                    [value.cause],
                );
                break;
            }
        }
        self.access(value, None, Mode::Write, span, frame);
        let child = Value::scalar(integer("u8"), None, value.cause);
        for node in &value.origins.nodes {
            self.store_field(*node, Slot::AnyIndex, child.clone());
        }
    }
}
