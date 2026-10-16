use super::*;
use ril_text_format::{FormatSpec, Scalar};

pub(super) fn failure(error: ril_text_format::Error) -> Failure {
    match error {
        ril_text_format::Error::Malformed => Failure::Diagnostic("E0112", error.to_string()),
        ril_text_format::Error::Incompatible => Failure::Diagnostic("E0329", error.to_string()),
        ril_text_format::Error::LimitExceeded => Failure::Unsupported(error.to_string()),
    }
}
impl Evaluator {
    pub(super) fn format_static(&self, value: &StaticValue, text: &str) -> Result<String> {
        let scalar = match value {
            StaticValue::Integer(value) | StaticValue::TypedInteger(value, ..) => {
                Scalar::Integer { value: *value }
            }
            StaticValue::BigInteger(value) => Scalar::BigInteger(value),
            StaticValue::Float(value, narrow) => Scalar::Float {
                value: *value,
                bits: if *narrow { 32 } else { 64 },
            },
            StaticValue::String(value) => Scalar::String(value),
            StaticValue::Bool(value) => Scalar::Bool(*value),
            _ => return Err(failure(ril_text_format::Error::Incompatible)),
        };
        // Resource exhaustion is not evidence that a Ril format is malformed.
        const MAX_STATIC_TEXT_BYTES: usize = 1_048_576;
        FormatSpec::parse(text, self.layout.pointer_bits)
            .and_then(|spec| spec.render(scalar, MAX_STATIC_TEXT_BYTES))
            .map_err(failure)
    }
}
