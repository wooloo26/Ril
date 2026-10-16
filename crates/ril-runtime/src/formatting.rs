//! Heap adapter for the phase-independent Ril scalar formatting rules.
use crate::{
    heap::Object,
    value::{Result, RuntimeError},
};
pub use ril_text_format::default_float;
use ril_text_format::{FormatSpec, Scalar};

pub fn format(value: &Object, specification: &str) -> Result<String> {
    let scalar = match value {
        Object::Integer { value, .. } => Scalar::Integer { value: *value },
        Object::BigInteger(value) => Scalar::BigInteger(value),
        Object::Float { value, bits } => Scalar::Float {
            value: *value,
            bits: *bits,
        },
        Object::String(value) => Scalar::String(value),
        Object::Bool(value) => Scalar::Bool(*value),
        _ => {
            return Err(RuntimeError::internal(
                "value does not support text formatting",
            ));
        }
    };
    FormatSpec::parse(specification, 64)
        .and_then(|spec| spec.render(scalar, usize::MAX))
        .map_err(|error| match error {
            ril_text_format::Error::LimitExceeded => RuntimeError::panic(error.to_string()),
            _ => RuntimeError::internal(error.to_string()),
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn float_defaults_use_ril_notation_and_preserve_signed_zero() {
        assert_eq!(default_float(1.2f32 as f64, 32), "1.2");
        assert_eq!(default_float(1e-6, 64), "0.000001");
        assert_eq!(default_float(1e-7, 64), "1e-7");
        assert_eq!(default_float(1e20, 64), "100000000000000000000.0");
        assert_eq!(default_float(1e21, 64), "1e21");
        assert_eq!(default_float(-0.0, 64), "-0.0");
    }
    #[test]
    fn formatting_counts_scalars_and_rounds_ties_to_even() {
        assert_eq!(
            format(
                &Object::Integer {
                    value: -42,
                    bits: 64,
                    signed: true
                },
                "05"
            )
            .unwrap(),
            "-0042"
        );
        assert_eq!(
            format(
                &Object::Float {
                    value: 1.25,
                    bits: 64
                },
                ".1f"
            )
            .unwrap(),
            "1.2"
        );
        assert_eq!(
            format(&Object::String("é🙂x".into()), ".2s").unwrap(),
            "é🙂"
        );
        assert_eq!(format(&Object::String("x".into()), "^4").unwrap(), " x  ");
    }
}
