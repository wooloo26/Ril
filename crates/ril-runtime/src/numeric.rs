//! Locale-independent numeric conversion. Decimal floats are rounded directly
//! to their destination format, including conversions from arbitrary integers.
use crate::{
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};
use num_bigint::BigInt;
use num_traits::{FromPrimitive, ToPrimitive, Zero};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Error {
    OutOfRange,
}

fn integer_format(name: &str) -> Option<(u8, bool)> {
    Some(match name {
        "int" | "i64" => (64, true),
        "u64" => (64, false),
        "i32" => (32, true),
        "u32" => (32, false),
        "i16" => (16, true),
        "u16" => (16, false),
        "i8" => (8, true),
        "u8" => (8, false),
        _ => return None,
    })
}
impl Runtime {
    fn number_error(&mut self, error: Error) -> Result<Handle> {
        let tag = match error {
            Error::OutOfRange => "OutOfRange",
        };
        let error = self.variant(&format!("Num::NumError::{tag}"), vec![])?;
        self.variant("Err", vec![error])
    }
    fn integer_result(&mut self, value: BigInt, destination: &str) -> Result<Handle> {
        if destination == "bigint" {
            let value = self.allocate(Object::BigInteger(value))?;
            return self.variant("Ok", vec![value]);
        }
        let (bits, signed) = integer_format(destination)
            .ok_or_else(|| RuntimeError::internal("unknown numeric destination"))?;
        let Some(number) = value.to_i128() else {
            return self.number_error(Error::OutOfRange);
        };
        let (min, max) = if signed {
            (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
        } else {
            (0, (1i128 << bits) - 1)
        };
        if number < min || number > max {
            return self.number_error(Error::OutOfRange);
        }
        let value = self.integer(number, bits, signed)?;
        self.variant("Ok", vec![value])
    }
    pub fn numeric_convert(&mut self, source: Handle, destination: &str) -> Result<Handle> {
        let source = self.heap.get(source)?.clone();
        if matches!(destination, "f32" | "f64") {
            let bits = if destination == "f32" { 32 } else { 64 };
            let value = match source {
                Object::Integer { value, .. } => integer_float(&BigInt::from(value), bits),
                Object::BigInteger(value) => integer_float(&value, bits),
                Object::Float { value, .. } => {
                    let rounded = if bits == 32 {
                        f64::from(value as f32)
                    } else {
                        value
                    };
                    if value.is_finite() && rounded.is_infinite() {
                        Err(Error::OutOfRange)
                    } else {
                        Ok(rounded)
                    }
                }
                _ => return Err(RuntimeError::internal("numeric conversion of non-number")),
            };
            return match value {
                Ok(value) => {
                    let value = self.float(value, bits)?;
                    self.variant("Ok", vec![value])
                }
                Err(error) => self.number_error(error),
            };
        }
        let value = match source {
            Object::Integer { value, .. } => BigInt::from(value),
            Object::BigInteger(value) => value,
            Object::Float { value, .. } if value.is_finite() && value.fract().is_zero() => {
                BigInt::from_f64(value)
                    .ok_or_else(|| RuntimeError::internal("finite integral conversion failed"))?
            }
            Object::Float { .. } => return self.number_error(Error::OutOfRange),
            _ => return Err(RuntimeError::internal("numeric conversion of non-number")),
        };
        self.integer_result(value, destination)
    }
    pub(crate) fn numeric_primitive(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let conversion = name
            .strip_prefix("\0ril.numeric.convert_")
            .ok_or_else(|| RuntimeError::internal("unknown numeric primitive"))?;
        let (_, destination) = conversion
            .split_once("_to_")
            .ok_or_else(|| RuntimeError::internal("invalid numeric conversion contract"))?;
        let source = args
            .first()
            .copied()
            .ok_or_else(|| RuntimeError::internal("missing numeric conversion value"))?;
        self.numeric_convert(source, destination)
    }
}

fn integer_float(value: &BigInt, bits: u8) -> std::result::Result<f64, Error> {
    let rounded = if bits == 32 {
        value.to_f32().map(f64::from)
    } else {
        value.to_f64()
    };
    rounded
        .filter(|number| number.is_finite())
        .ok_or(Error::OutOfRange)
}
#[cfg(test)]
mod tests {
    use super::*;
    fn payload(runtime: &Runtime, handle: Handle, expected: &str) -> Handle {
        let Object::Variant { tag, fields } = runtime.heap.get(handle).unwrap() else {
            panic!("variant")
        };
        assert_eq!(tag, expected);
        fields[0]
    }
    #[test]
    fn numeric_conversions_round_once_and_check_integrality_and_overflow() {
        let mut rt = Runtime::default();
        let halfway = rt
            .allocate(Object::BigInteger(BigInt::from(16_777_217)))
            .unwrap();
        let result = rt.numeric_convert(halfway, "f32").unwrap();
        assert!(
            matches!(rt.heap.get(payload(&rt,result,"Ok")).unwrap(), Object::Float{value,bits:32} if *value==16_777_216.0)
        );
        let nonintegral = rt.float(1.5, 64).unwrap();
        let result = rt.numeric_convert(nonintegral, "int").unwrap();
        payload(&rt, result, "Err");
        let negative = rt.float(-0.0, 64).unwrap();
        let result = rt.numeric_convert(negative, "u8").unwrap();
        assert_eq!(rt.as_integer(payload(&rt, result, "Ok")).unwrap(), 0);
        let huge = rt.float(f64::MAX, 64).unwrap();
        let result = rt.numeric_convert(huge, "f32").unwrap();
        payload(&rt, result, "Err");
    }

    #[test]
    fn shift_counts_are_independent_integers_and_keep_the_left_representation() {
        use ril_runtime_api::abi::{BinaryOp, OutcomeTag};
        let mut runtime = Runtime::default();
        for (value, bits, signed, expected) in [(1, 8, false, 4), (-2, 16, true, -8)] {
            let left = runtime.integer(value, bits, signed).unwrap();
            for count in [
                runtime.integer(2, 32, true).unwrap(),
                runtime.integer(2, 64, false).unwrap(),
                runtime
                    .allocate(Object::BigInteger(BigInt::from(2)))
                    .unwrap(),
            ] {
                let shifted = runtime.binary(BinaryOp::ShiftLeft, left, count).unwrap();
                assert_eq!(
                    runtime.heap.get(shifted).unwrap(),
                    &Object::Integer {
                        value: expected,
                        bits,
                        signed
                    }
                );
            }
            let invalid = runtime
                .allocate(Object::BigInteger(BigInt::from(1u128 << 100)))
                .unwrap();
            assert_eq!(
                runtime
                    .binary(BinaryOp::ShiftRight, left, invalid)
                    .unwrap_err()
                    .tag,
                OutcomeTag::LanguagePanic
            );
        }
        let left = runtime
            .allocate(Object::BigInteger(BigInt::from(-8)))
            .unwrap();
        let count = runtime.integer(3, 8, false).unwrap();
        let shifted = runtime.binary(BinaryOp::ShiftRight, left, count).unwrap();
        assert_eq!(
            runtime.heap.get(shifted).unwrap(),
            &Object::BigInteger(BigInt::from(-1))
        );
        let count = runtime.integer(-1, 16, true).unwrap();
        assert_eq!(
            runtime
                .binary(BinaryOp::ShiftLeft, left, count)
                .unwrap_err()
                .tag,
            OutcomeTag::LanguagePanic
        );
    }
}
