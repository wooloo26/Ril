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
    InvalidSyntax,
    OutOfRange,
    InvalidRadix,
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
fn radix(value: i128) -> std::result::Result<u32, Error> {
    u32::try_from(value)
        .ok()
        .filter(|n| (2..=36).contains(n))
        .ok_or(Error::InvalidRadix)
}
fn parse_integer(text: &str, base: u32) -> std::result::Result<BigInt, Error> {
    let (negative, digits) = if let Some(t) = text.strip_prefix('-') {
        (true, t)
    } else {
        (false, text.strip_prefix('+').unwrap_or(text))
    };
    if digits.is_empty()
        || !digits
            .bytes()
            .all(|c| c.is_ascii_alphanumeric() && (c as char).is_digit(base))
    {
        return Err(Error::InvalidSyntax);
    }
    let number = BigInt::parse_bytes(digits.as_bytes(), base).ok_or(Error::InvalidSyntax)?;
    Ok(if negative { -number } else { number })
}
fn decimal(text: &str) -> bool {
    let bytes = text.as_bytes();
    let mut i = usize::from(matches!(bytes.first(), Some(b'+' | b'-')));
    let before = i;
    while bytes.get(i).is_some_and(u8::is_ascii_digit) {
        i += 1;
    }
    let has_integer = i != before;
    if bytes.get(i) == Some(&b'.') {
        i += 1;
        let after = i;
        while bytes.get(i).is_some_and(u8::is_ascii_digit) {
            i += 1;
        }
        if after == i {
            return false;
        }
    } else if !has_integer {
        return false;
    }
    if matches!(bytes.get(i), Some(b'e' | b'E')) {
        i += 1;
        if matches!(bytes.get(i), Some(b'+' | b'-')) {
            i += 1;
        }
        let exponent = i;
        while bytes.get(i).is_some_and(u8::is_ascii_digit) {
            i += 1;
        }
        if exponent == i {
            return false;
        }
    }
    i == bytes.len()
}
fn parse_float(text: &str, bits: u8) -> std::result::Result<f64, Error> {
    match text {
        "nan" => return Ok(f64::NAN),
        "inf" | "+inf" => return Ok(f64::INFINITY),
        "-inf" => return Ok(f64::NEG_INFINITY),
        _ => {}
    }
    if !decimal(text) {
        return Err(Error::InvalidSyntax);
    }
    let value = if bits == 32 {
        f64::from(text.parse::<f32>().map_err(|_| Error::InvalidSyntax)?)
    } else {
        text.parse::<f64>().map_err(|_| Error::InvalidSyntax)?
    };
    if value.is_infinite() {
        Err(Error::OutOfRange)
    } else {
        Ok(value)
    }
}

impl Runtime {
    fn number_error(&mut self, error: Error) -> Result<Handle> {
        let tag = match error {
            Error::InvalidSyntax => "InvalidSyntax",
            Error::OutOfRange => "OutOfRange",
            Error::InvalidRadix => "InvalidRadix",
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
                Object::Integer { value, .. } => parse_float(&value.to_string(), bits),
                Object::BigInteger(value) => parse_float(&value.to_str_radix(10), bits),
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
    pub(crate) fn numeric_builtin(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let arg = |index: usize| {
            args.get(index)
                .copied()
                .ok_or_else(|| RuntimeError::internal("missing numeric argument"))
        };
        let operation = name
            .strip_prefix("Num::")
            .ok_or_else(|| RuntimeError::internal("unknown numeric namespace"))?;
        if let Some(types) = operation.strip_prefix("__convert_") {
            let destination = if let Some((source, destination)) = types.split_once("_to_") {
                if integer_format(source).is_none() && !matches!(source, "bigint" | "f32" | "f64") {
                    return Err(RuntimeError::internal("unknown conversion source type"));
                }
                destination
            } else {
                types
            };
            return self.numeric_convert(arg(0)?, destination);
        }
        if let Some(destination) = operation.strip_prefix("parse_") {
            if matches!(destination, "f32" | "f64") {
                let bits = if destination == "f32" { 32 } else { 64 };
                return match parse_float(self.as_string(arg(0)?)?, bits) {
                    Ok(value) => {
                        let value = self.float(value, bits)?;
                        self.variant("Ok", vec![value])
                    }
                    Err(error) => self.number_error(error),
                };
            }
            let base = match radix(
                args.get(1)
                    .map(|&h| self.as_integer(h))
                    .transpose()?
                    .unwrap_or(10),
            ) {
                Ok(base) => base,
                Err(error) => return self.number_error(error),
            };
            return match parse_integer(self.as_string(arg(0)?)?, base) {
                Ok(value) => self.integer_result(value, destination),
                Err(error) => self.number_error(error),
            };
        }
        if let Some(source_type) = operation.strip_prefix("format_") {
            if matches!(source_type, "f32" | "f64") {
                let Object::Float { value, bits } = self.heap.get(arg(0)?)? else {
                    return Err(RuntimeError::internal("expected float"));
                };
                let text = crate::formatting::default_float(*value, *bits);
                return self.string(text);
            }
            let base = match radix(
                args.get(1)
                    .map(|&h| self.as_integer(h))
                    .transpose()?
                    .unwrap_or(10),
            ) {
                Ok(base) => base,
                Err(error) => return self.number_error(error),
            };
            let text = match self.heap.get(arg(0)?)? {
                Object::Integer { value, .. } => BigInt::from(*value).to_str_radix(base),
                Object::BigInteger(value) => value.to_str_radix(base),
                _ => return Err(RuntimeError::internal("expected integer")),
            };
            let text = self.string(text)?;
            return self.variant("Ok", vec![text]);
        }
        Err(RuntimeError::internal("unknown numeric operation"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn call(runtime: &mut Runtime, name: &str, args: &[Handle]) -> Handle {
        runtime.numeric_builtin(name, args).unwrap()
    }
    fn payload(runtime: &Runtime, handle: Handle, expected: &str) -> Handle {
        let Object::Variant { tag, fields } = runtime.heap.get(handle).unwrap() else {
            panic!("variant")
        };
        assert_eq!(tag, expected);
        fields[0]
    }
    #[test]
    fn integer_parsing_validates_radix_before_syntax_and_respects_signedness() {
        let mut rt = Runtime::default();
        let bad = rt.string(" _".into()).unwrap();
        let base = rt.int(1).unwrap();
        let result = call(&mut rt, "Num::parse_int", &[bad, base]);
        let error = payload(&rt, result, "Err");
        assert!(
            matches!(rt.heap.get(error).unwrap(),Object::Variant{tag,..} if tag=="Num::NumError::InvalidRadix")
        );
        for (text, tag) in [
            ("-0", "Ok"),
            ("+255", "Ok"),
            ("256", "Err"),
            ("-1", "Err"),
            ("0xff", "Err"),
            ("1_0", "Err"),
            (" 1", "Err"),
        ] {
            let input = rt.string(text.into()).unwrap();
            let result = call(&mut rt, "Num::parse_u8", &[input]);
            payload(&rt, result, tag);
        }
        let input = rt.string("18446744073709551616".into()).unwrap();
        let result = call(&mut rt, "Num::parse_bigint", &[input]);
        assert_eq!(
            rt.heap.get(payload(&rt, result, "Ok")).unwrap(),
            &Object::BigInteger(BigInt::from(1u128 << 64))
        );
    }
    #[test]
    fn float_syntax_rounding_overflow_and_conversions_are_explicit() {
        let mut rt = Runtime::default();
        for (text, tag) in [
            (".5", "Ok"),
            ("-1.25e-2", "Ok"),
            ("nan", "Ok"),
            ("+inf", "Ok"),
            ("1.", "Err"),
            ("NaN", "Err"),
            ("1e", "Err"),
            ("1e999", "Err"),
        ] {
            let input = rt.string(text.into()).unwrap();
            let result = call(&mut rt, "Num::parse_f32", &[input]);
            payload(&rt, result, tag);
        }
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
