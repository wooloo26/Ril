//! Pure exact literal parsing and representation selection.
//!
//! These values grant no semantic authority. Callers must solve their own type
//! constraints before selection; this module does not modify checker gates,
//! invocation witnesses, static budgets, or the runtime ABI.
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, ToPrimitive, Zero};
use ril_compiler_core::target::TargetLayout;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumberType {
    Int,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    BigInt,
    F32,
    F64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FloatFormat {
    F32,
    F64,
}

impl FloatFormat {
    fn precision(self) -> u32 {
        match self {
            Self::F32 => 24,
            Self::F64 => 53,
        }
    }
    fn max_exponent(self) -> u64 {
        match self {
            Self::F32 => 127,
            Self::F64 => 1023,
        }
    }
    fn sign_bit(self) -> u64 {
        match self {
            Self::F32 => 1 << 31,
            Self::F64 => 1 << 63,
        }
    }
    fn infinity(self) -> u64 {
        match self {
            Self::F32 => 0x7f80_0000,
            Self::F64 => 0x7ff0_0000_0000_0000,
        }
    }
}

/// Upper bits are zero for f32. Widening an already selected f32 into Core's
/// f64 carrier is exact and performs no second rounding decision.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryFloat {
    format: FloatFormat,
    bits: u64,
}

impl BinaryFloat {
    pub fn format(self) -> FloatFormat {
        self.format
    }
    pub fn bits(self) -> u64 {
        self.bits
    }
    pub fn as_f64(self) -> f64 {
        match self.format {
            FloatFormat::F32 => f64::from(f32::from_bits(self.bits as u32)),
            FloatFormat::F64 => f64::from_bits(self.bits),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EncodedNumber {
    Integer {
        value: i128,
        ty: NumberType,
        bits: u8,
        signed: bool,
    },
    BigInteger(BigInt),
    Float(BinaryFloat),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    InvalidSyntax,
    ResourceLimit,
    IncompatibleSelection,
    OutOfRange,
    UnsupportedTarget,
    UnsupportedDecimal,
}

/// An implementation input bound, deliberately unrelated to any source-level
/// static or runtime allowance. The caller must choose it explicitly.
#[derive(Debug, Clone, Copy)]
pub struct ParseLimit {
    pub max_bytes: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ExactValue {
    Integer(BigUint),
    Decimal(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExactLiteral {
    value: ExactValue,
    suffix: Option<NumberType>,
    negative: bool,
}

const INTEGER_SUFFIXES: &[(&str, NumberType)] = &[
    ("bigint", NumberType::BigInt),
    ("int", NumberType::Int),
    ("i64", NumberType::I64),
    ("u64", NumberType::U64),
    ("i32", NumberType::I32),
    ("u32", NumberType::U32),
    ("i16", NumberType::I16),
    ("u16", NumberType::U16),
    ("i8", NumberType::I8),
    ("u8", NumberType::U8),
];

fn without_suffix<'a>(
    text: &'a str,
    suffixes: &[(&str, NumberType)],
) -> (&'a str, Option<NumberType>) {
    for &(suffix, ty) in suffixes {
        if let Some(body) = text.strip_suffix(suffix) {
            return (body.strip_suffix('_').unwrap_or(body), Some(ty));
        }
    }
    (text, None)
}

fn digit(byte: u8, radix: u32) -> bool {
    let value = match byte {
        b'0'..=b'9' => u32::from(byte - b'0'),
        b'a'..=b'f' => u32::from(byte - b'a') + 10,
        b'A'..=b'F' => u32::from(byte - b'A') + 10,
        _ => return false,
    };
    value < radix
}

fn digits(text: &str, radix: u32) -> bool {
    let mut preceding_digit = false;
    for byte in text.bytes() {
        if digit(byte, radix) {
            preceding_digit = true;
        } else if byte == b'_' && preceding_digit {
            preceding_digit = false;
        } else {
            return false;
        }
    }
    preceding_digit
}

impl ExactLiteral {
    /// `negative` denotes an immediately applied source minus; it is not part
    /// of the unsigned token spelling. It remains observable for float zero.
    pub fn integer(text: &str, negative: bool, limit: ParseLimit) -> Result<Self, Error> {
        if text.len() > limit.max_bytes {
            return Err(Error::ResourceLimit);
        }
        let (body, suffix) = without_suffix(text, INTEGER_SUFFIXES);
        let (radix, body) =
            if let Some(body) = body.strip_prefix("0x").or_else(|| body.strip_prefix("0X")) {
                (16, body)
            } else if let Some(body) = body.strip_prefix("0o").or_else(|| body.strip_prefix("0O")) {
                (8, body)
            } else if let Some(body) = body.strip_prefix("0b").or_else(|| body.strip_prefix("0B")) {
                (2, body)
            } else {
                (10, body)
            };
        if !digits(body, radix) {
            return Err(Error::InvalidSyntax);
        }
        let magnitude = BigUint::parse_bytes(body.replace('_', "").as_bytes(), radix)
            .ok_or(Error::InvalidSyntax)?;
        Ok(Self {
            value: ExactValue::Integer(magnitude),
            suffix,
            negative,
        })
    }

    /// Preserve decimal text until a float format is selected. In particular,
    /// parsing this value does not round it through an intermediate f64.
    pub fn decimal(text: &str, negative: bool, limit: ParseLimit) -> Result<Self, Error> {
        if text.len() > limit.max_bytes {
            return Err(Error::ResourceLimit);
        }
        let (body, suffix) =
            without_suffix(text, &[("f32", NumberType::F32), ("f64", NumberType::F64)]);
        let (mantissa, exponent) = body.find(['e', 'E']).map_or((body, None), |index| {
            (&body[..index], Some(&body[index + 1..]))
        });
        let Some((whole, fraction)) = mantissa.split_once('.') else {
            return Err(Error::InvalidSyntax);
        };
        if !digits(whole, 10)
            || !digits(fraction, 10)
            || exponent.is_some_and(|exponent| {
                let exponent = exponent.strip_prefix(['+', '-']).unwrap_or(exponent);
                exponent.is_empty() || !exponent.bytes().all(|byte| byte.is_ascii_digit())
            })
        {
            return Err(Error::InvalidSyntax);
        }
        Ok(Self {
            value: ExactValue::Decimal(body.replace('_', "")),
            suffix,
            negative,
        })
    }

    pub fn written_type(&self) -> Option<NumberType> {
        self.suffix
    }
    pub fn is_negative(&self) -> bool {
        self.negative
    }
    pub fn magnitude(&self) -> Option<&BigUint> {
        match &self.value {
            ExactValue::Integer(value) => Some(value),
            ExactValue::Decimal(_) => None,
        }
    }

    /// A pure conversion result, not a completed semantic selection witness.
    /// No default type is guessed here, including for an arbitrarily large int.
    pub fn select(&self, ty: NumberType, layout: TargetLayout) -> Result<EncodedNumber, Error> {
        if self.suffix.is_some_and(|suffix| suffix != ty) {
            return Err(Error::IncompatibleSelection);
        }
        if let Some(format) = match ty {
            NumberType::F32 => Some(FloatFormat::F32),
            NumberType::F64 => Some(FloatFormat::F64),
            _ => None,
        } {
            let bits = match &self.value {
                ExactValue::Integer(magnitude) => round_integer(magnitude, format),
                ExactValue::Decimal(text) => match format {
                    FloatFormat::F32 => u64::from(
                        text.parse::<f32>()
                            .map_err(|_| Error::UnsupportedDecimal)?
                            .to_bits(),
                    ),
                    FloatFormat::F64 => text
                        .parse::<f64>()
                        .map_err(|_| Error::UnsupportedDecimal)?
                        .to_bits(),
                },
            } | if self.negative { format.sign_bit() } else { 0 };
            return Ok(EncodedNumber::Float(BinaryFloat { format, bits }));
        }
        let ExactValue::Integer(magnitude) = &self.value else {
            return Err(Error::IncompatibleSelection);
        };
        if ty == NumberType::BigInt {
            return Ok(EncodedNumber::BigInteger(BigInt::from_biguint(
                if self.negative {
                    Sign::Minus
                } else {
                    Sign::Plus
                },
                magnitude.clone(),
            )));
        }
        let (bits, signed) = match ty {
            NumberType::Int if matches!(layout.pointer_bits, 32 | 64) => {
                (layout.pointer_bits, true)
            }
            NumberType::Int => return Err(Error::UnsupportedTarget),
            NumberType::I8 => (8, true),
            NumberType::I16 => (16, true),
            NumberType::I32 => (32, true),
            NumberType::I64 => (64, true),
            NumberType::U8 => (8, false),
            NumberType::U16 => (16, false),
            NumberType::U32 => (32, false),
            NumberType::U64 => (64, false),
            _ => unreachable!("float and bigint selections returned above"),
        };
        let bound = BigUint::one() << if signed { bits - 1 } else { bits };
        let fits = if self.negative {
            if signed {
                magnitude <= &bound
            } else {
                magnitude.is_zero()
            }
        } else {
            magnitude < &bound
        };
        if !fits {
            return Err(Error::OutOfRange);
        }
        // Only the proved fixed-width result crosses the host integer boundary.
        let value = magnitude.to_i128().ok_or(Error::OutOfRange)?;
        Ok(EncodedNumber::Integer {
            value: if self.negative { -value } else { value },
            ty,
            bits,
            signed,
        })
    }
}

fn round_integer(magnitude: &BigUint, format: FloatFormat) -> u64 {
    let length = magnitude.bits();
    if length == 0 {
        return 0;
    }
    let mut exponent = length - 1;
    if exponent > format.max_exponent() {
        return format.infinity();
    }
    let precision = format.precision();
    let mut significand = if length <= u64::from(precision) {
        magnitude
            .to_u64()
            .expect("the exact significand fits in 53 bits")
            << (u64::from(precision) - length)
    } else {
        // The exponent check bounds this shift to at most 971, on every host.
        let shift = (length - u64::from(precision)) as usize;
        let leading = (magnitude >> shift)
            .to_u64()
            .expect("the leading significand fits in 53 bits");
        let remainder = magnitude - (BigUint::from(leading) << shift);
        let half = BigUint::one() << (shift - 1);
        leading + u64::from(remainder > half || remainder == half && leading & 1 != 0)
    };
    if significand == 1u64 << precision {
        significand >>= 1;
        exponent += 1;
    }
    if exponent > format.max_exponent() {
        return format.infinity();
    }
    let fraction_bits = precision - 1;
    ((exponent + format.max_exponent()) << fraction_bits) | (significand - (1u64 << fraction_bits))
}
