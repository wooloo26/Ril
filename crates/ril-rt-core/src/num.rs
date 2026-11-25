use std::{borrow::Cow, cmp::Ordering};

use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};

use crate::{GcRuntime, Object, Value};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct RilInt(pub u64);

impl From<RilInt> for Value {
    fn from(value: RilInt) -> Self {
        Self(value.0)
    }
}

impl Value {
    pub const SMALL_INT_TAG: u64 = 1;

    pub const fn from_small_int(number: i64) -> Option<Self> {
        // 63-bit signed integer stored in bits [63:1] with low tag bit 1.
        if number >= (i64::MIN >> 1) && number <= (i64::MAX >> 1) {
            Some(Self(
                (u64::from_ne_bytes(number.to_ne_bytes()) << 1) | Self::SMALL_INT_TAG,
            ))
        } else {
            None
        }
    }

    pub const fn small_int(self) -> Option<i64> {
        if self.0 & Self::SMALL_INT_TAG != 0 {
            Some(i64::from_ne_bytes(self.0.to_ne_bytes()) >> 1)
        } else {
            None
        }
    }

    pub const fn is_immediate(self) -> bool {
        self.0 == 0 || (self.0 & 0b111) != 0
    }
}

pub(crate) enum Integer<'a> {
    Small(i64),
    Large(&'a BigInt),
}

impl<'a> Integer<'a> {
    fn from_value(value: Value, object: Option<&'a Object>) -> Option<Self> {
        if let Some(number) = value.small_int() {
            return Some(Self::Small(number));
        }
        match object {
            Some(Object::Int(number)) => Some(Self::Large(number)),
            _ => None,
        }
    }

    fn into_big(self) -> Cow<'a, BigInt> {
        match self {
            Self::Small(number) => Cow::Owned(number.into()),
            Self::Large(number) => Cow::Borrowed(number),
        }
    }

    #[cfg(not(miri))]
    pub(crate) fn is_negative(&self) -> bool {
        match self {
            Self::Small(number) => *number < 0,
            Self::Large(number) => number.is_negative(),
        }
    }

    fn compare(self, other: Self) -> Ordering {
        match (self, other) {
            (Self::Small(a), Self::Small(b)) => a.cmp(&b),
            (a, b) => a.into_big().cmp(&b.into_big()),
        }
    }
}

impl ToPrimitive for Integer<'_> {
    fn to_i64(&self) -> Option<i64> {
        match self {
            Self::Small(number) => Some(*number),
            Self::Large(number) => number.to_i64(),
        }
    }

    fn to_u64(&self) -> Option<u64> {
        match self {
            Self::Small(number) => number.to_u64(),
            Self::Large(number) => number.to_u64(),
        }
    }

    fn to_f64(&self) -> Option<f64> {
        match self {
            Self::Small(number) => number.to_f64(),
            Self::Large(number) => number.to_f64(),
        }
    }
}

impl GcRuntime {
    pub fn int(&mut self, int: BigInt) -> RilInt {
        RilInt(self.alloc(Object::Int(int)).0)
    }

    pub(crate) fn int_i64(&mut self, number: i64) -> Value {
        Value::from_small_int(number).unwrap_or_else(|| self.int(number.into()).into())
    }

    pub(crate) fn integer(&self, value: Value) -> Option<Integer<'_>> {
        Integer::from_value(value, self.object(value))
    }

    pub(crate) fn binary(&mut self, op: &str, a: Value, b: Value) -> Result<Value, &'static str> {
        match op {
            "==" => return self.equal(a, b).map(Value::boolean),
            "!=" => return self.equal(a, b).map(|value| Value::boolean(!value)),
            _ => {}
        }
        let objects = (self.object(a), self.object(b));
        let integers = (
            Integer::from_value(a, objects.0),
            Integer::from_value(b, objects.1),
        );
        match op {
            "<" | "<=" | ">" | ">=" => {
                let order = if let (Some(a), Some(b)) = integers {
                    Some(a.compare(b))
                } else {
                    match objects {
                        (Some(Object::F64(a)), Some(Object::F64(b))) => {
                            f64::from_bits(*a).partial_cmp(&f64::from_bits(*b))
                        }
                        (Some(Object::Str(a)), Some(Object::Str(b))) => {
                            Some(a.as_str().cmp(b.as_str()))
                        }
                        (Some(Object::Bytes(a)), Some(Object::Bytes(b))) => Some(a.cmp(b)),
                        _ => return Err("invalid comparison operands"),
                    }
                };
                return Ok(Value::boolean(match op {
                    "<" => order == Some(Ordering::Less),
                    ">" => order == Some(Ordering::Greater),
                    "<=" => matches!(order, Some(Ordering::Less | Ordering::Equal)),
                    _ => matches!(order, Some(Ordering::Greater | Ordering::Equal)),
                }));
            }
            _ => {}
        }
        if let (Some(a), Some(b)) = integers {
            if let (Integer::Small(a), Integer::Small(b)) = (&a, &b)
                && let Some(number) = small_arithmetic(op, *a, *b)?
            {
                return Ok(self.int_i64(number));
            }
            let result = big_arithmetic(op, &a.into_big(), &b.into_big())?;
            return Ok(self.int(result).into());
        }
        let object = match objects {
            (Some(Object::F64(a)), Some(Object::F64(b))) => {
                let (a, b) = (f64::from_bits(*a), f64::from_bits(*b));
                Object::F64(match op {
                    "+" => (a + b).to_bits(),
                    "-" => (a - b).to_bits(),
                    "*" => (a * b).to_bits(),
                    "/" => (a / b).to_bits(),
                    "%" => (a % b).to_bits(),
                    _ => return Err("invalid floating-point operator"),
                })
            }
            _ => return Err("invalid arithmetic operands"),
        };
        Ok(self.alloc(object))
    }

    pub(crate) fn unary(&mut self, op: &str, value: Value) -> Result<Value, &'static str> {
        if op == "!" {
            return value
                .as_bool()
                .map(|b| Value::boolean(!b))
                .ok_or("logical negation requires bool");
        }
        let object = self.object(value);
        match (op, Integer::from_value(value, object)) {
            ("-", Some(Integer::Small(number))) => return Ok(self.int_i64(-number)),
            ("~", Some(Integer::Small(number))) => return Ok(self.int_i64(!number)),
            ("-", Some(Integer::Large(number))) => return Ok(self.int(-number).into()),
            ("~", Some(Integer::Large(number))) => return Ok(self.int(!number).into()),
            _ => {}
        }
        let object = match (op, object) {
            ("-", Some(Object::F64(bits))) => Object::F64((-f64::from_bits(*bits)).to_bits()),
            _ => return Err("invalid unary operand"),
        };
        Ok(self.alloc(object))
    }
}

fn small_arithmetic(op: &str, a: i64, b: i64) -> Result<Option<i64>, &'static str> {
    if b == 0 && matches!(op, "/" | "%") {
        return Err("integer division by zero");
    }
    if b < 0 && matches!(op, "<<" | ">>") {
        return Err("negative shift count");
    }
    // Two signed 63-bit operands can add or subtract without overflowing i64.
    // Division of the smallest inline value by -1 also fits in i64.
    Ok(match op {
        "+" => Some(a + b),
        "-" => Some(a - b),
        "*" => a.checked_mul(b),
        "/" => Some(a / b),
        "%" => Some(a % b),
        "&" => Some(a & b),
        "|" => Some(a | b),
        "^" => Some(a ^ b),
        "<<" if b < 63 => a.checked_mul(1_i64 << b),
        "<<" => None,
        ">>" => Some(a >> b.min(63)),
        _ => return Err("invalid integer operator"),
    })
}

fn big_arithmetic(op: &str, a: &BigInt, b: &BigInt) -> Result<BigInt, &'static str> {
    if b.is_zero() && matches!(op, "/" | "%") {
        return Err("integer division by zero");
    }
    if b.is_negative() && matches!(op, "<<" | ">>") {
        return Err("negative shift count");
    }
    Ok(match op {
        "+" => a + b,
        "-" => a - b,
        "*" => a * b,
        "/" => a / b,
        "%" => a % b,
        "&" => a & b,
        "|" => a | b,
        "^" => a ^ b,
        "<<" => a << b.to_usize().ok_or("shift exceeds memory capacity")?,
        ">>" if b.to_usize().is_none() && a.is_negative() => BigInt::from(-1),
        ">>" => a >> b.to_usize().unwrap_or(usize::MAX),
        _ => return Err("invalid integer operator"),
    })
}
