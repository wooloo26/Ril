use std::cmp::Ordering;

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

impl GcRuntime {
    pub fn int(&mut self, int: BigInt) -> RilInt {
        RilInt(self.alloc(Object::Int(int)).0)
    }

    pub(crate) fn integer(&self, value: Value) -> Option<&BigInt> {
        match self.object(value) {
            Some(Object::Int(number)) => Some(number),
            _ => None,
        }
    }

    pub(crate) fn binary(&mut self, op: &str, a: Value, b: Value) -> Result<Value, &'static str> {
        match op {
            "==" => return self.equal(a, b).map(Value::boolean),
            "!=" => return self.equal(a, b).map(|value| Value::boolean(!value)),
            "<" | "<=" | ">" | ">=" => {
                let order = match (self.object(a), self.object(b)) {
                    (Some(Object::Int(a)), Some(Object::Int(b))) => Some(a.cmp(b)),
                    (Some(Object::F64(a)), Some(Object::F64(b))) => {
                        f64::from_bits(*a).partial_cmp(&f64::from_bits(*b))
                    }
                    (Some(Object::Str(a)), Some(Object::Str(b))) => Some(a.cmp(b)),
                    (Some(Object::Bytes(a)), Some(Object::Bytes(b))) => Some(a.cmp(b)),
                    _ => return Err("invalid comparison operands"),
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
        let object = match (self.object(a), self.object(b)) {
            (Some(Object::Int(a)), Some(Object::Int(b))) => {
                if b.is_zero() && matches!(op, "/" | "%") {
                    return Err("integer division by zero");
                }
                if b.is_negative() && matches!(op, "<<" | ">>") {
                    return Err("negative shift count");
                }
                Object::Int(match op {
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
        let object = match (op, self.object(value)) {
            ("-", Some(Object::Int(number))) => Object::Int(-number),
            ("~", Some(Object::Int(number))) => Object::Int(!number),
            ("-", Some(Object::F64(bits))) => Object::F64((-f64::from_bits(*bits)).to_bits()),
            _ => return Err("invalid unary operand"),
        };
        Ok(self.alloc(object))
    }
}
