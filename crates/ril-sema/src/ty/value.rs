use std::{cmp::Ordering, collections::BTreeMap, fmt::Write as _};

use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};
use ril_syntax::syntax::{Literal, LiteralKind};

use super::{MemberMode, Ty};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Value {
    Unit,
    Bool(bool),
    Int(BigInt),
    F64(u64),
    Str(String),
    Bytes(Vec<u8>),
    Tuple(Vec<Self>),
    Array(Vec<Self>),
    Record(BTreeMap<String, Self>),
    Map(Vec<(Self, Self)>),
    Tag(String, Vec<Self>),
    Type(Box<Ty>),
    Mode(MemberMode),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LiteralError {
    Invalid,
    Overflow,
}

pub fn literal(literal: &Literal) -> Result<Value, LiteralError> {
    let text = &literal.text;
    let invalid = LiteralError::Invalid;
    Ok(match literal.kind {
        LiteralKind::Int => {
            let (negative, digits) = text
                .strip_prefix('-')
                .map_or((false, text.as_str()), |rest| (true, rest));
            let (base, digits) = match digits.get(..2) {
                Some("0x" | "0X") => (16, digits.get(2..).ok_or(invalid)?),
                Some("0o" | "0O") => (8, digits.get(2..).ok_or(invalid)?),
                Some("0b" | "0B") => (2, digits.get(2..).ok_or(invalid)?),
                _ => (10, digits),
            };
            let int =
                BigInt::parse_bytes(digits.replace('_', "").as_bytes(), base).ok_or(invalid)?;
            Value::Int(if negative { -int } else { int })
        }
        LiteralKind::F64 => {
            let float = text.replace('_', "").parse::<f64>().map_err(|_| invalid)?;
            if !float.is_finite() {
                return Err(LiteralError::Overflow);
            }
            Value::F64(float.to_bits())
        }
        LiteralKind::Bool => Value::Bool(text == "true"),
        LiteralKind::String => {
            Value::Str(String::from_utf8(decode_text(text, false)?).map_err(|_| invalid)?)
        }
        LiteralKind::RawString => Value::Str(raw_body(text)?.to_owned()),
        LiteralKind::Bytes => Value::Bytes(decode_text(
            text.strip_prefix("bytes\"")
                .and_then(|s| s.strip_suffix('"'))
                .ok_or(invalid)?,
            true,
        )?),
        LiteralKind::RawBytes => Value::Bytes(
            raw_body(text.strip_prefix("bytes").ok_or(invalid)?)?
                .as_bytes()
                .to_vec(),
        ),
    })
}

fn raw_body(source: &str) -> Result<&str, LiteralError> {
    let (hashes, body) = source.split_once('"').ok_or(LiteralError::Invalid)?;
    body.strip_suffix(hashes)
        .and_then(|s| s.strip_suffix('"'))
        .ok_or(LiteralError::Invalid)
}

pub(super) fn decode_text(text: &str, bytes: bool) -> Result<Vec<u8>, LiteralError> {
    let invalid = LiteralError::Invalid;
    let mut chars = text.chars();
    let mut result = Vec::new();
    while let Some(ch) = chars.next() {
        let scalar = match ch {
            '\\' => match chars.next().ok_or(invalid)? {
                '\\' => '\\',
                '"' => '"',
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                '0' => '\0',
                'x' if bytes => {
                    let high = chars.next().and_then(|n| n.to_digit(16)).ok_or(invalid)?;
                    let low = chars.next().and_then(|n| n.to_digit(16)).ok_or(invalid)?;
                    result.push(u8::try_from(high * 16 + low).map_err(|_| invalid)?);
                    continue;
                }
                'u' if chars.next() == Some('{') => {
                    let mut value = 0_u32;
                    loop {
                        let next = chars.next().ok_or(invalid)?;
                        if next == '}' {
                            break;
                        }
                        value = (value * 16) + next.to_digit(16).ok_or(invalid)?;
                    }
                    char::from_u32(value).ok_or(invalid)?
                }
                _ => return Err(invalid),
            },
            '{' | '}' if !bytes => {
                if chars.next() != Some(ch) {
                    return Err(invalid);
                }
                ch
            }
            _ => ch,
        };
        result.extend_from_slice(scalar.encode_utf8(&mut [0; 4]).as_bytes());
    }
    Ok(result)
}

pub fn render(value: &Value) -> String {
    match value {
        Value::Unit => "()".into(),
        Value::Bool(value) => value.to_string(),
        Value::Int(value) => value.to_string(),
        Value::F64(value) => format!("{:?}", f64::from_bits(*value)),
        Value::Str(value) => inspect_string(value),
        Value::Bytes(value) => inspect_bytes(value),
        Value::Tuple(values) => format!("({})", render_list(values)),
        Value::Array(values) => format!("[{}]", render_list(values)),
        Value::Record(fields) => format!(
            ".{{ {} }}",
            fields
                .iter()
                .map(|(k, v)| format!("{k}: {}", render(v)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Value::Map(entries) => format!(
            "[{}]",
            entries
                .iter()
                .map(|(k, v)| format!("{}: {}", render(k), render(v)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Value::Tag(name, values) if values.is_empty() => name.clone(),
        Value::Tag(name, values) => format!("{name}({})", render_list(values)),
        Value::Type(_) => "<type>".into(),
        Value::Mode(mode) => super::mode_name(*mode).into(),
    }
}

fn inspect_string(text: &str) -> String {
    let mut out = String::from("\"");
    for ch in text.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            '{' => out.push_str("{{"),
            '}' => out.push_str("}}"),
            ch if ch.is_control() => {
                let _ = write!(out, "\\u{{{:x}}}", u32::from(ch));
            }
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}

fn inspect_bytes(bytes: &[u8]) -> String {
    let mut out = String::from("bytes\"");
    for &byte in bytes {
        match byte {
            b'\\' => out.push_str("\\\\"),
            b'"' => out.push_str("\\\""),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            0 => out.push_str("\\0"),
            b' '..=b'~' => out.push(char::from(byte)),
            _ => {
                let _ = write!(out, "\\x{byte:02x}");
            }
        }
    }
    out.push('"');
    out
}

fn render_list(values: &[Value]) -> String {
    values.iter().map(render).collect::<Vec<_>>().join(", ")
}

pub(super) fn ieee_equal(left: &Value, right: &Value) -> bool {
    match (left, right) {
        (Value::F64(left), Value::F64(right)) => f64::from_bits(*left) == f64::from_bits(*right),
        (Value::Tuple(left) | Value::Array(left), Value::Tuple(right) | Value::Array(right)) => {
            items_equal(left, right)
        }
        (Value::Record(left), Value::Record(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .all(|(key, left)| right.get(key).is_some_and(|right| ieee_equal(left, right)))
        }
        (Value::Tag(lt, left), Value::Tag(rt, right)) => lt == rt && items_equal(left, right),
        (Value::Map(left), Value::Map(right)) => {
            left.len() == right.len()
                && left.iter().all(|(key, left)| {
                    right
                        .iter()
                        .any(|(rk, right)| ieee_equal(key, rk) && ieee_equal(left, right))
                })
        }
        _ => left == right,
    }
}

fn items_equal(left: &[Value], right: &[Value]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| ieee_equal(left, right))
}

pub fn arithmetic(op: &str, left: Value, right: Value) -> Result<Value, &'static str> {
    if matches!(op, "==" | "!=") {
        return Ok(Value::Bool(ieee_equal(&left, &right) == (op == "==")));
    }
    if matches!(op, "<" | "<=" | ">" | ">=") {
        let order = match (&left, &right) {
            (Value::Int(left), Value::Int(right)) => Some(left.cmp(right)),
            (Value::F64(left), Value::F64(right)) => {
                f64::from_bits(*left).partial_cmp(&f64::from_bits(*right))
            }
            (Value::Str(left), Value::Str(right)) => Some(left.cmp(right)),
            (Value::Bytes(left), Value::Bytes(right)) => Some(left.cmp(right)),
            _ => return Err("invalid operands for ordering"),
        };
        return Ok(Value::Bool(match op {
            "<" => order == Some(Ordering::Less),
            ">" => order == Some(Ordering::Greater),
            "<=" => matches!(order, Some(Ordering::Less | Ordering::Equal)),
            _ => matches!(order, Some(Ordering::Greater | Ordering::Equal)),
        }));
    }
    match (left, right) {
        (Value::Bool(left), Value::Bool(right)) => match op {
            "&&" => Ok(Value::Bool(left && right)),
            "||" => Ok(Value::Bool(left || right)),
            _ => Err("invalid boolean operator"),
        },
        (Value::Int(left), Value::Int(right)) => {
            if right.is_zero() && matches!(op, "/" | "%") {
                return Err("integer division by zero");
            }
            if right.is_negative() && matches!(op, "<<" | ">>") {
                return Err("negative shift count");
            }
            Ok(Value::Int(match op {
                "+" => left + right,
                "-" => left - right,
                "*" => left * right,
                "/" => left / right,
                "%" => left % right,
                "&" => left & right,
                "|" => left | right,
                "^" => left ^ right,
                "<<" => {
                    left << right
                        .to_usize()
                        .ok_or("shift count exceeds memory capacity")?
                }
                ">>" => {
                    if let Some(count) = right.to_usize() {
                        left >> count
                    } else if left.is_negative() {
                        BigInt::from(-1)
                    } else {
                        BigInt::ZERO
                    }
                }
                _ => return Err("invalid integer operator"),
            }))
        }
        (Value::F64(left), Value::F64(right)) => {
            let (left, right) = (f64::from_bits(left), f64::from_bits(right));
            let value = match op {
                "+" => left + right,
                "-" => left - right,
                "*" => left * right,
                "/" => left / right,
                "%" => left % right,
                _ => return Err("invalid floating-point operator"),
            };
            Ok(Value::F64(value.to_bits()))
        }
        _ => Err("invalid operand types"),
    }
}

pub(super) fn static_argument(value: Value) -> Value {
    match value {
        Value::F64(bits) if f64::from_bits(bits).is_nan() => Value::F64(f64::NAN.to_bits()),
        Value::Tuple(items) => Value::Tuple(items.into_iter().map(static_argument).collect()),
        Value::Array(items) => Value::Array(items.into_iter().map(static_argument).collect()),
        Value::Tag(tag, items) => Value::Tag(tag, items.into_iter().map(static_argument).collect()),
        Value::Record(fields) => Value::Record(
            fields
                .into_iter()
                .map(|(k, v)| (k, static_argument(v)))
                .collect(),
        ),
        Value::Map(entries) => Value::Map(
            entries
                .into_iter()
                .map(|(k, v)| (static_argument(k), static_argument(v)))
                .collect(),
        ),
        value => value,
    }
}
