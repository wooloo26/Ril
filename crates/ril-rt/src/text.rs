use std::fmt::Write as _;

use num_traits::ToPrimitive as _;

use crate::{GcRuntime, Object, Value};

pub(crate) fn inspect_string(text: &str) -> String {
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

pub(crate) fn inspect_bytes(bytes: &[u8]) -> String {
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

pub(crate) fn str_at(gc: &GcRuntime, text: Value, index: Value) -> Option<u32> {
    let Object::Str(text) = gc.object(text)? else {
        return None;
    };
    let index = gc.integer(index)?.to_usize()?;
    text.scalar_at(index).map(u32::from)
}

pub(crate) fn byte_at(gc: &GcRuntime, bytes: Value, index: Value) -> Option<u8> {
    let Object::Bytes(bytes) = gc.object(bytes)? else {
        return None;
    };
    let index = gc.integer(index)?.to_usize()?;
    bytes.get(index).copied()
}

pub(crate) fn scalars(gc: &GcRuntime, values: Value) -> Option<String> {
    let Object::Array(values) = gc.object(values)? else {
        return None;
    };
    values
        .iter()
        .map(|&value| char::from_u32(gc.integer(value)?.to_u32()?))
        .collect()
}

pub(crate) fn bytes(gc: &GcRuntime, values: Value) -> Option<Vec<u8>> {
    let Object::Array(values) = gc.object(values)? else {
        return None;
    };
    values
        .iter()
        .map(|&value| gc.integer(value)?.to_u8())
        .collect()
}

pub(crate) fn option(gc: &mut GcRuntime, value: Option<Value>) -> Value {
    let tag = if value.is_some() { "Some" } else { "None" };
    gc.alloc(Object::Tag(tag.into(), value.into_iter().collect()))
}
