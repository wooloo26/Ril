use num_traits::ToPrimitive as _;

use crate::{GcRuntime, Object, Value};

pub(crate) fn str_at(gc: &GcRuntime, text: Value, index: Value) -> Option<u32> {
    let Object::Str(text) = gc.object(text)? else {
        return None;
    };
    let index = gc.integer(index)?.to_usize()?;
    text.chars().nth(index).map(u32::from)
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

pub(crate) fn int_array(gc: &mut GcRuntime, values: Vec<u32>) -> Value {
    gc.push_frame(values.len());
    let mut items = Vec::with_capacity(values.len());
    for (index, value) in values.into_iter().enumerate() {
        let value = gc.int(value.into()).into();
        gc.set_root(index, value);
        items.push(value);
    }
    let result = gc.alloc(Object::Array(items));
    gc.pop_frame();
    result
}

pub(crate) fn option(gc: &mut GcRuntime, value: Option<Value>) -> Value {
    let tag = if value.is_some() { "Some" } else { "None" };
    gc.alloc(Object::Tag(tag.into(), value.into_iter().collect()))
}
