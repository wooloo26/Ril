//! Native ABI for generated Ril code. Values are managed 64-bit handles.
//! A Runtime pointer belongs to one executing program. Generated code publishes
//! every managed value needed after a safepoint in its current root frame.

use std::{collections::BTreeMap, io::Write as _};

use num_bigint::BigInt;
use num_traits::ToPrimitive as _;

use crate::{Object, Runtime, TypeDesc, Value};

macro_rules! runtime_functions {
    ($(fn $name:ident($ctx:ident $(, $arg:ident: $ty:ty)*) $(-> $ret:ty)? $body:block)*) => {
        $(
            #[unsafe(no_mangle)]
            unsafe extern "C" fn $name(raw: *mut Runtime $(, $arg: $ty)*) $(-> $ret)? {
                // SAFETY: the caller owns the live context and calls runtime operations sequentially.
                let $ctx = unsafe { &mut *raw };
                $body
            }
        )*
        const RUNTIME_FNS: &[(&str, *const u8)] = &[
            $((stringify!($name), $name as *const u8)),*
        ];
    };
}

#[unsafe(no_mangle)]
extern "C" fn ril_rt_create() -> *mut Runtime {
    Box::into_raw(Box::new(Runtime::default()))
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_rt_finish(context: *mut Runtime, value: Value) -> i32 {
    // SAFETY: generated main passes the unique pointer returned by ril_rt_create exactly once.
    let mut runtime = unsafe { Box::from_raw(context) };
    runtime.finish(value)
}

unsafe fn raw_bytes<'a>(data: *const u8, length: usize) -> &'a [u8] {
    // SAFETY: the module supplies an immutable static data symbol and its actual length.
    unsafe { std::slice::from_raw_parts(data, length) }
}

fn read_text(rt: &Runtime, value: Value) -> Result<String, &'static str> {
    match rt.gc.object(value) {
        Some(Object::Str(s)) => Ok(s.clone()),
        _ => Err("expected str"),
    }
}

runtime_functions! {
    fn ril_rt_roots_push(rt, count: usize) { rt.gc.push_frame(count); }
    fn ril_rt_roots_set(rt, slot: usize, value: Value) { rt.gc.set_root(slot, value); }
    fn ril_rt_roots_pop(rt) { rt.gc.pop_frame(); }
    fn ril_rt_safepoint(rt) { rt.gc.safepoint(); }
    fn ril_rt_alloc_words(rt, count: usize, desc: TypeDesc) -> Value {
        if count > 64 { rt.raise("invalid runtime type descriptor"); return Value::UNIT; }
        rt.gc.alloc(Object::Words { layout: desc, words: vec![Value::UNIT; count] })
    }
    fn ril_rt_int_literal(rt, data: *const u8, len: usize) -> Value {
        // SAFETY: generated code passes the address and length of the literal's data symbol.
        let data = unsafe { raw_bytes(data, len) };
        if let Some(num) = BigInt::parse_bytes(data, 10) { rt.gc.int(num).into() }
        else { rt.raise("invalid native integer literal"); Value::UNIT }
    }
    fn ril_rt_f64_literal(rt, bits: u64) -> Value { rt.gc.alloc(Object::F64(bits)) }
    fn ril_rt_string(rt, data: *const u8, len: usize) -> Value {
        // SAFETY: generated code passes the address and length of the string's data symbol.
        let data = unsafe { raw_bytes(data, len) };
        match std::str::from_utf8(data) {
            Ok(text) => rt.gc.alloc(Object::Str(text.to_owned())),
            Err(_) => { rt.raise("invalid native string literal"); Value::UNIT }
        }
    }
    fn ril_rt_bytes(rt, data: *const u8, len: usize) -> Value {
        // SAFETY: generated code passes the address and length of the bytes' data symbol.
        let data = unsafe { raw_bytes(data, len) };
        rt.gc.alloc(Object::Bytes(data.to_vec()))
    }
    fn ril_rt_int_add(rt, a: Value, b: Value) -> Value { numeric(rt, "+", a, b) }
    fn ril_rt_int_sub(rt, a: Value, b: Value) -> Value { numeric(rt, "-", a, b) }
    fn ril_rt_int_mul(rt, a: Value, b: Value) -> Value { numeric(rt, "*", a, b) }
    fn ril_rt_int_div(rt, a: Value, b: Value) -> Value { numeric(rt, "/", a, b) }
    fn ril_rt_int_rem(rt, a: Value, b: Value) -> Value { numeric(rt, "%", a, b) }
    fn ril_rt_int_and(rt, a: Value, b: Value) -> Value { numeric(rt, "&", a, b) }
    fn ril_rt_int_or(rt, a: Value, b: Value) -> Value { numeric(rt, "|", a, b) }
    fn ril_rt_int_xor(rt, a: Value, b: Value) -> Value { numeric(rt, "^", a, b) }
    fn ril_rt_int_shl(rt, a: Value, b: Value) -> Value { numeric(rt, "<<", a, b) }
    fn ril_rt_int_shr(rt, a: Value, b: Value) -> Value { numeric(rt, ">>", a, b) }
    fn ril_rt_equal(rt, a: Value, b: Value) -> Value { numeric(rt, "==", a, b) }
    fn ril_rt_not_equal(rt, a: Value, b: Value) -> Value { numeric(rt, "!=", a, b) }
    fn ril_rt_lt(rt, a: Value, b: Value) -> Value { numeric(rt, "<", a, b) }
    fn ril_rt_le(rt, a: Value, b: Value) -> Value { numeric(rt, "<=", a, b) }
    fn ril_rt_gt(rt, a: Value, b: Value) -> Value { numeric(rt, ">", a, b) }
    fn ril_rt_ge(rt, a: Value, b: Value) -> Value { numeric(rt, ">=", a, b) }
    fn ril_rt_neg(rt, a: Value) -> Value { unary(rt, "-", a) }
    fn ril_rt_not(rt, a: Value) -> Value { unary(rt, "!", a) }
    fn ril_rt_bit_not(rt, a: Value) -> Value { unary(rt, "~", a) }
    fn ril_rt_print(rt, value: Value) -> Value { print(rt, value, false) }
    fn ril_rt_println(rt, value: Value) -> Value { print(rt, value, true) }
    fn ril_rt_panic(rt, message: Value) -> Value {
        let text = read_text(rt, message).unwrap_or_else(|message| message.into());
        rt.raise(text);
        Value::UNIT
    }
    fn ril_rt_panic_take(rt) -> Value {
        let message = rt.take_panic().unwrap_or_default();
        rt.gc.alloc(Object::Str(message))
    }
    fn ril_rt_assert(rt, condition: Value, message: Value) -> Value {
        if condition != Value::TRUE {
            let text = read_text(rt, message).unwrap_or_else(|_| "assertion failed".into());
            rt.raise(text);
        }
        Value::UNIT
    }
    fn ril_rt_len(rt, value: Value) -> Value {
        let len = match rt.gc.object(value) {
            Some(Object::Str(s)) => s.chars().count(),
            Some(Object::Bytes(bytes)) => bytes.len(),
            Some(Object::Array(items) | Object::Tuple(items)) => items.len(),
            Some(Object::Map(entries)) => entries.len(),
            _ => { rt.raise("len requires a collection, bytes, or str"); return Value::UNIT; }
        };
        rt.gc.int(len.into()).into()
    }
    fn ril_rt_inspect(rt, value: Value) -> Value {
        let text = rt.gc.inspect(value);
        rt.gc.alloc(Object::Str(text))
    }
    fn ril_rt_text(rt, value: Value) -> Value {
        if matches!(rt.gc.object(value), Some(Object::Str(_))) { value }
        else { let text = rt.gc.inspect(value); rt.gc.alloc(Object::Str(text)) }
    }
    fn ril_rt_concat(rt, left: Value, right: Value) -> Value {
        let result = read_text(rt, left).and_then(|mut left| { left.push_str(&read_text(rt, right)?); Ok(left) });
        match result {
            Ok(text) => rt.gc.alloc(Object::Str(text)),
            Err(msg) => { rt.raise(msg); Value::UNIT }
        }
    }
    fn ril_rt_array(rt) -> Value { rt.gc.alloc(Object::Array(Vec::new())) }
    fn ril_rt_tuple(rt) -> Value { rt.gc.alloc(Object::Tuple(Vec::new())) }
    fn ril_rt_record(rt) -> Value { rt.gc.alloc(Object::Record(BTreeMap::new())) }
    fn ril_rt_map(rt) -> Value { rt.gc.alloc(Object::Map(Vec::new())) }
    fn ril_rt_tag(rt, name: Value) -> Value {
        if let Ok(tag) = read_text(rt, name) { rt.gc.alloc(Object::Tag(tag, Vec::new())) }
        else { rt.raise("constructor requires a tag"); Value::UNIT }
    }
    fn ril_rt_is_tag(rt, object: Value, expected: Value) -> Value {
        let name = read_text(rt, expected);
        Value::boolean(matches!((rt.gc.object(object), name), (Some(Object::Tag(a, _)), Ok(b)) if *a == b))
    }
    fn ril_rt_append(rt, target: Value, value: Value) -> Value {
        match rt.gc.object_mut(target) {
            Some(Object::Array(values) | Object::Tuple(values) | Object::Tag(_, values)) => values.push(value),
            _ => rt.raise("append destination is not a sequence"),
        }
        Value::UNIT
    }
    fn ril_rt_store(rt, target: Value, key: Value, value: Value) -> Value {
        let key_text = read_text(rt, key).ok();
        let index = rt.gc.integer(key).and_then(num_traits::ToPrimitive::to_usize);
        let target = rt.gc.draft_read(target).unwrap_or(target);
        match rt.gc.object_mut(target) {
            Some(Object::Record(fields)) if let Some(key) = key_text => { fields.insert(key, value); }
            Some(Object::Array(items) | Object::Tuple(items)) => {
                if let Some(slot) = index.and_then(|i| items.get_mut(i)) { *slot = value; }
                else { rt.raise("index out of bounds"); }
            }
            Some(Object::Map(entries)) => {
                if let Some((_, slot)) = entries.iter_mut().find(|(k, _)| *k == key) { *slot = value; }
                else { entries.push((key, value)); }
            }
            _ => rt.raise("invalid destination for object update"),
        }
        Value::UNIT
    }
    fn ril_rt_load(rt, target: Value, key: Value) -> Value {
        let value = load(rt, target, key);
        rt.checked(value.ok_or("index or member is missing"))
    }
    fn ril_rt_safe_load(rt, target: Value, key: Value) -> Value {
        let value = load(rt, target, key);
        match value {
            Some(value) => rt.gc.alloc(Object::Tag("Some".into(), vec![value])),
            None => rt.gc.alloc(Object::Tag("None".into(), Vec::new())),
        }
    }
    fn ril_rt_clone(rt, value: Value) -> Value {
        rt.gc.safepoint();
        let result = rt.gc.clone_graph(value);
        rt.checked(result)
    }
    fn ril_rt_draft_begin(rt, base: Value) -> Value {
        let result = rt.gc.draft_begin(base);
        rt.checked(result)
    }
    fn ril_rt_draft_read(rt, draft: Value) -> Value {
        let result = rt.gc.draft_read(draft);
        rt.checked(result)
    }
    fn ril_rt_draft_write(rt, draft: Value, value: Value) -> Value {
        let result = rt.gc.draft_write(draft, value).map(|()| Value::UNIT);
        rt.checked(result)
    }
    fn ril_rt_draft_commit(rt, draft: Value) -> Value {
        let result = rt.gc.draft_commit(draft);
        rt.checked(result)
    }
    fn ril_rt_draft_abort(rt, draft: Value) -> Value {
        let result = rt.gc.draft_abort(draft).map(|()| Value::UNIT);
        rt.checked(result)
    }
}

fn numeric(rt: &mut Runtime, op: &str, a: Value, b: Value) -> Value {
    let result = rt.gc.binary(op, a, b);
    rt.checked(result)
}

fn unary(rt: &mut Runtime, op: &str, a: Value) -> Value {
    let result = rt.gc.unary(op, a);
    rt.checked(result)
}

fn print(rt: &mut Runtime, value: Value, newline: bool) -> Value {
    match read_text(rt, value) {
        Ok(text) => {
            let mut stdout = std::io::stdout().lock();
            let result = stdout.write_all(text.as_bytes()).and_then(|()| {
                if newline {
                    stdout.write_all(b"\n")?;
                }
                stdout.flush()
            });
            if let Err(err) = result {
                rt.raise(err.to_string());
            }
        }
        Err(error) => rt.raise(error),
    }
    Value::UNIT
}

fn load(rt: &mut Runtime, target: Value, key: Value) -> Option<Value> {
    let target = rt.gc.draft_read(target).unwrap_or(target);
    match rt.gc.object(target)? {
        Object::Record(fields) => fields.get(&read_text(rt, key).ok()?).copied(),
        Object::Array(values) | Object::Tuple(values) | Object::Tag(_, values) => {
            values.get(rt.gc.integer(key)?.to_usize()?).copied()
        }
        Object::Map(entries) => entries
            .iter()
            .find(|(k, _)| rt.gc.equal(*k, key).unwrap_or(false))
            .map(|(_, v)| *v),
        Object::Str(text) => {
            let item = text
                .chars()
                .nth(rt.gc.integer(key)?.to_usize()?)?
                .to_string();
            Some(rt.gc.alloc(Object::Str(item)))
        }
        Object::Bytes(bytes) => {
            let byte = *bytes.get(rt.gc.integer(key)?.to_usize()?)?;
            Some(rt.gc.int(byte.into()).into())
        }
        _ => None,
    }
}

pub fn symbols() -> Vec<(&'static str, *const u8)> {
    let mut symbols = RUNTIME_FNS.to_vec();
    symbols.extend([
        ("ril_rt_create", ril_rt_create as *const u8),
        ("ril_rt_finish", ril_rt_finish as *const u8),
    ]);
    symbols
}
