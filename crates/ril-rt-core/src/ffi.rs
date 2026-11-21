//! Native ABI for generated Ril code. Values are managed 64-bit handles.
//! A Runtime pointer belongs to one executing program. Generated code publishes
//! every managed value needed after a safepoint in its current root frame.

use std::{collections::BTreeMap, io::Write as _};

use num_bigint::BigInt;
use num_traits::{FromPrimitive as _, ToPrimitive as _};

use crate::{Object, Runtime, TypeDesc, Value, text};

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
    fn ril_rt_cleanup_enter(rt) { rt.enter_cleanup(); }
    fn ril_rt_cleanup_leave(rt) { rt.leave_cleanup(); }
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
    fn ril_rt_file_read(rt, path: Value) -> Value {
        let result = read_text(rt, path).map_err(str::to_owned).and_then(|path|
            std::fs::read_to_string(path).map_err(|error| error.to_string()));
        match result {
            Ok(text) => {
                let payload = rt.gc.alloc(Object::Str(text));
                rt.gc.alloc(Object::Tag("Ok".into(), vec![payload]))
            }
            Err(error) => file_error(rt, error),
        }
    }
    fn ril_rt_file_write(rt, path: Value, value: Value) -> Value {
        let result = read_text(rt, path).and_then(|path| read_text(rt, value).map(|value| (path, value)))
            .map_err(str::to_owned).and_then(|(path, value)| std::fs::write(path, value).map_err(|error| error.to_string()));
        match result {
            Ok(()) => rt.gc.alloc(Object::Tag("Ok".into(), vec![Value::UNIT])),
            Err(error) => file_error(rt, error),
        }
    }
    fn ril_rt_to_f64(rt, value: Value) -> Value {
        if let Some(number) = rt.gc.integer(value).and_then(num_traits::ToPrimitive::to_f64) {
            rt.gc.alloc(Object::F64(number.to_bits()))
        } else { rt.raise("expected int"); Value::UNIT }
    }
    fn ril_rt_to_int(rt, value: Value) -> Value { float_to_int(rt, value, false) }
    fn ril_rt_trunc(rt, value: Value) -> Value { float_to_int(rt, value, true) }
    fn ril_rt_checked_div(rt, a: Value, b: Value) -> Value { checked_div(rt, "/", a, b) }
    fn ril_rt_checked_rem(rt, a: Value, b: Value) -> Value { checked_div(rt, "%", a, b) }
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
    fn ril_rt_str_starts_with(rt, value: Value, prefix: Value) -> Value {
        let test = read_text(rt, value).and_then(|text| read_text(rt, prefix).map(|prefix| Value::boolean(text.starts_with(&prefix))));
        rt.checked(test)
    }
    fn ril_rt_str_ends_with(rt, value: Value, suffix: Value) -> Value {
        let test = read_text(rt, value).and_then(|text| read_text(rt, suffix).map(|suffix| Value::boolean(text.ends_with(&suffix))));
        rt.checked(test)
    }
    fn ril_rt_str_at(rt, value: Value, index: Value) -> Value {
        let item = text::str_at(&rt.gc, value, index).map(|item| rt.gc.int(item.into()).into());
        text::option(&mut rt.gc, item)
    }
    fn ril_rt_bytes_at(rt, value: Value, index: Value) -> Value {
        let item = text::byte_at(&rt.gc, value, index).map(|item| rt.gc.int(item.into()).into());
        text::option(&mut rt.gc, item)
    }
    fn ril_rt_str_scalars(rt, value: Value) -> Value {
        match rt.gc.object(value) {
            Some(Object::Str(text)) => {
                let values = text.chars().map(u32::from).collect();
                text::int_array(&mut rt.gc, values)
            }
            _ => rt.checked(Err("String::scalars requires str")),
        }
    }
    fn ril_rt_bytes_to_array(rt, value: Value) -> Value {
        match rt.gc.object(value) {
            Some(Object::Bytes(bytes)) => {
                let values = bytes.iter().copied().map(u32::from).collect();
                text::int_array(&mut rt.gc, values)
            }
            _ => rt.checked(Err("Bytes::to_array requires bytes")),
        }
    }
    fn ril_rt_str_from_scalars(rt, values: Value) -> Value {
        let result = text::scalars(&rt.gc, values).map(|text| rt.gc.alloc(Object::Str(text)));
        text::option(&mut rt.gc, result)
    }
    fn ril_rt_bytes_from_array(rt, values: Value) -> Value {
        let result = text::bytes(&rt.gc, values).map(|bytes| rt.gc.alloc(Object::Bytes(bytes)));
        text::option(&mut rt.gc, result)
    }
    fn ril_rt_encode_utf8(rt, value: Value) -> Value {
        match rt.gc.object(value) {
            Some(Object::Str(text)) => rt.gc.alloc(Object::Bytes(text.as_bytes().to_vec())),
            _ => rt.checked(Err("String::encode_utf8 requires str")),
        }
    }
    fn ril_rt_decode_utf8(rt, value: Value) -> Value {
        let result = match rt.gc.object(value) {
            Some(Object::Bytes(bytes)) => std::str::from_utf8(bytes).ok().map(str::to_owned),
            _ => return rt.checked(Err("String::decode_utf8 requires bytes")),
        };
        let item = result.map(|text| rt.gc.alloc(Object::Str(text)));
        text::option(&mut rt.gc, item)
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
        store(rt, target, key, value)
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
    fn ril_rt_slice(rt, target: Value, start: Value, end: Value, inclusive: Value) -> Value {
        let result = slice(rt, target, start, end, inclusive == Value::TRUE).ok_or("slice bounds are outside the collection");
        rt.checked(result)
    }
    fn ril_rt_safe_slice(rt, target: Value, start: Value, end: Value, inclusive: Value) -> Value {
        match slice(rt, target, start, end, inclusive == Value::TRUE) {
            Some(result) => rt.gc.alloc(Object::Tag("Some".into(), vec![result])),
            None => rt.gc.alloc(Object::Tag("None".into(), Vec::new())),
        }
    }
    fn ril_rt_safe_member(rt, target: Value, key: Value) -> Value {
        let payload = match rt.gc.object(target) {
            Some(Object::Tag(tag, args)) if tag == "Some" => args.first().copied(),
            Some(Object::Tag(tag, _)) if tag == "None" => return target,
            _ => { rt.raise("safe member requires an Option"); return Value::UNIT; }
        };
        if let Some(payload) = payload && let Some(value) = load(rt, payload, key) {
            rt.gc.alloc(Object::Tag("Some".into(), vec![value]))
        } else { rt.raise("invalid optional member"); Value::UNIT }
    }
    fn ril_rt_clone(rt, value: Value) -> Value {
        rt.gc.safepoint();
        let result = rt.gc.clone_graph(value);
        rt.checked(result)
    }
    fn ril_rt_closure(rt, address: u64, arity: u64, evidence: Value, environment: Value) -> Value {
        rt.gc.alloc(Object::Closure { function: address, arity, environment, evidence })
    }
    fn ril_rt_closure_address(rt, closure: Value, expected: u64) -> Value {
        if let Some(Object::Closure { function, arity, .. }) = rt.gc.object(closure) && *arity == expected { Value(*function) }
        else { rt.raise("invalid callable"); Value::UNIT }
    }
    fn ril_rt_closure_evidence(rt, closure: Value) -> Value {
        if let Some(Object::Closure { evidence, .. }) = rt.gc.object(closure) { *evidence }
        else { rt.raise("invalid callable"); Value::UNIT }
    }
    fn ril_rt_closure_environment(rt, closure: Value) -> Value {
        if let Some(Object::Closure { environment, .. }) = rt.gc.object(closure) { *environment }
        else { rt.raise("invalid callable"); Value::UNIT }
    }
    fn ril_rt_evidence_push(rt, parent: Value, operation: Value, handler: Value) -> Value {
        if let Ok(operation) = read_text(rt, operation) {
            rt.gc.alloc(Object::Evidence { parent, operation, handler })
        } else { rt.raise("invalid effect operation"); Value::UNIT }
    }
    fn ril_rt_evidence_find(rt, evidence: Value, key: Value) -> Value {
        let mut evidence = evidence;
        if let Ok(key) = read_text(rt, key) {
            while let Some(Object::Evidence { parent, operation, handler }) = rt.gc.object(evidence) {
                if operation == &key { return *handler; }
                evidence = *parent;
            }
        }
        rt.raise("missing lexical effect handler");
        Value::UNIT
    }
    fn ril_rt_draft_begin(rt, base: Value) -> Value {
        let result = rt.gc.draft_begin(base);
        rt.checked(result)
    }
    fn ril_rt_draft_read(rt, draft: Value) -> Value {
        let result = rt.gc.draft_read(draft);
        rt.checked(result)
    }
    fn ril_rt_draft_write(rt, draft: Value, key: Value, value: Value) -> Value {
        match rt.gc.draft_read(draft) {
            Ok(copy) => store(rt, copy, key, value),
            Err(message) => rt.checked(Err(message)),
        }
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

fn file_error(rt: &mut Runtime, error: String) -> Value {
    let payload = rt.gc.alloc(Object::Str(error));
    rt.gc.alloc(Object::Tag("Err".into(), vec![payload]))
}

fn float_to_int(rt: &mut Runtime, value: Value, rounded: bool) -> Value {
    let number = match rt.gc.object(value) {
        Some(Object::F64(bits)) => f64::from_bits(*bits),
        _ => {
            rt.raise("expected f64");
            return Value::UNIT;
        }
    };
    if (rounded || number.fract() == 0.0)
        && let Some(integer) = BigInt::from_f64(number.trunc())
    {
        let payload = rt.gc.int(integer).into();
        rt.gc.alloc(Object::Tag("Some".into(), vec![payload]))
    } else {
        rt.gc.alloc(Object::Tag("None".into(), Vec::new()))
    }
}

fn checked_div(rt: &mut Runtime, op: &str, a: Value, b: Value) -> Value {
    match rt.gc.binary(op, a, b) {
        Ok(value) => rt.gc.alloc(Object::Tag("Some".into(), vec![value])),
        Err(_) => rt.gc.alloc(Object::Tag("None".into(), Vec::new())),
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

fn store(rt: &mut Runtime, target: Value, key: Value, value: Value) -> Value {
    let key_text = read_text(rt, key).ok();
    let index = rt
        .gc
        .integer(key)
        .and_then(num_traits::ToPrimitive::to_usize);
    match rt.gc.object_mut(target) {
        Some(Object::Record(fields)) if let Some(key) = key_text => {
            fields.insert(key, value);
        }
        Some(Object::Array(items) | Object::Tuple(items)) => {
            if let Some(slot) = index.and_then(|i| items.get_mut(i)) {
                *slot = value;
            } else {
                rt.raise("index out of bounds");
            }
        }
        Some(Object::Map(entries)) => {
            if let Some((_, slot)) = entries.iter_mut().find(|(k, _)| *k == key) {
                *slot = value;
            } else {
                entries.push((key, value));
            }
        }
        _ => rt.raise("invalid destination for object update"),
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

fn slice(
    rt: &mut Runtime,
    target: Value,
    start: Value,
    end: Value,
    inclusive: bool,
) -> Option<Value> {
    let object = rt.gc.object(target)?;
    let length = match object {
        Object::Str(text) => text.chars().count(),
        Object::Bytes(bytes) => bytes.len(),
        Object::Array(items) => items.len(),
        _ => return None,
    };
    let start = if start == Value::UNIT {
        0
    } else {
        rt.gc.integer(start)?.to_usize()?
    };
    let end = if end == Value::UNIT {
        length
    } else {
        rt.gc
            .integer(end)?
            .to_usize()?
            .checked_add(usize::from(inclusive))?
    };
    if start > end || end > length {
        return None;
    }
    let result = match object {
        Object::Array(items) => Object::Array(items.get(start..end)?.to_vec()),
        Object::Bytes(bytes) => Object::Bytes(bytes.get(start..end)?.to_vec()),
        Object::Str(text) => Object::Str(text.chars().skip(start).take(end - start).collect()),
        _ => return None,
    };
    Some(rt.gc.alloc(result))
}

pub fn symbols() -> Vec<(&'static str, *const u8)> {
    let mut symbols = RUNTIME_FNS.to_vec();
    symbols.extend([
        ("ril_rt_create", ril_rt_create as *const u8),
        ("ril_rt_finish", ril_rt_finish as *const u8),
    ]);
    #[cfg(not(miri))]
    {
        symbols.extend(crate::fiber::native::symbols());
    }
    symbols
}
