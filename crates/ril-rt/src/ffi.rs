//! Native ABI for generated Ril code. Values are managed 64-bit handles.
//! A Runtime pointer belongs to one executing program. Generated code publishes
//! every managed value needed after a safepoint in its current root frame.

use std::{collections::BTreeMap, io::Write as _};

use num_bigint::BigInt;
use num_traits::{FromPrimitive as _, ToPrimitive as _};

use crate::{Object, RilMap, RilStr, Runtime, Value, draft::DraftSlot, text};

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
        Some(Object::Str(s)) => Ok(s.as_str().to_owned()),
        _ => Err("expected str"),
    }
}

runtime_functions! {
    fn ril_rt_cleanup_enter(rt) { rt.enter_cleanup(); }
    fn ril_rt_cleanup_leave(rt) { rt.leave_cleanup(); }
    fn ril_rt_int_literal(rt, data: *const u8, len: usize) -> Value {
        // SAFETY: generated code passes the address and length of the literal's data symbol.
        let data = unsafe { raw_bytes(data, len) };
        if let Ok(text) = std::str::from_utf8(data)
            && let Ok(number) = text.parse::<i64>()
        { return rt.gc.int_i64(number); }
        if let Some(num) = BigInt::parse_bytes(data, 10) { rt.gc.int(num).into() }
        else { rt.raise("invalid native integer literal"); Value::UNIT }
    }
    fn ril_rt_f64_literal(rt, bits: u64) -> Value { rt.gc.alloc(Object::F64(bits)) }
    fn ril_rt_string(rt, data: *const u8, len: usize) -> Value {
        // SAFETY: generated code passes the address and length of the string's data symbol.
        let data = unsafe { raw_bytes(data, len) };
        match std::str::from_utf8(data) {
            Ok(text) => rt.gc.alloc(Object::Str(RilStr::new(text.to_owned()))),
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
                let payload = rt.gc.alloc(Object::Str(RilStr::new(text)));
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
        if let Some(number) = rt.gc.integer(value) {
            let f = number.to_f64().unwrap_or_else(|| {
                if number.is_negative() {
                    f64::NEG_INFINITY
                } else {
                    f64::INFINITY
                }
            });
            rt.gc.alloc(Object::F64(f.to_bits()))
        } else {
            rt.raise("expected int");
            Value::UNIT
        }
    }
    fn ril_rt_to_int(rt, value: Value) -> Value { float_to_int(rt, value, false) }
    fn ril_rt_trunc(rt, value: Value) -> Value { float_to_int(rt, value, true) }
    fn ril_rt_print(rt, value: Value) -> Value { print(rt, value, false) }
    fn ril_rt_println(rt, value: Value) -> Value { print(rt, value, true) }
    fn ril_rt_panic(rt, message: Value) -> Value {
        let text = read_text(rt, message).unwrap_or_else(|message| message.into());
        rt.raise(text);
        Value::UNIT
    }
    fn ril_rt_panic_take(rt) -> Value {
        let message = rt.take_panic().unwrap_or_default();
        rt.gc.alloc(Object::PanicInfo(message))
    }
    fn ril_rt_panic_message(rt, info: Value) -> Value {
        match rt.gc.object(info) {
            Some(Object::PanicInfo(message)) => rt.gc.alloc(Object::Str(RilStr::new(message.clone()))),
            _ => rt.checked(Err("panic_message requires PanicInfo")),
        }
    }
    fn ril_rt_assert(rt, condition: Value, message: Value) -> Value {
        if condition != Value::TRUE {
            let text = read_text(rt, message).unwrap_or_else(|_| "assertion failed".into());
            rt.raise(text);
        }
        Value::UNIT
    }
    fn ril_rt_len(rt, value: Value) -> Value {
        let value = rt.gc.draft_read(value).unwrap_or(value);
        let len = match rt.gc.object(value) {
            Some(Object::Str(s)) => s.scalar_len(),
            Some(Object::Bytes(bytes)) => bytes.len(),
            Some(Object::Array(items) | Object::Tuple(items)) => items.len(),
            Some(Object::Map(map)) => map.len(),
            _ => { rt.raise("len requires a collection, bytes, or str"); return Value::UNIT; }
        };
        match i64::try_from(len) {
            Ok(len) => rt.gc.int_i64(len),
            Err(_) => rt.gc.int(len.into()).into(),
        }
    }
    fn ril_rt_inspect(rt, value: Value) -> Value {
        let text = rt.gc.inspect(value);
        rt.gc.alloc(Object::Str(RilStr::new(text)))
    }
    fn ril_rt_inspect_typed(rt, value: Value, plan: Value) -> Value {
        let text = rt.gc.inspect_typed(value, plan);
        rt.gc.alloc(Object::Str(RilStr::new(text)))
    }
    fn ril_rt_text(rt, value: Value) -> Value {
        if matches!(rt.gc.object(value), Some(Object::Str(_))) { value }
        else { let text = rt.gc.inspect(value); rt.gc.alloc(Object::Str(RilStr::new(text))) }
    }
    fn ril_rt_concat(rt, left: Value, right: Value) -> Value {
        let result = read_text(rt, left).and_then(|mut left| { left.push_str(&read_text(rt, right)?); Ok(left) });
        match result {
            Ok(text) => rt.gc.alloc(Object::Str(RilStr::new(text))),
            Err(msg) => { rt.raise(msg); Value::UNIT }
        }
    }
    fn ril_rt_concat_many(rt, parts: Value) -> Value {
        let Some(Object::Array(items)) = rt.gc.object(parts) else {
            rt.raise("ril_rt_concat_many requires an array");
            return Value::UNIT;
        };
        let mut total_len = 0usize;
        for &item in items {
            match rt.gc.object(item) {
                Some(Object::Str(s)) => total_len = total_len.saturating_add(s.len()),
                _ => {
                    rt.raise("expected str");
                    return Value::UNIT;
                }
            }
        }
        let mut out = String::with_capacity(total_len);
        for &item in items {
            if let Some(Object::Str(s)) = rt.gc.object(item) {
                out.push_str(s);
            }
        }
        rt.gc.alloc(Object::Str(RilStr::new(out)))
    }
    fn ril_rt_str_starts_with(rt, value: Value, prefix: Value) -> Value {
        let test = read_text(rt, value).and_then(|text| read_text(rt, prefix).map(|prefix| Value::boolean(text.starts_with(&prefix))));
        rt.checked(test)
    }
    fn ril_rt_str_join(rt, parts: Value, separator: Value) -> Value {
        match text::join(&rt.gc, parts, separator) {
            Some(text) => rt.gc.alloc(Object::Str(RilStr::new(text))),
            None => rt.checked(Err("String::join requires []str and str")),
        }
    }
    fn ril_rt_str_split(rt, value: Value, separator: Value) -> Value {
        let Some(parts) = text::split(&rt.gc, value, separator) else {
            return rt.checked(Err("String::split requires str and str"));
        };
        let array = rt.gc.alloc(Object::Array(Vec::new()));
        rt.gc.pin(array);
        for part in parts {
            let item = rt.gc.alloc(Object::Str(RilStr::new(part)));
            if let Some(Object::Array(items)) = rt.gc.object_mut(array) {
                items.push(item);
            }
        }
        rt.gc.unpin(array);
        array
    }
    fn ril_rt_str_ends_with(rt, value: Value, suffix: Value) -> Value {
        let test = read_text(rt, value).and_then(|text| read_text(rt, suffix).map(|suffix| Value::boolean(text.ends_with(&suffix))));
        rt.checked(test)
    }
    fn ril_rt_str_at(rt, value: Value, index: Value) -> Value {
        let item = text::str_at(&rt.gc, value, index).map(|item| rt.gc.int_i64(i64::from(item)));
        text::option(&mut rt.gc, item)
    }
    fn ril_rt_bytes_at(rt, value: Value, index: Value) -> Value {
        let item = text::byte_at(&rt.gc, value, index).map(|item| rt.gc.int_i64(i64::from(item)));
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
        let result = text::scalars(&rt.gc, values).map(|text| rt.gc.alloc(Object::Str(RilStr::new(text))));
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
        let item = result.map(|text| rt.gc.alloc(Object::Str(RilStr::new(text))));
        text::option(&mut rt.gc, item)
    }
    fn ril_rt_array(rt) -> Value { rt.gc.alloc(Object::Array(Vec::new())) }
    fn ril_rt_tuple(rt) -> Value { rt.gc.alloc(Object::Tuple(Vec::new())) }
    fn ril_rt_record(rt) -> Value { rt.gc.alloc(Object::Record(BTreeMap::new())) }
    fn ril_rt_map(rt) -> Value { rt.gc.alloc(Object::Map(RilMap::new())) }
    fn ril_rt_array_pop(rt, target: Value) -> Value {
        let target = rt.gc.draft_read(target).unwrap_or(target);
        let item = match rt.gc.object_mut(target) {
            Some(Object::Array(values)) => values.pop(),
            _ => return rt.checked(Err("Array::pop requires an array")),
        };
        text::option(&mut rt.gc, item)
    }
    fn ril_rt_array_insert(rt, target: Value, index: Value, value: Value) -> Value {
        let target = rt.gc.draft_read(target).unwrap_or(target);
        let value = match rt.gc.draft_insertion(target, value) {
            Ok(value) => value,
            Err(message) => return rt.checked(Err(message)),
        };
        let Some(index) = rt.gc.integer(index).and_then(|n| n.to_usize()) else {
            rt.raise("index out of bounds");
            return Value::UNIT;
        };
        match rt.gc.object_mut(target) {
            Some(Object::Array(values)) if index <= values.len() => values.insert(index, value),
            Some(Object::Array(_)) => rt.raise("index out of bounds"),
            _ => rt.raise("Array::insert requires an array"),
        }
        Value::UNIT
    }
    fn ril_rt_array_remove(rt, target: Value, index: Value) -> Value {
        let target = rt.gc.draft_read(target).unwrap_or(target);
        let index = rt.gc.integer(index).and_then(|n| n.to_usize());
        let item = match rt.gc.object_mut(target) {
            Some(Object::Array(values)) => {
                index.and_then(|i| (i < values.len()).then(|| values.remove(i)))
            }
            _ => return rt.checked(Err("Array::remove requires an array")),
        };
        text::option(&mut rt.gc, item)
    }
    fn ril_rt_array_clear(rt, target: Value) -> Value {
        let target = rt.gc.draft_read(target).unwrap_or(target);
        match rt.gc.object_mut(target) {
            Some(Object::Array(values)) => values.clear(),
            _ => rt.raise("Array::clear requires an array"),
        }
        Value::UNIT
    }
    fn ril_rt_array_sort(rt, target: Value) -> Value {
        let target = rt.gc.draft_read(target).unwrap_or(target);
        let mut items = match rt.gc.object(target) {
            Some(Object::Array(values)) => values.clone(),
            _ => return rt.checked(Err("Array::sort requires an array")),
        };
        items.sort_by(|&a, &b| compare_sortable(&rt.gc, a, b));
        if let Some(Object::Array(values)) = rt.gc.object_mut(target) {
            *values = items;
        }
        Value::UNIT
    }
    fn ril_rt_map_get(rt, target: Value, key: Value) -> Value {
        let value = load(rt, target, key);
        text::option(&mut rt.gc, value)
    }
    fn ril_rt_map_insert(rt, target: Value, key: Value, value: Value) -> Value {
        let target = rt.gc.draft_read(target).unwrap_or(target);
        store(rt, target, key, value)
    }
    fn ril_rt_map_remove(rt, target: Value, key: Value) -> Value {
        let target = rt.gc.draft_read(target).unwrap_or(target);
        let hash = rt.gc.bisim_hash(key);
        let existing = match rt.gc.object(target) {
            Some(Object::Map(map)) => {
                map.find_index(hash, |stored| rt.gc.equal(stored, key).unwrap_or(false))
            }
            _ => return rt.checked(Err("Map::remove requires a map")),
        };
        let removed = existing.and_then(|index| {
            if let Some(Object::Map(map)) = rt.gc.object_mut(target) {
                map.remove_at(index).map(|(_, v)| v)
            } else {
                None
            }
        });
        text::option(&mut rt.gc, removed)
    }
    fn ril_rt_map_contains(rt, target: Value, key: Value) -> Value {
        let target = rt.gc.draft_read(target).unwrap_or(target);
        let hash = rt.gc.bisim_hash(key);
        match rt.gc.object(target) {
            Some(Object::Map(map)) => Value::boolean(
                map.find_index(hash, |stored| rt.gc.equal(stored, key).unwrap_or(false))
                    .is_some(),
            ),
            _ => rt.checked(Err("Map::contains requires a map")),
        }
    }
    fn ril_rt_map_clear(rt, target: Value) -> Value {
        let target = rt.gc.draft_read(target).unwrap_or(target);
        match rt.gc.object_mut(target) {
            Some(Object::Map(map)) => map.clear(),
            _ => rt.raise("Map::clear requires a map"),
        }
        Value::UNIT
    }
    fn ril_rt_map_keys(rt, target: Value) -> Value {
        let target = rt.gc.draft_read(target).unwrap_or(target);
        let keys: Vec<Value> = match rt.gc.object(target) {
            Some(Object::Map(map)) => map.entries().iter().map(|&(_, k, _)| k).collect(),
            _ => return rt.checked(Err("Map::keys requires a map")),
        };
        rt.gc.alloc(Object::Array(keys))
    }
    fn ril_rt_map_values(rt, target: Value) -> Value {
        let target = rt.gc.draft_read(target).unwrap_or(target);
        let values: Vec<Value> = match rt.gc.object(target) {
            Some(Object::Map(map)) => map.entries().iter().map(|&(_, _, v)| v).collect(),
            _ => return rt.checked(Err("Map::values requires a map")),
        };
        rt.gc.alloc(Object::Array(values))
    }
    fn ril_rt_tag(rt, name: Value) -> Value {
        if let Ok(tag) = read_text(rt, name) { rt.gc.alloc(Object::Tag(tag, Vec::new())) }
        else { rt.raise("constructor requires a tag"); Value::UNIT }
    }
    fn ril_rt_is_tag(rt, object: Value, expected: Value) -> Value {
        let object = rt.gc.draft_read(object).unwrap_or(object);
        let name = read_text(rt, expected);
        Value::boolean(matches!((rt.gc.object(object), name), (Some(Object::Tag(a, _)), Ok(b)) if *a == b))
    }
    fn ril_rt_append(rt, target: Value, value: Value) -> Value {
        let target = rt.gc.draft_read(target).unwrap_or(target);
        let value = match rt.gc.draft_insertion(target, value) {
            Ok(value) => value,
            Err(message) => return rt.checked(Err(message)),
        };
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
    fn ril_rt_iter_at(rt, target: Value, position: Value) -> Value {
        let value = iter_at(rt, target, position);
        rt.checked(value.ok_or("iteration position is outside the collection"))
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
        let target = rt.gc.draft_read(target).unwrap_or(target);
        let payload = match rt.gc.object(target) {
            Some(Object::Tag(tag, args)) if tag == "Some" => args.first().copied(),
            Some(Object::Tag(tag, _)) if tag == "None" => return target,
            _ => { rt.raise("safe member requires an Option"); return Value::UNIT; }
        };
        if let Some(raw) = payload
            && let Some(payload) = rt.gc.draft_child(target, DraftSlot::Element(0), raw)
            && let Some(value) = load(rt, payload, key)
        {
            rt.gc.alloc(Object::Tag("Some".into(), vec![value]))
        } else { rt.raise("invalid optional member"); Value::UNIT }
    }
    fn ril_rt_clone(rt, value: Value) -> Value {
        rt.gc.safepoint();
        let result = rt.gc.clone_graph(value);
        rt.checked(result)
    }
    fn ril_rt_closure(rt, address: *const u8, arity: u64, evidence: Value, environment: Value) -> Value {
        rt.gc.alloc(Object::Closure { function: address, arity, environment, evidence })
    }
    fn ril_rt_closure_address(rt, closure: Value, expected: u64) -> *const u8 {
        if let Some(Object::Closure { function, arity, .. }) = rt.gc.object(closure) && *arity == expected { *function }
        else { rt.raise("invalid callable"); std::ptr::null() }
    }
    fn ril_rt_closure_evidence(rt, closure: Value) -> Value {
        if let Some(Object::Closure { evidence, .. }) = rt.gc.object(closure) { *evidence }
        else { rt.raise("invalid callable"); Value::UNIT }
    }
    fn ril_rt_closure_environment(rt, closure: Value) -> Value {
        if let Some(Object::Closure { environment, .. }) = rt.gc.object(closure) { *environment }
        else { rt.raise("invalid callable"); Value::UNIT }
    }
    fn ril_rt_evidence_push(rt, parent: Value, operation: u64, handler: Value) -> Value {
        rt.gc.alloc(Object::Evidence { parent, operation, handler })
    }
    fn ril_rt_evidence_find(rt, evidence: Value, key: u64) -> Value {
        let mut evidence = evidence;
        while let Some(Object::Evidence { parent, operation, handler }) = rt.gc.object(evidence) {
            if *operation == key { return *handler; }
            evidence = *parent;
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
    let payload = rt.gc.alloc(Object::Str(RilStr::new(error)));
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
    let value = match rt.gc.draft_insertion(target, value) {
        Ok(value) => value,
        Err(message) => return rt.checked(Err(message)),
    };
    let target = rt.gc.draft_read(target).unwrap_or(target);
    let key_text = read_text(rt, key).ok();
    let index = rt.gc.integer(key).and_then(|key| key.to_usize());
    let map_lookup = match rt.gc.object(target) {
        Some(Object::Map(map)) => {
            let hash = rt.gc.bisim_hash(key);
            let existing = map.find_index(hash, |stored| rt.gc.equal(stored, key).unwrap_or(false));
            Some((hash, existing))
        }
        _ => None,
    };
    match rt.gc.object_mut(target) {
        Some(Object::Record(fields)) if let Some(key) = key_text => {
            fields.insert(key, value);
        }
        Some(Object::Array(items) | Object::Tuple(items) | Object::Tag(_, items)) => {
            if let Some(slot) = index.and_then(|i| items.get_mut(i)) {
                *slot = value;
            } else {
                rt.raise("index out of bounds");
            }
        }
        Some(Object::Map(map)) => {
            if let Some((hash, existing)) = map_lookup {
                if let Some(slot) = existing.and_then(|idx| map.value_mut(idx)) {
                    *slot = value;
                } else {
                    map.push_new(hash, key, value);
                }
            }
        }
        _ => rt.raise("invalid destination for object update"),
    }
    Value::UNIT
}

fn load(rt: &mut Runtime, target: Value, key: Value) -> Option<Value> {
    let target = rt.gc.draft_read(target).unwrap_or(target);
    let (slot, value) = match rt.gc.object(target)? {
        Object::Record(fields) => {
            let key = read_text(rt, key).ok()?;
            let value = fields.get(&key).copied()?;
            (DraftSlot::Field(key), value)
        }
        Object::Array(values) | Object::Tuple(values) | Object::Tag(_, values) => {
            let index = rt.gc.integer(key)?.to_usize()?;
            (DraftSlot::Element(index), values.get(index).copied()?)
        }
        Object::Map(map) => {
            let hash = rt.gc.bisim_hash(key);
            let index = map.find_index(hash, |stored| rt.gc.equal(stored, key).unwrap_or(false))?;
            let (_, value) = map.get_entry(index)?;
            (DraftSlot::MapValue(index), value)
        }
        Object::Str(text) => {
            let item = text.scalar_at(rt.gc.integer(key)?.to_usize()?)?.to_string();
            return Some(rt.gc.alloc(Object::Str(RilStr::new(item))));
        }
        Object::Bytes(bytes) => {
            let byte = *bytes.get(rt.gc.integer(key)?.to_usize()?)?;
            return Some(rt.gc.int_i64(i64::from(byte)));
        }
        _ => return None,
    };
    rt.gc.draft_child(target, slot, value)
}

fn compare_sortable(gc: &crate::GcRuntime, a: Value, b: Value) -> std::cmp::Ordering {
    if let (Some(x), Some(y)) = (gc.integer(a), gc.integer(b)) {
        return x.compare(y);
    }
    match (gc.object(a), gc.object(b)) {
        (Some(Object::F64(x)), Some(Object::F64(y))) => {
            f64::from_bits(*x).total_cmp(&f64::from_bits(*y))
        }
        (Some(Object::Str(x)), Some(Object::Str(y))) => x.as_str().cmp(y.as_str()),
        (Some(Object::Bytes(x)), Some(Object::Bytes(y))) => x.cmp(y),
        _ => std::cmp::Ordering::Equal,
    }
}

fn iter_at(rt: &mut Runtime, target: Value, position: Value) -> Option<Value> {
    let target = rt.gc.draft_read(target).unwrap_or(target);
    let Some(Object::Map(map)) = rt.gc.object(target) else {
        return load(rt, target, position);
    };
    let index = rt.gc.integer(position)?.to_usize()?;
    let (key, value) = map.get_entry(index)?;
    rt.gc.pin(key);
    let value = rt.gc.draft_child(target, DraftSlot::MapValue(index), value);
    rt.gc.unpin(key);
    let value = value?;
    Some(rt.gc.alloc(Object::Tuple(vec![key, value])))
}

fn slice(
    rt: &mut Runtime,
    target: Value,
    start: Value,
    end: Value,
    inclusive: bool,
) -> Option<Value> {
    let target = rt.gc.draft_read(target).unwrap_or(target);
    let object = rt.gc.object(target)?;
    let length = match object {
        Object::Str(text) => text.scalar_len(),
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
        Object::Array(items) => {
            let mut values = items.get(start..end)?.to_vec();
            for (index, value) in values.iter_mut().enumerate() {
                *value = rt
                    .gc
                    .draft_child(target, DraftSlot::Element(start + index), *value)?;
            }
            Object::Array(values)
        }
        Object::Bytes(bytes) => Object::Bytes(bytes.get(start..end)?.to_vec()),
        Object::Str(text) => Object::Str(RilStr::new(text.slice_scalars(start, end)?)),
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
