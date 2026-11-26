use std::{
    collections::BTreeMap,
    time::{Duration, Instant},
};

use num_traits::ToPrimitive;

use crate::{Object, Runtime, Value};

use super::{Completion, Event, Raw, Task, context, error, start, tag, wait, wait_task};

enum First {
    Task(Task, Completion),
    Expired,
    Cancelled,
}

fn first(raw: Raw, choices: &[Task], deadline: Option<Instant>) -> First {
    loop {
        // SAFETY: only the current task accesses the runtime, and this borrow ends before wait.
        let rt = unsafe { context(raw) };
        if let Some(id) = rt
            .fiber
            .completion_order
            .iter()
            .copied()
            .find(|id| choices.contains(id))
            && let Some(completed) = rt.fiber.tasks.remove(&id)
        {
            rt.fiber.completion_order.retain(|task| *task != id);
            return First::Task(id, completed);
        }
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return First::Expired;
        }
        if !wait(raw, Event::Change(deadline)) {
            return First::Cancelled;
        }
    }
}

fn cancel_all(raw: Raw, tasks: &[Task]) {
    if tasks.is_empty() {
        return;
    }
    // SAFETY: suspend the current task's panic while it drains cancelled siblings.
    let rt = unsafe { context(raw) };
    let panic = rt.take_panic();
    let owner = rt.fiber.active;
    rt.fiber.cancelled.extend(tasks);
    *rt.fiber.shielded.entry(owner).or_default() += 1;
    for &task in tasks {
        if let Some(Completion::Finished(value)) = wait_task(raw, task) {
            // SAFETY: after waiting this task again owns the runtime.
            unsafe { context(raw) }.gc.unpin(value);
        }
    }
    // SAFETY: the draining task is active.
    let rt = unsafe { context(raw) };
    if let Some(depth) = rt.fiber.shielded.get_mut(&owner) {
        if *depth <= 1 {
            rt.fiber.shielded.remove(&owner);
        } else {
            *depth -= 1;
        }
    }
    if let Some(panic) = panic {
        rt.raise(panic);
    }
}

fn value(rt: &mut Runtime, status: Completion) -> Option<Value> {
    match status {
        Completion::Finished(value) => {
            rt.gc.unpin(value);
            Some(value)
        }
        Completion::Panicked(message) => {
            rt.raise(message);
            None
        }
        Completion::Cancelled => {
            rt.raise("child task cancelled");
            None
        }
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_fiber_supervise(raw: Raw, work: Value) -> Value {
    // SAFETY: queue only; release the runtime reference before joining.
    let task = start(unsafe { context(raw) }, raw, work, None);
    let done = wait_task(raw, task);
    // SAFETY: now back in the caller's stack.
    let rt = unsafe { context(raw) };
    let fault = match done {
        Some(Completion::Finished(value)) => {
            rt.gc.unpin(value);
            return tag(rt, "Ok", Some(value));
        }
        Some(Completion::Panicked(message)) => {
            let detail = rt.gc.alloc(Object::Str(crate::RilStr::new(message)));
            tag(rt, "Panicked", Some(detail))
        }
        Some(Completion::Cancelled) => tag(rt, "Cancelled", None),
        None => {
            cancel_all(raw, &[task]);
            return Value::UNIT;
        }
    };
    tag(rt, "Err", Some(fault))
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_fiber_timeout(raw: Raw, duration: Value, work: Value) -> Value {
    // SAFETY: borrow only while computing the deadline and enqueueing work.
    let rt = unsafe { context(raw) };
    let Some(duration) = rt
        .gc
        .integer(duration)
        .and_then(|duration| duration.to_u64())
        .and_then(|ms| Instant::now().checked_add(Duration::from_millis(ms)))
    else {
        return error(rt, "invalid timeout");
    };
    let task = start(rt, raw, work, None);
    match first(raw, &[task], Some(duration)) {
        First::Task(_, status) => {
            // SAFETY: the calling task is active.
            let rt = unsafe { context(raw) };
            value(rt, status).map_or(Value::UNIT, |value| tag(rt, "Ok", Some(value)))
        }
        First::Expired => {
            cancel_all(raw, &[task]);
            // SAFETY: the cancelling task is active after draining.
            let rt = unsafe { context(raw) };
            let fault = tag(rt, "Elapsed", None);
            tag(rt, "Err", Some(fault))
        }
        First::Cancelled => {
            cancel_all(raw, &[task]);
            Value::UNIT
        }
    }
}

fn is_err(rt: &Runtime, value: Value) -> bool {
    matches!(rt.gc.object(value), Some(Object::Tag(tag, _)) if tag == "Err")
}

fn ok_payload(rt: &Runtime, value: Value) -> Option<Value> {
    match rt.gc.object(value) {
        Some(Object::Tag(tag, items)) if tag == "Ok" => items.first().copied(),
        _ => None,
    }
}

fn pair(raw: Raw, left: Value, right: Value, mode: Pair) -> Value {
    // SAFETY: this borrow ends before entering a wait.
    let rt = unsafe { context(raw) };
    let a = start(rt, raw, left, None);
    let b = start(rt, raw, right, None);
    let First::Task(id, first_value) = first(raw, &[a, b], None) else {
        cancel_all(raw, &[a, b]);
        return Value::UNIT;
    };
    let other = if id == a { b } else { a };
    if mode == Pair::Race {
        cancel_all(raw, &[other]);
        // SAFETY: stack switches in cancellation have finished.
        return value(unsafe { context(raw) }, first_value).unwrap_or(Value::UNIT);
    }
    // SAFETY: the joining task is active.
    let rt = unsafe { context(raw) };
    let Some(first_value) = value(rt, first_value) else {
        cancel_all(raw, &[other]);
        return Value::UNIT;
    };
    rt.gc.pin(first_value);
    if mode == Pair::TryZip && is_err(rt, first_value) {
        cancel_all(raw, &[other]);
        // SAFETY: completion returned to the caller's stack.
        unsafe { context(raw) }.gc.unpin(first_value);
        return first_value;
    }
    let second = wait_task(raw, other);
    // SAFETY: the waiting task is active.
    let rt = unsafe { context(raw) };
    rt.gc.unpin(first_value);
    let Some(completed) = second else {
        cancel_all(raw, &[other]);
        return Value::UNIT;
    };
    let Some(second) = value(rt, completed) else {
        return Value::UNIT;
    };
    let (a, b) = if id == a {
        (first_value, second)
    } else {
        (second, first_value)
    };
    let (a, b) = if mode == Pair::TryZip {
        if is_err(rt, second) {
            return second;
        }
        match (ok_payload(rt, a), ok_payload(rt, b)) {
            (Some(a), Some(b)) => (a, b),
            _ => return error(rt, "try_zip expects Result payloads"),
        }
    } else {
        (a, b)
    };
    let pair = rt.gc.alloc(Object::Record(BTreeMap::from([
        ("first".into(), a),
        ("second".into(), b),
    ])));
    if mode == Pair::TryZip {
        tag(rt, "Ok", Some(pair))
    } else {
        pair
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Pair {
    Zip,
    TryZip,
    Race,
}

#[unsafe(no_mangle)]
extern "C" fn ril_fiber_zip(raw: Raw, a: Value, b: Value) -> Value {
    pair(raw, a, b, Pair::Zip)
}

#[unsafe(no_mangle)]
extern "C" fn ril_fiber_try_zip(raw: Raw, a: Value, b: Value) -> Value {
    pair(raw, a, b, Pair::TryZip)
}

#[unsafe(no_mangle)]
extern "C" fn ril_fiber_race(raw: Raw, a: Value, b: Value) -> Value {
    pair(raw, a, b, Pair::Race)
}

fn map(raw: Raw, array: Value, callback: Value, fallible: bool) -> Value {
    // SAFETY: once the jobs are created, the runtime borrow ends before waiting.
    let rt = unsafe { context(raw) };
    let Some(Object::Array(values)) = rt.gc.object(array) else {
        return error(rt, "fiber map requires an array");
    };
    let values = values.clone();
    let tasks: Vec<_> = values
        .into_iter()
        .map(|item| start(rt, raw, callback, Some(item)))
        .collect();
    let mut pending = tasks.clone();
    let mut output = BTreeMap::new();
    while !pending.is_empty() {
        let First::Task(task, result) = first(raw, &pending, None) else {
            break;
        };
        pending.retain(|id| *id != task);
        // SAFETY: the collecting task is active.
        let rt = unsafe { context(raw) };
        let Some(item) = value(rt, result) else { break };
        if fallible && is_err(rt, item) {
            rt.gc.pin(item);
            cancel_all(raw, &pending);
            // SAFETY: return to the caller's stack after cancellation.
            let rt = unsafe { context(raw) };
            for prior in output.into_values() {
                rt.gc.unpin(prior);
            }
            rt.gc.unpin(item);
            return item;
        }
        let item = if fallible {
            ok_payload(rt, item).unwrap_or(Value::UNIT)
        } else {
            item
        };
        rt.gc.pin(item);
        output.insert(task, item);
    }
    cancel_all(raw, &pending);
    // SAFETY: no stack switch occurs while assembling the result.
    let rt = unsafe { context(raw) };
    let result: Vec<_> = tasks
        .iter()
        .filter_map(|task| output.get(task).copied())
        .collect();
    for &item in &result {
        rt.gc.unpin(item);
    }
    if result.len() != tasks.len() {
        return Value::UNIT;
    }
    let result = rt.gc.alloc(Object::Array(result));
    if fallible {
        tag(rt, "Ok", Some(result))
    } else {
        result
    }
}

#[unsafe(no_mangle)]
extern "C" fn ril_fiber_map(raw: Raw, array: Value, callback: Value) -> Value {
    map(raw, array, callback, false)
}

#[unsafe(no_mangle)]
extern "C" fn ril_fiber_try_map(raw: Raw, array: Value, callback: Value) -> Value {
    map(raw, array, callback, true)
}

pub(super) fn symbols() -> [(&'static str, *const u8); 7] {
    [
        ("ril_fiber_supervise", ril_fiber_supervise as *const u8),
        ("ril_fiber_timeout", ril_fiber_timeout as *const u8),
        ("ril_fiber_zip", ril_fiber_zip as *const u8),
        ("ril_fiber_try_zip", ril_fiber_try_zip as *const u8),
        ("ril_fiber_race", ril_fiber_race as *const u8),
        ("ril_fiber_map", ril_fiber_map as *const u8),
        ("ril_fiber_try_map", ril_fiber_try_map as *const u8),
    ]
}
