//! Unified dynamic effect handler stack and one-shot delimited continuations (`ctl`).
//!
//! One runtime thread drives all native stacks. Never retain a Rust borrow of
//! `Runtime` across a native call or a `corosensei` stack switch.

#[cfg(not(miri))]
use std::{cell::Cell, collections::BTreeMap};

#[cfg(not(miri))]
use corosensei::{Coroutine, CoroutineResult, Yielder, stack::DefaultStack};

use crate::{Object, Runtime, Value};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum HandlerArmKind {
    Fn,
    CtlCoro,
    CtlTail,
    CtlAbort,
}

impl HandlerArmKind {
    fn is_ctl(self) -> bool {
        self != Self::Fn
    }
}

#[derive(Clone, Debug)]
pub(crate) struct HandlerEntry {
    pub op: u64,
    pub kind: HandlerArmKind,
    pub handler: Value,
}

#[derive(Clone, Debug)]
pub(crate) struct HandlerFrame {
    #[cfg_attr(miri, allow(dead_code))]
    pub prompt_id: u64,
    pub arms: Vec<HandlerEntry>,
}

#[cfg(not(miri))]
enum ResumeMsg {
    Start,
    Value(Value),
    Abort,
}

#[cfg(not(miri))]
enum YieldMsg {
    Perform {
        target_prompt: u64,
        op: u64,
        args: Value,
    },
}

#[cfg(not(miri))]
enum FinishMsg {
    Done(Value),
    Panicked(String),
    Aborted,
    CtlAbort {
        prompt_id: u64,
        op: u64,
        args: Value,
    },
}

#[cfg(not(miri))]
struct ContState {
    coro: Coroutine<ResumeMsg, YieldMsg, FinishMsg>,
    coro_id: u64,
    prompt_id: u64,
    captured_frames: Vec<HandlerFrame>,
    body_thunk: Value,
}

#[derive(Default)]
pub(crate) struct State {
    handler_stack: Vec<HandlerFrame>,
    saved_frames: Vec<Vec<HandlerFrame>>,
    #[cfg_attr(miri, allow(dead_code))]
    next_id: u64,
    #[cfg(not(miri))]
    continuations: BTreeMap<u64, ContState>,
    #[cfg(not(miri))]
    stack_pool: Vec<DefaultStack>,
}

impl State {
    #[cfg(not(miri))]
    fn fresh_id(&mut self) -> u64 {
        self.next_id += 1;
        self.next_id
    }
}

#[cfg(not(miri))]
const MAX_POOLED_STACKS: usize = 64;

#[cfg(not(miri))]
thread_local! {
    static CTL_YIELDER: Cell<*const Yielder<ResumeMsg, YieldMsg>> = const { Cell::new(std::ptr::null()) };
}

pub(crate) fn push_fn_handler(rt: &mut Runtime, op: u64, handler: Value) {
    rt.gc.pin(handler);
    rt.ctl.handler_stack.push(HandlerFrame {
        prompt_id: 0,
        arms: vec![HandlerEntry {
            op,
            kind: HandlerArmKind::Fn,
            handler,
        }],
    });
}

pub(crate) fn push_fn_frame(rt: &mut Runtime, entries: Value) {
    let Some(arms) = decode_arms(rt, entries) else {
        rt.raise("invalid handler frame descriptor");
        return;
    };
    for arm in &arms {
        rt.gc.pin(arm.handler);
    }
    rt.ctl
        .handler_stack
        .push(HandlerFrame { prompt_id: 0, arms });
}

pub(crate) fn pop_handler_frame(rt: &mut Runtime) {
    if let Some(frame) = rt.ctl.handler_stack.pop() {
        for arm in frame.arms {
            rt.gc.unpin(arm.handler);
        }
    }
}

pub(crate) fn enter_fn_handler(rt: &mut Runtime, op: u64) -> Value {
    let found = rt
        .ctl
        .handler_stack
        .iter()
        .enumerate()
        .rev()
        .find_map(|(idx, frame)| {
            frame
                .arms
                .iter()
                .find(|arm| arm.op == op && arm.kind == HandlerArmKind::Fn)
                .map(|arm| (idx, arm.handler))
        });
    let Some((idx, handler)) = found else {
        rt.raise("missing dynamic fn effect handler");
        return Value::UNIT;
    };
    let detached = rt.ctl.handler_stack.split_off(idx);
    rt.ctl.saved_frames.push(detached);
    handler
}

pub(crate) fn leave_fn_handler(rt: &mut Runtime) {
    if let Some(restored) = rt.ctl.saved_frames.pop() {
        rt.ctl.handler_stack.extend(restored);
    }
}

fn decode_arms(rt: &Runtime, entries: Value) -> Option<Vec<HandlerEntry>> {
    let Some(Object::Array(items)) = rt.gc.object(entries) else {
        return None;
    };
    if items.len() % 3 != 0 {
        return None;
    }
    let mut arms = Vec::with_capacity(items.len() / 3);
    for chunk in items.chunks_exact(3) {
        let [op_val, is_ctl_val, handler] = *chunk else {
            return None;
        };
        let op = u64::try_from(op_val.small_int()?).ok()?;
        let kind = if is_ctl_val == Value::FALSE {
            HandlerArmKind::Fn
        } else if is_ctl_val == Value::TRUE {
            HandlerArmKind::CtlCoro
        } else {
            match is_ctl_val.small_int() {
                Some(0) => HandlerArmKind::Fn,
                Some(1) => HandlerArmKind::CtlCoro,
                Some(2) => HandlerArmKind::CtlTail,
                Some(3) => HandlerArmKind::CtlAbort,
                _ => return None,
            }
        };
        arms.push(HandlerEntry { op, kind, handler });
    }
    Some(arms)
}

#[cfg(miri)]
pub(crate) fn with_ctl(rt: &mut Runtime, _entries: Value, _body_thunk: Value) -> Value {
    rt.raise("ctl delimited continuations are not supported under Miri");
    Value::UNIT
}

#[cfg(miri)]
pub(crate) fn with_ctl_fast(rt: &mut Runtime, _entries: Value, _body_thunk: Value) -> Value {
    rt.raise("ctl handlers are not supported under Miri");
    Value::UNIT
}

#[cfg(miri)]
pub(crate) fn perform_ctl(rt: &mut Runtime, _op: u64, _args: Value) -> Value {
    rt.raise("ctl delimited continuations are not supported under Miri");
    Value::UNIT
}

#[cfg(miri)]
pub(crate) fn resume_ctl(rt: &mut Runtime, _k: Value, _arg: Value) -> Value {
    rt.raise("ctl delimited continuations are not supported under Miri");
    Value::UNIT
}

#[cfg(miri)]
pub(crate) fn abort_ctl(rt: &mut Runtime, _k: Value) -> Value {
    rt.raise("ctl delimited continuations are not supported under Miri");
    Value::UNIT
}

#[cfg(not(miri))]
#[allow(
    unsafe_code,
    reason = "corosensei delimited continuation stack switches and generated closure calls"
)]
mod native {
    use super::*;
    use crate::unwind::UnwindState;

    type Raw = *mut Runtime;

    unsafe fn ctx<'a>(raw: Raw) -> &'a mut Runtime {
        // SAFETY: one thread drives all coroutines; no Rust borrow spans a stack switch or native call.
        unsafe { &mut *raw }
    }

    #[derive(Clone, Copy)]
    struct ClosureParts {
        function: *const u8,
        arity: u64,
        env: Value,
    }

    fn closure_parts(rt: &Runtime, value: Value) -> Option<ClosureParts> {
        match rt.gc.object(value) {
            Some(Object::Closure {
                function,
                arity,
                environment,
            }) => Some(ClosureParts {
                function: *function,
                arity: *arity,
                env: *environment,
            }),
            _ => None,
        }
    }

    unsafe fn invoke0(raw: Raw, closure: Value) -> Value {
        // SAFETY: raw is unique and live.
        let Some(parts) = (unsafe { closure_parts(ctx(raw), closure) }) else {
            // SAFETY: raw is unique and live.
            unsafe { ctx(raw) }.raise("expected 0-arg thunk in ctl prompt");
            return Value::UNIT;
        };
        if parts.arity != 0 || parts.function.is_null() {
            // SAFETY: raw is unique and live.
            unsafe { ctx(raw) }.raise("invalid 0-arg thunk in ctl prompt");
            return Value::UNIT;
        }
        // SAFETY: lowered 0-arg Ril closures use the C ABI `(rt, env) -> Value`.
        let f = unsafe {
            std::mem::transmute::<*const u8, extern "C" fn(Raw, Value) -> Value>(parts.function)
        };
        f(raw, parts.env)
    }

    unsafe fn invoke2(raw: Raw, closure: Value, arg0: Value, arg1: Value) -> Value {
        // SAFETY: raw is unique and live.
        let Some(parts) = (unsafe { closure_parts(ctx(raw), closure) }) else {
            // SAFETY: raw is unique and live.
            unsafe { ctx(raw) }.raise("expected 2-arg ctl arm adapter");
            return Value::UNIT;
        };
        if parts.arity != 2 || parts.function.is_null() {
            // SAFETY: raw is unique and live.
            unsafe { ctx(raw) }.raise("invalid 2-arg ctl arm adapter");
            return Value::UNIT;
        }
        // SAFETY: lowered 2-arg Ril closures use the C ABI `(rt, env, arg0, arg1) -> Value`.
        let f = unsafe {
            std::mem::transmute::<*const u8, extern "C" fn(Raw, Value, Value, Value) -> Value>(
                parts.function,
            )
        };
        f(raw, parts.env, arg0, arg1)
    }

    fn stack_size() -> usize {
        std::env::var("RIL_CTL_STACK")
            .ok()
            .and_then(|n| n.parse::<usize>().ok())
            .unwrap_or(1024 * 1024)
            .max(64 * 1024)
    }

    fn cleanup_finished(rt: &mut Runtime, cont: ContState) {
        rt.gc.clear_coro_frames(cont.coro_id);
        rt.gc.unpin(cont.body_thunk);
        for frame in cont.captured_frames {
            for arm in frame.arms {
                rt.gc.unpin(arm.handler);
            }
        }
        if rt.ctl.stack_pool.len() < MAX_POOLED_STACKS {
            rt.ctl.stack_pool.push(cont.coro.into_stack());
        }
    }

    unsafe fn drive_prompt(raw: Raw, mut cont: ContState, mut msg: ResumeMsg) -> Value {
        loop {
            let (base_depth, prev_coro) = {
                // SAFETY: no coroutine is executing while we splice frames.
                let rt = unsafe { ctx(raw) };
                let base_depth = rt.ctl.handler_stack.len();
                rt.ctl.handler_stack.append(&mut cont.captured_frames);
                let prev_coro = rt.gc.switch_coro(cont.coro_id);
                (base_depth, prev_coro)
            };

            let prev_yielder = CTL_YIELDER.with(Cell::get);
            let step = cont.coro.resume(msg);
            CTL_YIELDER.with(|slot| slot.set(prev_yielder));

            {
                // SAFETY: coroutine just suspended or returned.
                let rt = unsafe { ctx(raw) };
                rt.gc.switch_coro(prev_coro);
                cont.captured_frames = rt.ctl.handler_stack.split_off(base_depth);
            }

            match step {
                CoroutineResult::Return(finish) => {
                    // SAFETY: coroutine finished; reclaim stack and pins.
                    if let FinishMsg::CtlAbort {
                        prompt_id,
                        op,
                        args,
                    } = finish
                    {
                        if prompt_id == cont.prompt_id {
                            let arm_handler = cont.captured_frames.first().and_then(|frame| {
                                frame
                                    .arms
                                    .iter()
                                    .find(|arm| {
                                        arm.op == op && arm.kind == HandlerArmKind::CtlAbort
                                    })
                                    .map(|arm| arm.handler)
                            });
                            let result = if let Some(handler) = arm_handler {
                                // SAFETY: invoke 2-arg arm adapter with parent handler stack active.
                                unsafe { invoke2(raw, handler, args, Value::UNIT) }
                            } else {
                                // SAFETY: raw is live.
                                unsafe { ctx(raw) }.raise("missing abort ctl arm in target prompt");
                                Value::UNIT
                            };
                            // SAFETY: arm returned; unpin args and reclaim finished prompt.
                            let rt = unsafe { ctx(raw) };
                            rt.gc.unpin(args);
                            cleanup_finished(rt, cont);
                            return result;
                        }
                        // SAFETY: raw is live and unique while forwarding abort to outer prompt.
                        let rt = unsafe { ctx(raw) };
                        cleanup_finished(rt, cont);
                        rt.resume_ctl_abort(prompt_id, op, args);
                        return Value::UNIT;
                    }
                    // SAFETY: coroutine finished; raw is live and unique.
                    let rt = unsafe { ctx(raw) };
                    cleanup_finished(rt, cont);
                    return match finish {
                        FinishMsg::Done(value) => value,
                        FinishMsg::Panicked(message) => {
                            rt.raise(message);
                            Value::UNIT
                        }
                        FinishMsg::Aborted => Value::UNIT,
                        FinishMsg::CtlAbort { .. } => Value::UNIT,
                    };
                }
                CoroutineResult::Yield(YieldMsg::Perform {
                    target_prompt,
                    op,
                    args,
                }) => {
                    if target_prompt == cont.prompt_id {
                        let arm_handler = cont.captured_frames.first().and_then(|frame| {
                            frame
                                .arms
                                .iter()
                                .find(|arm| arm.op == op && arm.kind.is_ctl())
                                .map(|arm| arm.handler)
                        });
                        let Some(arm_handler) = arm_handler else {
                            // SAFETY: prompt mismatch error.
                            let rt = unsafe { ctx(raw) };
                            rt.gc.unpin(args);
                            cleanup_finished(rt, cont);
                            rt.raise("missing ctl arm in target prompt");
                            return Value::UNIT;
                        };
                        let coro_id = cont.coro_id;
                        let k = {
                            // SAFETY: store continuation and allocate GC handle while args is pinned.
                            let rt = unsafe { ctx(raw) };
                            rt.ctl.continuations.insert(coro_id, cont);
                            rt.gc.alloc(Object::Continuation(coro_id))
                        };
                        // SAFETY: invoke 2-arg arm adapter with parent handler stack active.
                        let result = unsafe { invoke2(raw, arm_handler, args, k) };
                        // SAFETY: arm returned; unpin args pinned at perform_ctl.
                        unsafe { ctx(raw) }.gc.unpin(args);
                        return result;
                    }
                    // Target is an outer prompt: forward the yield up our enclosing coroutine!
                    let outer_ptr = CTL_YIELDER.with(Cell::get);
                    if outer_ptr.is_null() {
                        // SAFETY: no enclosing prompt coroutine exists.
                        let rt = unsafe { ctx(raw) };
                        rt.gc.unpin(args);
                        cleanup_finished(rt, cont);
                        rt.raise("missing enclosing ctl prompt");
                        return Value::UNIT;
                    }
                    // SAFETY: outer_ptr is the live yielder of our immediate enclosing coroutine.
                    let outer_yielder = unsafe { &*outer_ptr };
                    let forwarded = outer_yielder.suspend(YieldMsg::Perform {
                        target_prompt,
                        op,
                        args,
                    });
                    CTL_YIELDER.with(|slot| slot.set(outer_ptr));
                    msg = forwarded;
                }
            }
        }
    }

    pub(super) unsafe fn with_ctl_raw(raw: Raw, entries: Value, body_thunk: Value) -> Value {
        let (prompt_id, coro_id, arms, stack) = {
            // SAFETY: raw is live and unique.
            let rt = unsafe { ctx(raw) };
            let Some(arms) = decode_arms(rt, entries) else {
                rt.raise("invalid ctl handler frame descriptor");
                return Value::UNIT;
            };
            let stack = match rt.ctl.stack_pool.pop() {
                Some(stack) => stack,
                None => match DefaultStack::new(stack_size()) {
                    Ok(stack) => stack,
                    Err(err) => {
                        rt.raise(format!("failed to allocate ctl stack: {err}"));
                        return Value::UNIT;
                    }
                },
            };
            for arm in &arms {
                rt.gc.pin(arm.handler);
            }
            rt.gc.pin(body_thunk);
            let prompt_id = rt.ctl.fresh_id();
            let coro_id = rt.ctl.fresh_id();
            (prompt_id, coro_id, arms, stack)
        };

        let coro = Coroutine::with_stack(stack, move |yielder, first_msg| {
            if matches!(first_msg, ResumeMsg::Abort) {
                return FinishMsg::Aborted;
            }
            CTL_YIELDER.with(|slot| slot.set(yielder));
            // SAFETY: body_thunk was validated and pinned above.
            let output = unsafe { invoke0(raw, body_thunk) };
            CTL_YIELDER.with(|slot| slot.set(std::ptr::null()));
            // SAFETY: coroutine finished executing generated code.
            let rt = unsafe { ctx(raw) };
            match rt.take_unwind() {
                UnwindState::None => FinishMsg::Done(output),
                UnwindState::Panic(msg) => FinishMsg::Panicked(msg),
                UnwindState::Abort => FinishMsg::Aborted,
                UnwindState::CtlAbort {
                    prompt_id,
                    op,
                    args,
                } => FinishMsg::CtlAbort {
                    prompt_id,
                    op,
                    args,
                },
            }
        });

        let cont = ContState {
            coro,
            coro_id,
            prompt_id,
            captured_frames: vec![HandlerFrame { prompt_id, arms }],
            body_thunk,
        };
        // SAFETY: drive_prompt manages GC stack switching and frame splicing.
        unsafe { drive_prompt(raw, cont, ResumeMsg::Start) }
    }

    pub(super) unsafe fn with_ctl_fast_raw(raw: Raw, entries: Value, body_thunk: Value) -> Value {
        let prompt_id = {
            // SAFETY: raw is live and unique.
            let rt = unsafe { ctx(raw) };
            let Some(arms) = decode_arms(rt, entries) else {
                rt.raise("invalid ctl handler frame descriptor");
                return Value::UNIT;
            };
            for arm in &arms {
                rt.gc.pin(arm.handler);
            }
            rt.gc.pin(body_thunk);
            let prompt_id = rt.ctl.fresh_id();
            rt.ctl.handler_stack.push(HandlerFrame { prompt_id, arms });
            prompt_id
        };
        // SAFETY: body_thunk is pinned and runs directly on the current native stack.
        let output = unsafe { invoke0(raw, body_thunk) };
        let (frame, abort_hit) = {
            // SAFETY: raw is live and unique.
            let rt = unsafe { ctx(raw) };
            rt.gc.unpin(body_thunk);
            let frame = rt.ctl.handler_stack.pop();
            let abort_hit = rt.take_ctl_abort(prompt_id);
            (frame, abort_hit)
        };
        if let Some((op, args)) = abort_hit {
            let arm_handler = frame.as_ref().and_then(|f| {
                f.arms
                    .iter()
                    .find(|arm| arm.op == op && arm.kind == HandlerArmKind::CtlAbort)
                    .map(|arm| arm.handler)
            });
            let result = if let Some(handler) = arm_handler {
                // SAFETY: parent handler stack is active; invoke 2-arg adapter directly.
                unsafe { invoke2(raw, handler, args, Value::UNIT) }
            } else {
                // SAFETY: raw is live.
                unsafe { ctx(raw) }.raise("missing abort ctl arm in target prompt");
                Value::UNIT
            };
            // SAFETY: raw is live.
            let rt = unsafe { ctx(raw) };
            rt.gc.unpin(args);
            if let Some(frame) = frame {
                for arm in frame.arms {
                    rt.gc.unpin(arm.handler);
                }
            }
            return result;
        }
        if let Some(frame) = frame {
            // SAFETY: raw is live.
            let rt = unsafe { ctx(raw) };
            for arm in frame.arms {
                rt.gc.unpin(arm.handler);
            }
        }
        output
    }

    pub(super) unsafe fn perform_ctl_raw(raw: Raw, op: u64, args: Value) -> Value {
        let found = {
            // SAFETY: raw is live and unique.
            let rt = unsafe { ctx(raw) };
            rt.ctl
                .handler_stack
                .iter()
                .enumerate()
                .rev()
                .find_map(|(idx, frame)| {
                    frame
                        .arms
                        .iter()
                        .find(|arm| arm.op == op && arm.kind.is_ctl())
                        .map(|arm| (idx, frame.prompt_id, arm.kind, arm.handler))
                })
        };
        let Some((idx, prompt_id, kind, arm_handler)) = found else {
            // SAFETY: raw is live.
            unsafe { ctx(raw) }.raise("missing dynamic ctl effect handler");
            return Value::UNIT;
        };
        match kind {
            HandlerArmKind::CtlTail => {
                {
                    // SAFETY: detach target frame and inner frames so arm runs against parent stack.
                    let rt = unsafe { ctx(raw) };
                    rt.gc.pin(args);
                    let detached = rt.ctl.handler_stack.split_off(idx);
                    rt.ctl.saved_frames.push(detached);
                }
                // SAFETY: invoke tail-resumptive 2-arg adapter directly on current native stack.
                let result = unsafe { invoke2(raw, arm_handler, args, Value::UNIT) };
                {
                    // SAFETY: restore detached frames and unpin args.
                    let rt = unsafe { ctx(raw) };
                    if let Some(restored) = rt.ctl.saved_frames.pop() {
                        rt.ctl.handler_stack.extend(restored);
                    }
                    rt.gc.unpin(args);
                }
                return result;
            }
            HandlerArmKind::CtlAbort => {
                // SAFETY: mark runtime unwinding to target prompt_id so defers run LIFO.
                unsafe { ctx(raw) }.begin_ctl_abort(prompt_id, op, args);
                return Value::UNIT;
            }
            HandlerArmKind::CtlCoro => {
                if prompt_id == 0 {
                    // SAFETY: raw is live.
                    unsafe { ctx(raw) }.raise("missing dynamic ctl effect handler");
                    return Value::UNIT;
                }
                // SAFETY: pin args across yield.
                unsafe { ctx(raw) }.gc.pin(args);
            }
            HandlerArmKind::Fn => {
                // SAFETY: unreachable due to is_ctl() filter.
                unsafe { ctx(raw) }.raise("expected ctl effect handler");
                return Value::UNIT;
            }
        }
        let target_prompt = prompt_id;
        let ptr = CTL_YIELDER.with(Cell::get);
        if ptr.is_null() {
            // SAFETY: raw is live.
            let rt = unsafe { ctx(raw) };
            rt.gc.unpin(args);
            rt.raise("ctl operation performed outside ctl prompt");
            return Value::UNIT;
        }
        // SAFETY: ptr is installed by the active coroutine's entry frame.
        let yielder = unsafe { &*ptr };
        let resumed = yielder.suspend(YieldMsg::Perform {
            target_prompt,
            op,
            args,
        });
        CTL_YIELDER.with(|slot| slot.set(ptr));
        match resumed {
            ResumeMsg::Value(value) => {
                // SAFETY: unpin resume value pinned by ril_rt_resume_ctl.
                unsafe { ctx(raw) }.gc.unpin(value);
                value
            }
            ResumeMsg::Abort => {
                // SAFETY: mark runtime as unwinding via UNWIND_ABORT so defers run LIFO.
                unsafe { ctx(raw) }.begin_abort();
                Value::UNIT
            }
            ResumeMsg::Start => {
                // SAFETY: unreachable protocol violation.
                unsafe { ctx(raw) }.raise("unexpected Start resume on suspended continuation");
                Value::UNIT
            }
        }
    }

    pub(super) unsafe fn resume_ctl_raw(raw: Raw, k: Value, arg: Value) -> Value {
        let cont = {
            // SAFETY: raw is live and unique.
            let rt = unsafe { ctx(raw) };
            let Some(&Object::Continuation(coro_id)) = rt.gc.object(k) else {
                rt.raise("expected ctl continuation");
                return Value::UNIT;
            };
            let Some(cont) = rt.ctl.continuations.remove(&coro_id) else {
                rt.raise("ctl continuation was already consumed");
                return Value::UNIT;
            };
            rt.gc.pin(arg);
            cont
        };
        // SAFETY: drive_prompt resumes the continuation with `arg` pinned until received.
        unsafe { drive_prompt(raw, cont, ResumeMsg::Value(arg)) }
    }

    pub(super) unsafe fn abort_ctl_raw(raw: Raw, k: Value) -> Value {
        let cont = {
            // SAFETY: raw is live and unique.
            let rt = unsafe { ctx(raw) };
            let Some(&Object::Continuation(coro_id)) = rt.gc.object(k) else {
                rt.raise("expected ctl continuation in unwind_ctl");
                return Value::UNIT;
            };
            let Some(cont) = rt.ctl.continuations.remove(&coro_id) else {
                rt.raise("ctl continuation was already consumed");
                return Value::UNIT;
            };
            cont
        };
        // SAFETY: drive_prompt unwinds the continuation's defers LIFO via UNWIND_ABORT.
        unsafe { drive_prompt(raw, cont, ResumeMsg::Abort) }
    }
}

#[cfg(not(miri))]
#[allow(
    unsafe_code,
    reason = "entry points into native corosensei ctl runtime"
)]
pub(crate) fn with_ctl(rt: &mut Runtime, entries: Value, body_thunk: Value) -> Value {
    // SAFETY: rt is the unique live Runtime for this thread.
    unsafe { native::with_ctl_raw(std::ptr::from_mut(rt), entries, body_thunk) }
}

#[cfg(not(miri))]
#[allow(
    unsafe_code,
    reason = "entry points into native zero-stack ctl runtime"
)]
pub(crate) fn with_ctl_fast(rt: &mut Runtime, entries: Value, body_thunk: Value) -> Value {
    // SAFETY: rt is the unique live Runtime for this thread.
    unsafe { native::with_ctl_fast_raw(std::ptr::from_mut(rt), entries, body_thunk) }
}

#[cfg(not(miri))]
#[allow(
    unsafe_code,
    reason = "entry points into native corosensei ctl runtime"
)]
pub(crate) fn perform_ctl(rt: &mut Runtime, op: u64, args: Value) -> Value {
    // SAFETY: rt is the unique live Runtime for this thread.
    unsafe { native::perform_ctl_raw(std::ptr::from_mut(rt), op, args) }
}

#[cfg(not(miri))]
#[allow(
    unsafe_code,
    reason = "entry points into native corosensei ctl runtime"
)]
pub(crate) fn resume_ctl(rt: &mut Runtime, k: Value, arg: Value) -> Value {
    // SAFETY: rt is the unique live Runtime for this thread.
    unsafe { native::resume_ctl_raw(std::ptr::from_mut(rt), k, arg) }
}

#[cfg(not(miri))]
#[allow(
    unsafe_code,
    reason = "entry points into native corosensei ctl runtime"
)]
pub(crate) fn abort_ctl(rt: &mut Runtime, k: Value) -> Value {
    // SAFETY: rt is the unique live Runtime for this thread.
    unsafe { native::abort_ctl_raw(std::ptr::from_mut(rt), k) }
}
