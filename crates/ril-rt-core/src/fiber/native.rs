//! One runtime thread drives all native stacks. Never retain a Rust borrow of the
//! runtime across a native call or a stack switch.

use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet, VecDeque},
    time::{Duration, Instant},
};

use corosensei::{Coroutine, CoroutineResult, Yielder, stack::DefaultStack};
use num_traits::ToPrimitive;

use super::{Channel, Completion, Event, FiberBackend, Ready, Scope, Step, Task};
use crate::{Object, Runtime, Value};

type Raw = *mut Runtime;

#[derive(Default)]
pub(crate) struct State {
    active: Task,
    next: u64,
    running: bool,
    pending: VecDeque<(Task, Job)>,
    completion_order: VecDeque<Task>,
    tasks: BTreeMap<Task, Completion>,
    scopes: BTreeMap<Scope, Vec<Task>>,
    cancelled: BTreeSet<Task>,
    wake: BTreeSet<Channel>,
    channels: BTreeMap<Channel, Pipe>,
    shielded: BTreeMap<Task, usize>,
}

impl State {
    fn id(&mut self) -> u64 {
        self.next += 1;
        self.next
    }

    fn cancelled(&self) -> bool {
        self.cancelled.contains(&self.active)
            && self.shielded.get(&self.active).copied().unwrap_or(0) == 0
    }
}

struct Pipe {
    cap: Option<usize>,
    queued: VecDeque<Value>,
    senders: usize,
    receiver: bool,
}

thread_local! {
    static SUSPEND: Cell<*const Yielder<(), Event>> = const { Cell::new(std::ptr::null()) };
}

unsafe fn context<'a>(raw: Raw) -> &'a mut Runtime {
    // SAFETY: all accesses use the context from a live generated call. No access spans a stack switch.
    unsafe { &mut *raw }
}

fn suspend(event: Event) -> bool {
    SUSPEND.with(|slot| {
        let ptr = slot.get();
        if ptr.is_null() {
            return false;
        }
        // SAFETY: the active coroutine installs this yielder before running its body.
        // Its stack remains alive until the scheduler finishes the body.
        let yielder = unsafe { &*ptr };
        yielder.suspend(event);
        slot.set(ptr);
        true
    })
}

#[derive(Clone, Copy)]
struct Closure {
    function: u64,
    arity: u64,
    evidence: Value,
    env: Value,
}

fn closure(runtime: &Runtime, value: Value) -> Option<Closure> {
    match runtime.gc.object(value) {
        Some(Object::Closure {
            function,
            arity,
            evidence,
            environment,
        }) => Some(Closure {
            function: *function,
            arity: *arity,
            evidence: *evidence,
            env: *environment,
        }),
        _ => None,
    }
}

unsafe fn invoke(raw: Raw, value: Value, arguments: Option<Value>) -> Value {
    // SAFETY: raw is owned by the scheduler or generated caller.
    let Some(closure) = (unsafe { closure(context(raw), value) }) else {
        // SAFETY: same unique runtime.
        unsafe { context(raw) }.raise("expected callable in fiber operation");
        return Value::UNIT;
    };
    if closure.arity != u64::from(arguments.is_some()) {
        // SAFETY: no generated callee was invoked on this path.
        unsafe { context(raw) }.raise("incorrect fiber callback arity");
        return Value::UNIT;
    }
    let Ok(address) = usize::try_from(closure.function) else {
        return Value::UNIT;
    };
    let address = std::ptr::with_exposed_provenance::<u8>(address);
    if let Some(arg) = arguments {
        // SAFETY: lowered scope bodies have the closure ABI with one Scope argument.
        let run = unsafe {
            std::mem::transmute::<*const u8, extern "C" fn(Raw, Value, Value, Value) -> Value>(
                address,
            )
        };
        run(raw, closure.evidence, closure.env, arg)
    } else {
        // SAFETY: lowered run and spawn actions have the zero-argument closure ABI.
        let run = unsafe {
            std::mem::transmute::<*const u8, extern "C" fn(Raw, Value, Value) -> Value>(address)
        };
        run(raw, closure.evidence, closure.env)
    }
}

struct Job {
    runtime: Raw,
    callback: Value,
    argument: Option<Value>,
}

struct StackBackend {
    stack_size: usize,
    jobs: BTreeMap<Task, Coroutine<(), Event, Completion>>,
}

impl FiberBackend for StackBackend {
    type Job = Job;

    fn create(&mut self, task: Task, job: Job) -> Result<(), String> {
        let stack = DefaultStack::new(self.stack_size).map_err(|error| error.to_string())?;
        let coro = Coroutine::with_stack(stack, move |yielder, ()| {
            let Job {
                runtime,
                callback,
                argument,
            } = job;
            // SAFETY: the raw context is owned by this run, which drains all its tasks before returning.
            if unsafe { context(runtime) }.fiber.cancelled() {
                return Completion::Cancelled;
            }
            SUSPEND.with(|entry| entry.set(yielder));
            // SAFETY: spawn and run validate the zero-argument callable ABI before lowering.
            let output = unsafe { invoke(runtime, callback, argument) };
            SUSPEND.with(|entry| entry.set(std::ptr::null()));
            // SAFETY: this coroutine is the only running task at this point.
            let runtime = unsafe { context(runtime) };
            match runtime.take_panic() {
                Some(_) if runtime.fiber.cancelled() => Completion::Cancelled,
                Some(message) => Completion::Panicked(message),
                None => Completion::Finished(output),
            }
        });
        self.jobs.insert(task, coro);
        Ok(())
    }

    fn resume(&mut self, task: Task) -> Result<Step, String> {
        let coro = self.jobs.get_mut(&task).ok_or("unknown scheduled task")?;
        let result = coro.resume(());
        Ok(match result {
            CoroutineResult::Yield(event) => Step::Suspended(event),
            CoroutineResult::Return(value) => {
                self.jobs.remove(&task);
                Step::Complete(value)
            }
        })
    }
}

unsafe fn schedule(raw: Raw, action: Value) -> Result<Value, String> {
    // SAFETY: the generated caller owns one live context throughout scheduling.
    let state = unsafe { context(raw) };
    if state.fiber.running {
        return Err("nested Fiber::run".into());
    }
    state.fiber.running = true;
    let root = start(state, raw, action, None);
    let stack_size = std::env::var("RIL_FIBER_STACK")
        .ok()
        .and_then(|n| n.parse::<usize>().ok())
        .unwrap_or(1024 * 1024)
        .max(64 * 1024);
    let mut backend = StackBackend {
        stack_size,
        jobs: BTreeMap::new(),
    };
    let mut ready = Ready::default();
    let mut inputs = BTreeMap::new();
    let mut deadlock = false;
    loop {
        // SAFETY: no coroutine is running while scheduling.
        let rt = unsafe { context(raw) };
        enqueue(rt, &mut backend, &mut ready, &mut inputs);
        let wake = std::mem::take(&mut rt.fiber.wake);
        ready.signal(|event| matches!(event, Event::Channel(channel) if wake.contains(&channel)));
        for &task in &rt.fiber.cancelled {
            ready.wake(task);
        }
        let now = Instant::now();
        ready.signal(
            |event| matches!(event, Event::Sleep(when) | Event::Change(Some(when)) if when <= now),
        );
        let Some(task) = ready.next() else {
            if let Some(when) = ready.nearest_timer() {
                std::thread::sleep(when.saturating_duration_since(now));
                continue;
            }
            let active: Vec<_> = ready.active().collect();
            if active.is_empty() {
                break;
            }
            deadlock = true;
            rt.fiber.cancelled.extend(active);
            continue;
        };
        rt.fiber.active = task;
        rt.gc.switch_fiber(task);
        let step = backend.resume(task)?;
        // SAFETY: the coroutine has suspended or returned, so Rust can access the context again.
        let rt = unsafe { context(raw) };
        enqueue(rt, &mut backend, &mut ready, &mut inputs);
        match step {
            Step::Suspended(event) => ready.suspend(task, event),
            Step::Complete(completion) => {
                if let Some((callback, argument)) = inputs.remove(&task) {
                    rt.gc.unpin(callback);
                    if let Some(argument) = argument {
                        rt.gc.unpin(argument);
                    }
                }
                if let Completion::Finished(value) = completion {
                    rt.gc.pin(value);
                }
                rt.fiber.tasks.insert(task, completion);
                rt.fiber.completion_order.push_back(task);
                ready.complete(task);
            }
        }
    }
    // SAFETY: all task stacks have returned and the outer caller becomes active.
    let rt = unsafe { context(raw) };
    rt.fiber.active = 0;
    rt.fiber.running = false;
    rt.gc.switch_fiber(0);
    let result = rt.fiber.tasks.remove(&root);
    let leftovers = std::mem::take(&mut rt.fiber.tasks);
    for complete in leftovers.into_values() {
        if let Completion::Finished(value) = complete {
            rt.gc.unpin(value);
        }
    }
    rt.fiber.cancelled.clear();
    rt.fiber.completion_order.clear();
    rt.fiber.shielded.clear();
    if deadlock {
        if let Some(Completion::Finished(value)) = result {
            rt.gc.unpin(value);
        }
        return Err("fiber deadlock".into());
    }
    match result {
        Some(Completion::Finished(value)) => {
            rt.gc.unpin(value);
            Ok(value)
        }
        Some(Completion::Panicked(error)) => Err(error),
        Some(Completion::Cancelled) => Err("fiber cancelled".into()),
        None => Err("fiber did not complete".into()),
    }
}

fn start(rt: &mut Runtime, raw: Raw, callback: Value, argument: Option<Value>) -> Task {
    let task = rt.fiber.id();
    rt.gc.pin(callback);
    if let Some(argument) = argument {
        rt.gc.pin(argument);
    }
    rt.fiber.pending.push_back((
        task,
        Job {
            runtime: raw,
            callback,
            argument,
        },
    ));
    task
}

fn enqueue(
    rt: &mut Runtime,
    backend: &mut StackBackend,
    ready: &mut Ready,
    inputs: &mut BTreeMap<Task, (Value, Option<Value>)>,
) {
    for (task, job) in rt.fiber.pending.drain(..) {
        let (callback, argument) = (job.callback, job.argument);
        if let Err(error) = backend.create(task, job) {
            rt.fiber.tasks.insert(task, Completion::Panicked(error));
            rt.fiber.completion_order.push_back(task);
            ready.signal(|event| event == Event::Await(task) || matches!(event, Event::Change(_)));
            rt.gc.unpin(callback);
            if let Some(argument) = argument {
                rt.gc.unpin(argument);
            }
        } else {
            inputs.insert(task, (callback, argument));
            ready.add(task);
        }
    }
}

fn wait(raw: Raw, event: Event) -> bool {
    if !suspend(event) {
        // SAFETY: the runtime context was passed by the immediate generated caller.
        unsafe { context(raw) }.raise("suspension requires Fiber::run");
        return false;
    }
    // SAFETY: the scheduler resumed this fiber and no other context access is active.
    let rt = unsafe { context(raw) };
    if rt.fiber.cancelled() {
        rt.raise("fiber cancelled");
        return false;
    }
    true
}

fn wait_task(raw: Raw, id: Task) -> Option<Completion> {
    loop {
        // SAFETY: accesses to the context end before suspension.
        let runtime = unsafe { context(raw) };
        if let Some(completed) = runtime.fiber.tasks.remove(&id) {
            runtime.fiber.completion_order.retain(|task| *task != id);
            return Some(completed);
        }
        if !wait(raw, Event::Await(id)) {
            return None;
        }
    }
}

fn tag(rt: &mut Runtime, tag: &str, payload: Option<Value>) -> Value {
    rt.gc
        .alloc(Object::Tag(tag.into(), payload.into_iter().collect()))
}

fn error(rt: &mut Runtime, message: impl Into<String>) -> Value {
    rt.raise(message);
    Value::UNIT
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_fiber_run(raw: Raw, action: Value) -> Value {
    // SAFETY: the live context remains available through all stacks created for this run.
    match unsafe { schedule(raw, action) } {
        Ok(value) => value,
        // SAFETY: scheduling has returned ownership to the caller.
        Err(message) => error(unsafe { context(raw) }, message),
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_fiber_yield(raw: Raw) -> Value {
    wait(raw, Event::Yield);
    Value::UNIT
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_fiber_sleep(raw: Raw, delay: Value) -> Value {
    // SAFETY: convert the input and drop the runtime borrow before sleeping.
    let rt = unsafe { context(raw) };
    if let Some(delay) = rt.gc.integer(delay).and_then(ToPrimitive::to_u64)
        && let Some(until) = Instant::now().checked_add(Duration::from_millis(delay))
    {
        wait(raw, Event::Sleep(until));
        Value::UNIT
    } else {
        error(rt, "invalid fiber sleep duration")
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_fiber_cancelled(raw: Raw) -> Value {
    // SAFETY: this is a non-suspending query on the current context.
    let state = &unsafe { context(raw) }.fiber;
    Value::boolean(state.cancelled.contains(&state.active))
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_fiber_uncancellable(raw: Raw, action: Value) -> Value {
    // SAFETY: release the context borrow before invoking generated code.
    let state = &mut unsafe { context(raw) }.fiber;
    let task = state.active;
    *state.shielded.entry(task).or_default() += 1;
    // SAFETY: the action has the nullary callable ABI.
    let value = unsafe { invoke(raw, action, None) };
    // SAFETY: generated code has completed and relinquished the context.
    if let Some(depth) = unsafe { context(raw) }.fiber.shielded.get_mut(&task) {
        *depth -= 1;
    }
    value
}

unsafe fn scope(raw: Raw, action: Value, try_scope: bool) -> Value {
    // SAFETY: no Rust reference is retained across the callback.
    let rt = unsafe { context(raw) };
    if !rt.fiber.running {
        return error(rt, "scope requires Fiber::run");
    }
    let id = rt.fiber.id();
    rt.fiber.scopes.insert(id, Vec::new());
    let scope = rt.gc.alloc(Object::Scope(id));
    // SAFETY: the action has the one-Scope parameter ABI.
    let output = unsafe { invoke(raw, action, Some(scope)) };
    // SAFETY: the scope callback has completed on the current stack.
    let rt = unsafe { context(raw) };
    let mut failed = rt.take_panic();
    let failed_result =
        try_scope && matches!(rt.gc.object(output), Some(Object::Tag(tag, _)) if tag == "Err");
    let tasks = rt.fiber.scopes.remove(&id).unwrap_or_default();
    rt.gc.pin(output);
    if failed.is_some() || failed_result {
        rt.fiber.cancelled.extend(&tasks);
    }
    let task = rt.fiber.active;
    *rt.fiber.shielded.entry(task).or_default() += 1;
    for child in tasks.into_iter().rev() {
        match wait_task(raw, child) {
            Some(Completion::Finished(output)) => {
                // SAFETY: waiting has returned to the scope's stack.
                unsafe { context(raw) }.gc.unpin(output);
            }
            Some(Completion::Panicked(message)) if failed.is_none() => failed = Some(message),
            _ => {}
        }
    }
    // SAFETY: the scope owns the context again after draining its children.
    let rt = unsafe { context(raw) };
    if let Some(depth) = rt.fiber.shielded.get_mut(&task) {
        *depth -= 1;
    }
    rt.gc.unpin(output);
    if let Some(message) = failed {
        error(rt, message)
    } else if rt.fiber.cancelled() {
        error(rt, "fiber cancelled")
    } else {
        output
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_fiber_scope(raw: Raw, action: Value) -> Value {
    // SAFETY: the scope lifetime is bounded by this invocation.
    unsafe { scope(raw, action, false) }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_fiber_try_scope(raw: Raw, action: Value) -> Value {
    // SAFETY: the scope lifetime is bounded by this invocation.
    unsafe { scope(raw, action, true) }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_fiber_spawn(raw: Raw, handle: Value, work: Value) -> Value {
    // SAFETY: queuing a job does not suspend.
    let rt = unsafe { context(raw) };
    let Some(Object::Scope(scope)) = rt.gc.object(handle) else {
        return error(rt, "invalid task scope");
    };
    let scope = *scope;
    if !rt.fiber.scopes.contains_key(&scope) {
        return error(rt, "task scope is closed");
    }
    let task = start(rt, raw, work, None);
    if let Some(tasks) = rt.fiber.scopes.get_mut(&scope) {
        tasks.push(task);
    }
    rt.gc.alloc(Object::Task { task, scope })
}

fn join(raw: Raw, handle: Value, task: Value, cancel: bool) -> Value {
    // SAFETY: read and validate the handles before yielding.
    let rt = unsafe { context(raw) };
    let (Some(Object::Scope(scope)), Some(Object::Task { task, scope: owner })) =
        (rt.gc.object(handle), rt.gc.object(task))
    else {
        return error(rt, "invalid task handle");
    };
    if scope != owner {
        return error(rt, "task does not belong to this scope");
    }
    let (scope, task) = (*scope, *task);
    let Some(tasks) = rt.fiber.scopes.get_mut(&scope) else {
        return error(rt, "task scope is closed");
    };
    if !tasks.contains(&task) {
        return error(rt, "task was already joined");
    }
    tasks.retain(|id| *id != task);
    if cancel {
        rt.fiber.cancelled.insert(task);
    }
    let result = wait_task(raw, task);
    // SAFETY: the joining stack has resumed.
    let rt = unsafe { context(raw) };
    match result {
        Some(Completion::Finished(value)) => {
            rt.gc.unpin(value);
            if cancel {
                tag(rt, "Some", Some(value))
            } else {
                value
            }
        }
        Some(Completion::Panicked(message)) => error(rt, message),
        Some(Completion::Cancelled) if cancel => tag(rt, "None", None),
        Some(Completion::Cancelled) => error(rt, "child task cancelled"),
        None => Value::UNIT,
    }
}

#[unsafe(no_mangle)]
extern "C" fn ril_fiber_join(raw: Raw, scope: Value, task: Value) -> Value {
    join(raw, scope, task, false)
}

#[unsafe(no_mangle)]
extern "C" fn ril_fiber_cancel(raw: Raw, scope: Value, task: Value) -> Value {
    join(raw, scope, task, true)
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_fiber_cancel_scope(raw: Raw, scope: Value) -> Value {
    // SAFETY: marking tasks is a non-suspending runtime operation.
    let rt = unsafe { context(raw) };
    let Some(Object::Scope(scope)) = rt.gc.object(scope) else {
        return error(rt, "invalid task scope");
    };
    if let Some(tasks) = rt.fiber.scopes.get(scope) {
        rt.fiber.cancelled.extend(tasks);
    }
    Value::UNIT
}

fn pipe(rt: &mut Runtime, cap: Option<usize>) -> Value {
    let id = rt.fiber.id();
    rt.fiber.channels.insert(
        id,
        Pipe {
            cap,
            queued: VecDeque::new(),
            senders: 1,
            receiver: true,
        },
    );
    let tx = rt.gc.alloc(Object::Sender(id));
    rt.gc.pin(tx);
    let rx = rt.gc.alloc(Object::Receiver(id));
    rt.gc.unpin(tx);
    rt.gc.alloc(Object::Record(BTreeMap::from([
        ("rx".into(), rx),
        ("tx".into(), tx),
    ])))
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_channel_bounded(raw: Raw, capacity: Value) -> Value {
    // SAFETY: allocation does not switch fibers.
    let rt = unsafe { context(raw) };
    if let Some(cap) = rt.gc.integer(capacity).and_then(ToPrimitive::to_usize) {
        pipe(rt, Some(cap.max(1)))
    } else {
        error(rt, "channel capacity must be a nonnegative int")
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_channel_unbounded(raw: Raw) -> Value {
    // SAFETY: allocation does not switch fibers.
    pipe(unsafe { context(raw) }, None)
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_channel_clone(raw: Raw, sender: Value) -> Value {
    // SAFETY: increments the handle count without a stack switch.
    let rt = unsafe { context(raw) };
    let Some(Object::Sender(id)) = rt.gc.object(sender) else {
        return error(rt, "invalid channel sender");
    };
    let id = *id;
    if let Some(channel) = rt.fiber.channels.get_mut(&id) {
        channel.senders += 1;
    }
    rt.gc.alloc(Object::Sender(id))
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_channel_close(raw: Raw, sender: Value) -> Value {
    // SAFETY: closes the handle synchronously.
    let rt = unsafe { context(raw) };
    let Some(Object::Sender(id)) = rt.gc.object(sender) else {
        return error(rt, "invalid channel sender");
    };
    let id = *id;
    if let Some(channel) = rt.fiber.channels.get_mut(&id) {
        channel.senders = channel.senders.saturating_sub(1);
    }
    if let Some(value) = rt.gc.object_mut(sender) {
        *value = Object::Array(Vec::new());
    }
    rt.fiber.wake.insert(id);
    Value::UNIT
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_channel_close_recv(raw: Raw, receiver: Value) -> Value {
    // SAFETY: closes the handle synchronously and releases buffered roots.
    let rt = unsafe { context(raw) };
    let Some(Object::Receiver(id)) = rt.gc.object(receiver) else {
        return error(rt, "invalid channel receiver");
    };
    let id = *id;
    if let Some(channel) = rt.fiber.channels.get_mut(&id) {
        channel.receiver = false;
        for item in channel.queued.drain(..) {
            rt.gc.unpin(item);
        }
    }
    rt.fiber.wake.insert(id);
    Value::UNIT
}

fn send(raw: Raw, sender: Value, item: Value, blocking: bool) -> Value {
    loop {
        // SAFETY: this borrow ends before waiting or returning to generated code.
        let rt = unsafe { context(raw) };
        let Some(Object::Sender(id)) = rt.gc.object(sender) else {
            return error(rt, "invalid channel sender");
        };
        let id = *id;
        let Some(channel) = rt.fiber.channels.get_mut(&id) else {
            return error(rt, "unknown channel");
        };
        if !channel.receiver {
            let fault = tag(rt, "Closed", Some(item));
            return tag(rt, "Err", Some(fault));
        }
        if channel.cap.is_none_or(|cap| channel.queued.len() < cap) {
            channel.queued.push_back(item);
            rt.gc.pin(item);
            rt.fiber.wake.insert(id);
            return tag(rt, "Ok", Some(Value::UNIT));
        }
        if !blocking {
            let fault = tag(rt, "Full", Some(item));
            return tag(rt, "Err", Some(fault));
        }
        if !wait(raw, Event::Channel(id)) {
            return Value::UNIT;
        }
    }
}

fn receive(raw: Raw, receiver: Value, blocking: bool) -> Value {
    loop {
        // SAFETY: access to the active runtime ends before any suspension.
        let rt = unsafe { context(raw) };
        let Some(Object::Receiver(id)) = rt.gc.object(receiver) else {
            return error(rt, "invalid channel receiver");
        };
        let id = *id;
        let Some(channel) = rt.fiber.channels.get_mut(&id) else {
            return error(rt, "unknown channel");
        };
        if let Some(item) = channel.queued.pop_front() {
            rt.gc.unpin(item);
            rt.fiber.wake.insert(id);
            return tag(rt, if blocking { "Some" } else { "Ok" }, Some(item));
        }
        if blocking && (!channel.receiver || channel.senders == 0) {
            return tag(rt, "None", None);
        }
        if !blocking {
            let name = if !channel.receiver || channel.senders == 0 {
                "Closed"
            } else {
                "Empty"
            };
            let fault = tag(rt, name, None);
            return tag(rt, "Err", Some(fault));
        }
        if !wait(raw, Event::Channel(id)) {
            return Value::UNIT;
        }
    }
}

#[unsafe(no_mangle)]
extern "C" fn ril_channel_send(raw: Raw, sender: Value, item: Value) -> Value {
    send(raw, sender, item, true)
}

#[unsafe(no_mangle)]
extern "C" fn ril_channel_try_send(raw: Raw, sender: Value, item: Value) -> Value {
    send(raw, sender, item, false)
}

#[unsafe(no_mangle)]
extern "C" fn ril_channel_recv(raw: Raw, receiver: Value) -> Value {
    receive(raw, receiver, true)
}

#[unsafe(no_mangle)]
extern "C" fn ril_channel_try_recv(raw: Raw, receiver: Value) -> Value {
    receive(raw, receiver, false)
}

mod combinators;

pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    macro_rules! table {
        ($($symbol:ident),+ $(,)?) => { vec![ $((stringify!($symbol), $symbol as *const u8)),+ ] };
    }
    let mut symbols = table![
        ril_fiber_run,
        ril_fiber_scope,
        ril_fiber_try_scope,
        ril_fiber_spawn,
        ril_fiber_yield,
        ril_fiber_sleep,
        ril_fiber_cancelled,
        ril_fiber_uncancellable,
        ril_fiber_join,
        ril_fiber_cancel,
        ril_fiber_cancel_scope,
        ril_channel_bounded,
        ril_channel_unbounded,
        ril_channel_clone,
        ril_channel_close,
        ril_channel_close_recv,
        ril_channel_send,
        ril_channel_try_send,
        ril_channel_recv,
        ril_channel_try_recv,
    ];
    symbols.extend(combinators::symbols());
    symbols
}
