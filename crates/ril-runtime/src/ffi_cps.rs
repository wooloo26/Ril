//! Native-step trampoline. Runtime borrows end before any native invocation.
use super::*;
use crate::cps::{Continuation, HandlerFrame, Resumption, Step};
use crate::cps_exit::{After, Work};
#[path = "ffi_budget.rs"]
mod budget;
#[path = "ffi_channel.rs"]
mod channel;
#[path = "ffi_concurrent.rs"]
mod concurrent;
#[path = "ffi_exit.rs"]
mod exits;
#[path = "ffi_foreign.rs"]
mod foreign;
#[path = "ffi_host.rs"]
mod host;
#[path = "ffi_parallel.rs"]
mod parallel;
#[path = "ffi_retained.rs"]
mod retained;

#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_activation_new() -> u64 {
    handle(Runtime::new_activation)
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_activation_attach(activation: u64) {
    guarded(|runtime| runtime.attach_activation(Handle(activation)));
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_scope_enter(activation: u64) -> u64 {
    handle(|runtime| {
        let state = runtime.activation(Handle(activation))?;
        if state.closed {
            return Err(RuntimeError::internal("logical activation has ended"));
        }
        let depth = u32::try_from(state.cleanups.len())
            .map_err(|_| RuntimeError::internal("too many scoped resources"))?;
        runtime.allocate(Object::CpsScope {
            activation: Handle(activation),
            depth,
        })
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_scope_register(activation: u64, resource: u64) -> u64 {
    handle(|runtime| runtime.register_activation_cleanup(Handle(activation), Handle(resource)))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_scope_leave(activation: u64, marker: u64, value: u64) -> u64 {
    match catch_unwind(AssertUnwindSafe(|| scope_leave(activation, marker, value))) {
        Ok(value) => value,
        Err(_) => {
            with_runtime(|runtime| {
                runtime.fault = Some(RuntimeError::internal(
                    "unexpected Rust panic in logical cleanup",
                ))
            });
            0
        }
    }
}
fn scope_leave(activation: u64, marker: u64, value: u64) -> u64 {
    let depth: Option<u32> = guarded(|runtime| match runtime.heap.get(Handle(marker))? {
        Object::CpsScope {
            activation: owner,
            depth,
        } if owner.0 == activation => Ok(Some(*depth)),
        _ => Err(RuntimeError::internal(
            "logical scope marker belongs to another activation",
        )),
    });
    let Some(depth) = depth else {
        return 0;
    };
    run_cleanup_stack(Some(Handle(activation)), depth, value);
    if ril_rt_status() == 0 { value } else { 0 }
}
fn close_empty_activation(activation: Handle) {
    if activation == Handle::INVALID {
        return;
    }
    let state = with_runtime(|runtime| runtime.activation(activation).cloned());
    let state = match state {
        Ok(state) => state,
        Err(error) => {
            with_runtime(|runtime| {
                runtime.fault = Some(error);
                runtime.cps_activation = Handle::INVALID;
            });
            return;
        }
    };
    if !state.cleanups.is_empty() {
        with_runtime(|runtime| {
            runtime.fault = Some(RuntimeError::internal(
                "empty-arm optimization retained cleanup",
            ))
        });
        return;
    }
    if with_runtime(|runtime| {
        runtime
            .concurrent_scopes
            .iter()
            .any(|scope| scope.activation == activation)
            || runtime
                .foreign_calls
                .values()
                .any(|call| call.activation == activation)
    }) {
        with_runtime(|runtime| {
            runtime.fault = Some(RuntimeError::internal(
                "empty-arm optimization retained host ownership",
            ))
        });
        return;
    }
    with_runtime(|runtime| {
        runtime.end_buffered_reads(activation);
        if let Ok(Object::CpsActivation(state)) = runtime.heap.get_mut(activation) {
            state.closed = true;
        }
        runtime.cps_activation = state.parent;
    });
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_activation_return(
    activation: u64,
    continuation: u64,
    value: u64,
) -> u64 {
    match catch_unwind(AssertUnwindSafe(|| {
        exits::close_return(
            Handle(activation),
            Handle(continuation),
            Handle(value),
            None,
        )
    })) {
        Ok(value) => value,
        Err(_) => {
            with_runtime(|runtime| {
                runtime.fault = Some(RuntimeError::internal(
                    "unexpected Rust panic while returning a logical activation",
                ))
            });
            0
        }
    }
}

fn step(value: impl FnOnce(&mut Runtime) -> Step) -> u64 {
    handle(|runtime| {
        let value = value(runtime);
        runtime.allocate(Object::CpsStep(value))
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_is_cps(callable: u64) -> u32 {
    guarded(|runtime| {
        Ok(u32::from(match runtime.heap.get(Handle(callable))? {
            Object::BudgetClosure { normal_is_cps, .. } => {
                *normal_is_cps || runtime.budgets.is_active()
            }
            Object::CpsClosure { .. }
            | Object::CpsOperation(_)
            | Object::RetainedClosure { .. } => true,
            _ => false,
        }))
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_callable(address: u64, environment: u64) -> u64 {
    handle(|runtime| {
        runtime.heap.get(Handle(environment))?;
        if address == 0 {
            return Err(RuntimeError::internal("null native CPS address"));
        }
        runtime.allocate(Object::CpsClosure {
            function: address,
            environment: Handle(environment),
        })
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_operation(operation: u64) -> u64 {
    handle(|runtime| runtime.allocate(Object::CpsOperation(operation)))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_continuation(address: u64, environment: u64) -> u64 {
    handle(|runtime| {
        runtime.heap.get(Handle(environment))?;
        if address == 0 {
            return Err(RuntimeError::internal("null continuation address"));
        }
        runtime.allocate(Object::CpsContinuation {
            state: Continuation::Native {
                function: address,
                environment: Handle(environment),
                handlers: runtime.cps_handlers,
                activation: runtime.cps_activation,
                delimiters: runtime.cps_delimiters.clone(),
                budget_depth: runtime.budgets.depth(),
            },
            used: false,
        })
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_end() -> u64 {
    handle(|runtime| {
        runtime.allocate(Object::CpsContinuation {
            state: Continuation::End,
            used: false,
        })
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_call(callable: u64, arguments: u64, continuation: u64) -> u64 {
    call_step(callable, arguments, continuation, false)
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_callback_call(
    callable: u64,
    arguments: u64,
    continuation: u64,
) -> u64 {
    call_step(callable, arguments, continuation, true)
}
fn call_step(callable: u64, arguments: u64, continuation: u64, callback_entry: bool) -> u64 {
    // Argument evaluation has completed. Preserve the actual call before the
    // operation's cancellation point (send must consume submitted tickets).
    handle_control(|runtime| {
        runtime.allocate(Object::CpsStep(Step::Call {
            callable: Handle(callable),
            arguments: Handle(arguments),
            continuation: Handle(continuation),
            handlers: runtime.cps_handlers,
            callback_entry,
        }))
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_return(continuation: u64, value: u64) -> u64 {
    step(|_| Step::Return {
        continuation: Handle(continuation),
        value: Handle(value),
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_perform(operation: u64, arguments: u64, continuation: u64) -> u64 {
    step(|runtime| Step::Perform {
        operation,
        arguments: Handle(arguments),
        continuation: Handle(continuation),
        handlers: runtime.cps_handlers,
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_handlers() -> u64 {
    handle(|runtime| runtime.allocate(Object::CpsHandlers(Default::default())))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_handler_add(table: u64, operation: u64, arm: u64) -> u64 {
    handle(|runtime| {
        runtime.heap.get(Handle(arm))?;
        let Object::CpsHandlers(entries) = runtime.heap.get_mut(Handle(table))? else {
            return Err(RuntimeError::internal("invalid handler table"));
        };
        entries.insert(operation, Handle(arm));
        Ok(Handle(table))
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_handle(
    body: u64,
    table: u64,
    continuation: u64,
    definition: u64,
) -> u64 {
    step(|runtime| Step::Handle {
        definition,
        body: Handle(body),
        table: Handle(table),
        continuation: Handle(continuation),
        handlers: runtime.cps_handlers,
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_resume(resumption: u64, value: u64) -> u64 {
    step(|_| Step::Resume {
        resumption: Handle(resumption),
        value: Handle(value),
        next: None,
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_resume_then(resumption: u64, value: u64, next: u64) -> u64 {
    step(|_| Step::Resume {
        resumption: Handle(resumption),
        value: Handle(value),
        next: Some(Handle(next)),
    })
}

enum Target {
    Native(u64, Handle, bool, bool),
    Builtin,
    Operation(u64),
}
fn target(runtime: &Runtime, callable: Handle) -> Result<Target> {
    Ok(match runtime.heap.get(callable)? {
        Object::BudgetClosure {
            normal,
            metered,
            environment,
            normal_is_cps,
            metered_entry_event,
        } => {
            if runtime.budgets.is_active() {
                Target::Native(*metered, *environment, true, *metered_entry_event)
            } else {
                Target::Native(*normal, *environment, *normal_is_cps, false)
            }
        }
        Object::Closure { .. } | Object::CpsClosure { .. } if runtime.budgets.is_active() => {
            return Err(RuntimeError::internal(
                "covered callable lacks a metered native entry",
            ));
        }
        Object::Closure {
            function,
            environment,
        } => Target::Native(*function, *environment, false, false),
        Object::CpsClosure {
            function,
            environment,
        } => Target::Native(*function, *environment, true, false),
        Object::CpsOperation(operation) => Target::Operation(*operation),
        Object::Builtin(_) | Object::DataConstructor { .. } => Target::Builtin,
        _ => return Err(RuntimeError::internal("non-callable native CPS target")),
    })
}
fn set_handlers(handlers: Handle) {
    with_runtime(|runtime| runtime.cps_handlers = handlers);
}
fn return_step(continuation: Handle, value: u64) -> u64 {
    ril_rt_cps_return(continuation.0, value)
}
fn ancestor(runtime: &Runtime, ancestor: Handle, mut child: Handle) -> Result<bool> {
    loop {
        if ancestor == child {
            return Ok(true);
        }
        if child == Handle::INVALID {
            return Ok(false);
        }
        child = runtime.activation(child)?.parent;
    }
}
struct Crossing {
    delimiter: Handle,
    checkpoint: Handle,
    aborted: bool,
}
fn find_crossing(
    runtime: &Runtime,
    target: Handle,
    scopes: &[Handle],
    base: usize,
) -> Result<Option<Crossing>> {
    let mut selected: Option<Crossing> = None;
    let mut any_abort = false;
    for &delimiter in runtime
        .cps_delimiters
        .get(base..)
        .ok_or_else(|| RuntimeError::internal("active delimiter scope was lost"))?
        .iter()
        .rev()
    {
        let Object::CpsContinuation {
            state:
                Continuation::Delimiter {
                    activation: checkpoint,
                    resumptions,
                    ..
                },
            ..
        } = runtime.heap.get(delimiter)?
        else {
            return Err(RuntimeError::internal(
                "active delimiter has the wrong control shape",
            ));
        };
        if scopes.contains(&delimiter) || !ancestor(runtime, target, *checkpoint)? {
            continue;
        }
        let mut aborted = false;
        for resumption in resumptions {
            let Object::CpsResumption(state) = runtime.heap.get(*resumption)? else {
                return Err(RuntimeError::internal("invalid active resumption"));
            };
            aborted |= !state.used;
        }
        any_abort |= aborted;
        if selected.is_none() {
            selected = Some(Crossing {
                delimiter,
                checkpoint: *checkpoint,
                aborted,
            });
        }
    }
    if let Some(selected) = &mut selected {
        selected.aborted = any_abort;
    }
    Ok(selected)
}
type FaultCheckpoint = (Handle, Vec<Handle>, Vec<(Handle, Handle)>);

/// Owns a trampoline extent between native-step safepoints. A pending driver
/// must stay paired with its logical Runtime, including its precise root frame.
struct Driver {
    runtime: std::sync::Arc<()>,
    previous: Handle,
    previous_activation: Handle,
    previous_delimiter_depth: usize,
    previous_scopes: Vec<Handle>,
    previous_return_depth: usize,
    previous_concurrent_depth: usize,
    previous_exit_depth: usize,
    previous_budget_depth: usize,
    fault_unwinding: bool,
    fault_checkpoint: Option<FaultCheckpoint>,
    current: u64,
    completed: bool,
    pending: Option<Pending>,
}

enum Pending {
    Parallel(parallel::PendingParallel),
    Foreign(foreign::PendingForeign),
    ForeignClose {
        state: foreign::PendingForeignClose,
        owner: u64,
        activation: Handle,
    },
    HostCleanup {
        job: crate::host_job::Job<()>,
        owner: u64,
    },
    Host(host::PendingHost),
    ScopeFinish(concurrent::PendingFinish),
    ScopeClose(concurrent::PendingClose),
    Sleep {
        future: crate::timer::Sleep,
        continuation: Handle,
    },
    Join {
        future: crate::concurrent::JoinFuture,
        continuation: Handle,
    },
    Send {
        future: crate::channel::SendFuture,
        continuation: Handle,
    },
    Receive {
        future: crate::channel::ReceiveFuture,
        continuation: Handle,
    },
}

fn start_driver(initial: u64) -> Driver {
    // This extent also owns fault unwinding. It needs a frame even when the
    // caller already carries a fault; guarded ABI entry would skip that push.
    with_runtime(|runtime| runtime.enter());
    let previous = with_runtime(|runtime| runtime.cps_handlers);
    let previous_activation = with_runtime(|runtime| runtime.cps_activation);
    let previous_delimiter_depth = with_runtime(|runtime| runtime.cps_delimiters.len());
    let previous_scopes = with_runtime(|runtime| runtime.cps_delimiters.clone());
    let previous_return_depth = with_runtime(|runtime| runtime.cps_resume_returns.len());
    let previous_concurrent_depth = with_runtime(|runtime| runtime.concurrent_scopes.len());
    let previous_exit_depth = with_runtime(|runtime| runtime.cps_exits.len());
    let previous_budget_depth = with_runtime(|runtime| runtime.budgets.depth());
    if previous != Handle::INVALID {
        ril_rt_root(1, previous.0);
    }
    if previous_activation != Handle::INVALID {
        ril_rt_root(2, previous_activation.0);
    }
    if initial != 0 {
        ril_rt_root(0, initial);
    }
    // Saved delimiter checkpoints remain live even when an inner handler
    // temporarily leaves them out of the current dynamic delimiter list.
    for (index, scope) in previous_scopes.iter().enumerate() {
        if let Some(slot) = u32::try_from(index)
            .ok()
            .and_then(|index| index.checked_add(3))
        {
            ril_rt_root(slot, scope.0);
        } else {
            with_runtime(|runtime| {
                runtime.fault = Some(RuntimeError::internal("driver root index exhausted"))
            });
            break;
        }
    }
    Driver {
        runtime: RUNTIME.with_borrow(|runtime| runtime.identity.clone()),
        previous,
        previous_activation,
        previous_delimiter_depth,
        previous_scopes,
        previous_return_depth,
        previous_concurrent_depth,
        previous_exit_depth,
        previous_budget_depth,
        fault_unwinding: false,
        fault_checkpoint: None,
        current: initial,
        completed: false,
        pending: None,
    }
}

#[cfg(test)]
fn drive_slice(driver: &mut Driver, steps: std::num::NonZeroUsize) -> std::task::Poll<u64> {
    let mut context = std::task::Context::from_waker(std::task::Waker::noop());
    drive_with_context(driver, steps, &mut context)
}

fn poll_pending(
    driver: &mut Driver,
    context: &mut std::task::Context<'_>,
) -> std::task::Poll<Option<u64>> {
    let Some(pending) = &mut driver.pending else {
        return std::task::Poll::Ready(None);
    };
    let next = match pending {
        Pending::Parallel(pending) => {
            let std::task::Poll::Ready(next) = parallel::poll(pending, context) else {
                return std::task::Poll::Pending;
            };
            next
        }
        Pending::Foreign(pending) => {
            let std::task::Poll::Ready(next) = foreign::poll(pending, context) else {
                return std::task::Poll::Pending;
            };
            next
        }
        Pending::ForeignClose {
            state,
            owner,
            activation,
        } => {
            let std::task::Poll::Ready(result) = foreign::poll_close(state, context) else {
                return std::task::Poll::Pending;
            };
            exits::complete_foreign_close(*owner, *activation, result)
        }
        Pending::HostCleanup { job, owner } => {
            let std::task::Poll::Ready(result) =
                std::future::Future::poll(std::pin::Pin::new(job), context)
            else {
                return std::task::Poll::Pending;
            };
            exits::complete_host_cleanup(*owner, result)
        }
        Pending::Host(pending) => {
            let std::task::Poll::Ready(next) = host::poll(pending, context) else {
                return std::task::Poll::Pending;
            };
            next
        }
        Pending::ScopeFinish(pending) => {
            let std::task::Poll::Ready(next) = concurrent::poll_finish(pending, context) else {
                return std::task::Poll::Pending;
            };
            next
        }
        Pending::ScopeClose(pending) => {
            let std::task::Poll::Ready(next) = concurrent::poll_close(pending, context) else {
                return std::task::Poll::Pending;
            };
            next
        }
        Pending::Sleep {
            future,
            continuation,
        } => {
            let std::task::Poll::Ready(result) =
                std::future::Future::poll(std::pin::Pin::new(future), context)
            else {
                return std::task::Poll::Pending;
            };
            let value = finish_host(
                result.map(|()| crate::host_service::Reply::Slept),
                crate::host_service::finish,
            );
            if value == 0 {
                0
            } else {
                return_step(*continuation, value)
            }
        }
        Pending::Join {
            future,
            continuation,
        } => {
            let std::task::Poll::Ready(result) =
                std::future::Future::poll(std::pin::Pin::new(future), context)
            else {
                return std::task::Poll::Pending;
            };
            concurrent::finish_join(result, *continuation)
        }
        Pending::Send {
            future,
            continuation,
        } => {
            let std::task::Poll::Ready(result) =
                std::future::Future::poll(std::pin::Pin::new(future), context)
            else {
                return std::task::Poll::Pending;
            };
            channel::finish_send(result, *continuation)
        }
        Pending::Receive {
            future,
            continuation,
        } => {
            let std::task::Poll::Ready(result) =
                std::future::Future::poll(std::pin::Pin::new(future), context)
            else {
                return std::task::Poll::Pending;
            };
            channel::finish_recv(result, *continuation)
        }
    };
    driver.pending = None;
    std::task::Poll::Ready(Some(next))
}

fn drive_with_context(
    driver: &mut Driver,
    steps: std::num::NonZeroUsize,
    context: &mut std::task::Context<'_>,
) -> std::task::Poll<u64> {
    if driver.completed
        || !RUNTIME
            .with_borrow(|runtime| std::sync::Arc::ptr_eq(&runtime.identity, &driver.runtime))
    {
        with_runtime(|runtime| {
            runtime.fault = Some(RuntimeError::internal(
                "native driver is complete or belongs to another runtime",
            ))
        });
        return std::task::Poll::Ready(0);
    }
    match poll_pending(driver, context) {
        std::task::Poll::Pending => return std::task::Poll::Pending,
        std::task::Poll::Ready(Some(next)) => driver.current = next,
        std::task::Poll::Ready(None) => {}
    }
    let previous = driver.previous;
    let previous_activation = driver.previous_activation;
    let previous_delimiter_depth = driver.previous_delimiter_depth;
    let previous_scopes = driver.previous_scopes.clone();
    let previous_return_depth = driver.previous_return_depth;
    let previous_concurrent_depth = driver.previous_concurrent_depth;
    let previous_exit_depth = driver.previous_exit_depth;
    let previous_budget_depth = driver.previous_budget_depth;
    let mut fault_unwinding = driver.fault_unwinding;
    let mut fault_checkpoint = driver.fault_checkpoint.clone();
    let mut current = driver.current;
    let mut remaining = steps.get();
    let result = loop {
        let result = loop {
            if current == 0 || ril_rt_status() != 0 {
                break 0;
            }
            ril_rt_root(0, current);
            ril_rt_statement_end();
            if remaining == 0 {
                driver.current = current;
                driver.fault_unwinding = fault_unwinding;
                driver.fault_checkpoint = fault_checkpoint;
                return std::task::Poll::Pending;
            }
            remaining -= 1;
            let event: Option<Step> =
                guarded_control(|runtime| match runtime.heap.get(Handle(current))? {
                    Object::CpsStep(event) => Ok(Some(event.clone())),
                    _ => Err(RuntimeError::internal(
                        "native CPS function returned a non-step",
                    )),
                });
            let Some(event) = event else {
                break 0;
            };
            let submitted_send = matches!(&event, Step::Call { callable, .. }
                if with_runtime(|runtime| matches!(runtime.heap.get(*callable), Ok(Object::Builtin(name)) if name.strip_prefix("Prelude::").unwrap_or(name) == "Channel::send")));
            if !submitted_send
                && !matches!(
                    event,
                    Step::ConcurrentDrain { .. }
                        | Step::ConcurrentClose { .. }
                        | Step::HostCleanup { .. }
                        | Step::ForeignClose { .. }
                )
            {
                guarded(|_| Ok(()));
                if ril_rt_status() != 0 {
                    break 0;
                }
            }
            current = match event {
                Step::Foreign { call } => {
                    let pending = match foreign::prepare(call) {
                        Ok(pending) => pending,
                        Err(error) => {
                            with_runtime(|runtime| runtime.fault = Some(error));
                            break 0;
                        }
                    };
                    driver.pending = Some(Pending::Foreign(pending));
                    match poll_pending(driver, context) {
                        std::task::Poll::Ready(Some(next)) => next,
                        std::task::Poll::Ready(None) => unreachable!(),
                        std::task::Poll::Pending => {
                            driver.current = current;
                            driver.fault_unwinding = fault_unwinding;
                            driver.fault_checkpoint = fault_checkpoint;
                            return std::task::Poll::Pending;
                        }
                    }
                }
                Step::ForeignClose { owner, activation } => {
                    let state = match foreign::prepare_close(activation) {
                        Ok(state) => state,
                        Err(error) => {
                            current = exits::complete_foreign_close(owner, activation, Err(error));
                            continue;
                        }
                    };
                    driver.pending = Some(Pending::ForeignClose {
                        state,
                        owner,
                        activation,
                    });
                    match poll_pending(driver, context) {
                        std::task::Poll::Ready(Some(next)) => next,
                        std::task::Poll::Ready(None) => unreachable!(),
                        std::task::Poll::Pending => {
                            driver.current = current;
                            driver.fault_unwinding = fault_unwinding;
                            driver.fault_checkpoint = fault_checkpoint;
                            return std::task::Poll::Pending;
                        }
                    }
                }
                Step::Complete { value } => break value.0,
                Step::Exit { owner } => exits::advance(owner),
                Step::HostCleanup { owner } => {
                    let job = match exits::prepare_host_cleanup(owner) {
                        Ok(job) => job,
                        Err(error) => {
                            current = exits::complete_host_cleanup(owner, Err(error));
                            continue;
                        }
                    };
                    driver.pending = Some(Pending::HostCleanup { job, owner });
                    match poll_pending(driver, context) {
                        std::task::Poll::Ready(Some(next)) => next,
                        std::task::Poll::Ready(None) => unreachable!(),
                        std::task::Poll::Pending => {
                            driver.current = current;
                            driver.fault_unwinding = fault_unwinding;
                            driver.fault_checkpoint = fault_checkpoint;
                            return std::task::Poll::Pending;
                        }
                    }
                }
                Step::ConcurrentClose {
                    scope,
                    activation,
                    owner,
                } => {
                    let pending = match concurrent::prepare_close(scope, activation, owner) {
                        Ok(pending) => pending,
                        Err(error) => {
                            with_runtime(|runtime| runtime.fault = Some(error));
                            break 0;
                        }
                    };
                    driver.pending = Some(Pending::ScopeClose(pending));
                    match poll_pending(driver, context) {
                        std::task::Poll::Ready(Some(next)) => next,
                        std::task::Poll::Ready(None) => unreachable!(),
                        std::task::Poll::Pending => {
                            driver.current = current;
                            driver.fault_unwinding = fault_unwinding;
                            driver.fault_checkpoint = fault_checkpoint;
                            return std::task::Poll::Pending;
                        }
                    }
                }
                Step::ConcurrentDrain { scope, body } => {
                    let pending = match concurrent::prepare_finish(scope, body) {
                        Ok(pending) => pending,
                        Err(error) => {
                            with_runtime(|runtime| runtime.fault = Some(error));
                            break 0;
                        }
                    };
                    driver.pending = Some(Pending::ScopeFinish(pending));
                    match poll_pending(driver, context) {
                        std::task::Poll::Ready(Some(next)) => next,
                        std::task::Poll::Ready(None) => unreachable!(),
                        std::task::Poll::Pending => {
                            driver.current = current;
                            driver.fault_unwinding = fault_unwinding;
                            driver.fault_checkpoint = fault_checkpoint;
                            return std::task::Poll::Pending;
                        }
                    }
                }
                Step::Budget {
                    limit,
                    action,
                    continuation,
                    operation,
                    handlers,
                    activation,
                    delimiters,
                } => budget::enter(
                    limit,
                    action,
                    continuation,
                    operation,
                    handlers,
                    activation,
                    delimiters,
                ),
                Step::Charge { event, next } => budget::charge(event, next),
                Step::BudgetExhaust {
                    boundary,
                    abandoned,
                } => budget::abandon(boundary, abandoned),
                Step::Call {
                    callable,
                    arguments,
                    continuation,
                    handlers,
                    callback_entry,
                } => {
                    set_handlers(handlers);
                    guarded_control(|runtime| runtime.check_read_reservation(callable, arguments));
                    if ril_rt_status() != 0 {
                        break 0;
                    }
                    if let Some(step) = retained::dispatch(
                        callable,
                        arguments,
                        continuation,
                        handlers,
                        callback_entry,
                    ) {
                        current = step;
                        continue;
                    }
                    let destination: Option<Target> =
                        guarded_control(|runtime| target(runtime, callable).map(Some));
                    if callback_entry
                        && !matches!(destination, Some(Target::Native(_, _, _, true)))
                        && let Some(step) = budget::before_callback()
                    {
                        current = step;
                        continue;
                    }
                    if ril_rt_status() != 0 {
                        break 0;
                    }
                    match destination {
                        Some(Target::Native(address, environment, suspends, _)) => {
                            let args = if suspends {
                                handle(|runtime| {
                                    let mut args = runtime.sequence(arguments)?;
                                    args.push(continuation);
                                    runtime.allocate(Object::Tuple(args))
                                })
                            } else {
                                arguments.0
                            };
                            if args == 0 {
                                break 0;
                            }
                            let value = invoke_address(address, environment.0, args);
                            if value == 0 {
                                break 0;
                            }
                            if suspends {
                                value
                            } else {
                                return_step(continuation, value)
                            }
                        }
                        Some(Target::Builtin) => {
                            // Classification must not insert a cancellation
                            // point before a submitted Channel::send consumes
                            // its transferred authority.
                            let pending: Option<Pending> = guarded_control(|runtime| {
                                let Object::Builtin(name) = runtime.heap.get(callable)? else {
                                    return Ok(None);
                                };
                                let name = name.strip_prefix("Prelude::").unwrap_or(name);
                                let name = ril_runtime_api::builtins::canonical_builtin(name)
                                    .unwrap_or(name);
                                if name == "Channel::send" {
                                    return Ok(Some(Pending::Send {
                                        future: channel::prepare_send(runtime, arguments)?,
                                        continuation,
                                    }));
                                }
                                if name == "Channel::recv" {
                                    return Ok(Some(Pending::Receive {
                                        future: channel::prepare_recv(runtime, arguments)?,
                                        continuation,
                                    }));
                                }
                                if name == "Concurrent::join" {
                                    return Ok(Some(Pending::Join {
                                        future: concurrent::prepare_join(runtime, arguments)?,
                                        continuation,
                                    }));
                                }
                                if name != "Time::sleep" {
                                    return Ok(None);
                                }
                                let arguments = runtime.sequence(arguments)?;
                                let crate::host_service::Request::Sleep {
                                    duration,
                                    cancellation,
                                } = crate::host_service::prepare(runtime, name, &arguments)?
                                else {
                                    return Err(RuntimeError::internal(
                                        "invalid native sleep request",
                                    ));
                                };
                                Ok(Some(Pending::Sleep {
                                    future: crate::timer::Sleep::new(duration, cancellation)?,
                                    continuation,
                                }))
                            });
                            if let Some(pending) = pending {
                                driver.pending = Some(pending);
                                match poll_pending(driver, context) {
                                    std::task::Poll::Ready(Some(next)) => {
                                        current = next;
                                        continue;
                                    }
                                    std::task::Poll::Ready(None) => unreachable!(),
                                    std::task::Poll::Pending => {
                                        driver.current = current;
                                        driver.fault_unwinding = fault_unwinding;
                                        driver.fault_checkpoint = fault_checkpoint;
                                        return std::task::Poll::Pending;
                                    }
                                }
                            }
                            if ril_rt_status() != 0 {
                                break 0;
                            }
                            if let Some(pending) = host::prepare(callable, arguments, continuation)
                            {
                                driver.pending = Some(Pending::Host(pending));
                                match poll_pending(driver, context) {
                                    std::task::Poll::Ready(Some(next)) => {
                                        current = next;
                                        continue;
                                    }
                                    std::task::Poll::Ready(None) => unreachable!(),
                                    std::task::Poll::Pending => {
                                        driver.current = current;
                                        driver.fault_unwinding = fault_unwinding;
                                        driver.fault_checkpoint = fault_checkpoint;
                                        return std::task::Poll::Pending;
                                    }
                                }
                            }
                            if ril_rt_status() != 0 {
                                break 0;
                            }
                            if let Some(step) =
                                foreign::dispatch(callable, arguments, continuation, handlers)
                            {
                                current = step;
                                continue;
                            }
                            if let Some(step) =
                                concurrent::dispatch(callable, arguments, continuation, handlers)
                            {
                                current = step;
                                continue;
                            }
                            if let Some(step) = channel::dispatch(callable, arguments, continuation)
                            {
                                current = step;
                                continue;
                            }
                            if let Some(pending) =
                                parallel::prepare(callable, arguments, continuation)
                            {
                                driver.pending = Some(Pending::Parallel(pending));
                                match poll_pending(driver, context) {
                                    std::task::Poll::Ready(Some(next)) => {
                                        current = next;
                                        continue;
                                    }
                                    std::task::Poll::Ready(None) => unreachable!(),
                                    std::task::Poll::Pending => {
                                        driver.current = current;
                                        driver.fault_unwinding = fault_unwinding;
                                        driver.fault_checkpoint = fault_checkpoint;
                                        return std::task::Poll::Pending;
                                    }
                                }
                            }
                            if ril_rt_status() != 0 {
                                break 0;
                            }
                            let value = invoke_callable(callable.0, arguments.0);
                            if value == 0 {
                                break 0;
                            }
                            return_step(continuation, value)
                        }
                        Some(Target::Operation(operation)) => {
                            ril_rt_cps_perform(operation, arguments.0, continuation.0)
                        }
                        None => break 0,
                    }
                }
                Step::Return {
                    continuation,
                    value,
                } => {
                    let state: Option<Continuation> = guarded(|runtime| {
                        let Object::CpsContinuation { state, used } =
                            runtime.heap.get_mut(continuation)?
                        else {
                            return Err(RuntimeError::internal("invalid native continuation"));
                        };
                        if *used {
                            return Err(RuntimeError::internal(
                                "native continuation invoked more than once",
                            ));
                        }
                        // Keep the delimiter live through its protected cleanup.
                        if !matches!(state, Continuation::Delimiter { .. }) {
                            *used = true;
                        }
                        Ok(Some(state.clone()))
                    });
                    match state {
                        Some(Continuation::Cleanup { owner }) => {
                            exits::callback_return(owner, value)
                        }
                        Some(Continuation::End) => exits::transition(
                            vec![
                                Work::Cross {
                                    target: previous_activation,
                                    scopes: previous_scopes.clone(),
                                    base: previous_delimiter_depth,
                                    aborted: false,
                                },
                                Work::Unwind(previous_activation),
                                Work::Budgets(previous_budget_depth),
                            ],
                            After::Complete,
                            value,
                        ),
                        Some(Continuation::Native {
                            function,
                            environment,
                            handlers,
                            activation,
                            delimiters,
                            budget_depth,
                        }) => exits::transition(
                            vec![
                                Work::Cross {
                                    target: activation,
                                    scopes: delimiters,
                                    base: previous_delimiter_depth,
                                    aborted: false,
                                },
                                Work::RequireSuccess,
                                Work::Unwind(activation),
                                Work::Budgets(budget_depth),
                            ],
                            After::Native {
                                function,
                                environment,
                                handlers,
                            },
                            value,
                        ),
                        Some(Continuation::Delimiter {
                            outer,
                            handlers,
                            activation,
                            resumptions,
                            budget_depth,
                        }) => {
                            let aborted = with_runtime(|runtime| {
                                let aborted=resumptions.iter().any(|resumption|matches!(runtime.heap.get(*resumption),Ok(Object::CpsResumption(state))if !state.used));
                                if let Ok(Object::CpsContinuation {
                                    state: Continuation::Delimiter { resumptions, .. },
                                    ..
                                }) = runtime.heap.get_mut(continuation)
                                {
                                    resumptions.clear();
                                }
                                aborted
                            });
                            let outer_scopes = with_runtime(|runtime| {
                                runtime
                                    .cps_delimiters
                                    .iter()
                                    .take_while(|&&delimiter| delimiter != continuation)
                                    .copied()
                                    .chain(std::iter::once(continuation))
                                    .collect::<Vec<_>>()
                            });
                            let mut work = vec![Work::Cross {
                                target: activation,
                                scopes: outer_scopes,
                                base: previous_delimiter_depth,
                                aborted,
                            }];
                            if aborted {
                                work.push(Work::BeginAbort);
                            }
                            work.push(Work::Unwind(activation));
                            if aborted {
                                work.push(Work::EndAbort);
                            }
                            work.push(Work::Budgets(budget_depth));
                            exits::transition(
                                work,
                                After::DelimiterAnswer {
                                    delimiter: continuation,
                                    outer,
                                    handlers,
                                    checkpoint: activation,
                                },
                                value,
                            )
                        }
                        Some(Continuation::BudgetFinish { boundary }) => {
                            budget::finish(boundary, value)
                        }
                        Some(Continuation::ConcurrentFinish { scope }) => {
                            concurrent::finish(scope, Some(value))
                        }
                        Some(Continuation::ForeignCallback { call, request }) => {
                            foreign::callback_return(call, request, value)
                        }
                        Some(Continuation::FinishArm {
                            activation,
                            delimiter,
                        }) => exits::close_return(activation, delimiter, value, None),
                        None => break 0,
                    }
                }
                Step::Handle {
                    definition,
                    body,
                    table,
                    continuation,
                    handlers,
                } => handle(|runtime| {
                    if !matches!(runtime.heap.get(table)?, Object::CpsHandlers(_)) {
                        return Err(RuntimeError::internal("invalid handler table"));
                    }
                    let delimiter = runtime.allocate(Object::CpsContinuation {
                        state: Continuation::Delimiter {
                            outer: continuation,
                            handlers,
                            activation: runtime.cps_activation,
                            resumptions: vec![],
                            budget_depth: runtime.budgets.depth(),
                        },
                        used: false,
                    })?;
                    runtime.cps_delimiters.push(delimiter);
                    let inner = runtime.allocate(Object::CpsHandlerFrame(HandlerFrame {
                        definition,
                        table,
                        parent: handlers,
                        delimiter,
                    }))?;
                    let args = runtime.allocate(Object::Tuple(vec![]))?;
                    runtime.allocate(Object::CpsStep(Step::Call {
                        callable: body,
                        arguments: args,
                        continuation: delimiter,
                        handlers: inner,
                        callback_entry: false,
                    }))
                }),
                Step::Perform {
                    operation,
                    arguments,
                    continuation,
                    handlers,
                } => {
                    let mut yield_current = false;
                    let next = handle(|runtime| {
                        let mut cursor = handlers;
                        while cursor != Handle::INVALID {
                            let Object::CpsHandlerFrame(frame) = runtime.heap.get(cursor)? else {
                                return Err(RuntimeError::internal("invalid handler chain"));
                            };
                            let frame = frame.clone();
                            let Object::CpsHandlers(table) = runtime.heap.get(frame.table)? else {
                                return Err(RuntimeError::internal("invalid handler table"));
                            };
                            if let Some(&arm) = table.get(&operation) {
                                let resumption =
                                    runtime.allocate(Object::CpsResumption(Resumption {
                                        non_resumable: false,
                                        continuation,
                                        handlers,
                                        used: false,
                                        delimiter: frame.delimiter,
                                        activation: runtime.cps_activation,
                                    }))?;
                                if let Object::CpsContinuation {
                                    state: Continuation::Delimiter { resumptions, .. },
                                    ..
                                } = runtime.heap.get_mut(frame.delimiter)?
                                {
                                    resumptions.push(resumption);
                                }
                                let mut args = runtime.sequence(arguments)?;
                                args.push(resumption);
                                let args = runtime.allocate(Object::Tuple(args))?;
                                return runtime.allocate(Object::CpsStep(Step::Call {
                                    callable: arm,
                                    arguments: args,
                                    continuation: frame.delimiter,
                                    handlers: frame.parent,
                                    callback_entry: false,
                                }));
                            }
                            cursor = frame.parent;
                        }
                        if operation == u64::MAX {
                            yield_current = true;
                            let value = runtime.unit()?;
                            return runtime.allocate(Object::CpsStep(Step::Return {
                                continuation,
                                value,
                            }));
                        }
                        Err(RuntimeError::internal(format!(
                            "unhandled effect operation {operation}"
                        )))
                    });
                    if yield_current && next != 0 {
                        ril_rt_root(0, next);
                        driver.current = next;
                        driver.fault_unwinding = fault_unwinding;
                        driver.fault_checkpoint = fault_checkpoint;
                        return std::task::Poll::Pending;
                    }
                    next
                }
                Step::Resume {
                    resumption,
                    value,
                    next,
                } => {
                    let arm_activation = with_runtime(|runtime| runtime.cps_activation);
                    let state: Option<(Handle, Handle, Handle, Handle)> = guarded(|runtime| {
                        let Object::CpsResumption(state) = runtime.heap.get(resumption)? else {
                            return Err(RuntimeError::internal("invalid resumption"));
                        };
                        let state = state.clone();
                        if state.non_resumable {
                            return Err(RuntimeError::internal(
                                "budget exhaustion is non-resumable",
                            ));
                        }
                        if state.used {
                            return Err(RuntimeError::internal("resumption used more than once"));
                        }
                        let Object::CpsContinuation {
                            state: Continuation::Delimiter { resumptions, .. },
                            used,
                        } = runtime.heap.get(state.delimiter)?
                        else {
                            return Err(RuntimeError::internal("invalid resumption delimiter"));
                        };
                        if *used || !resumptions.contains(&resumption) {
                            return Err(RuntimeError::internal("resumption scope has ended"));
                        }
                        let Object::CpsResumption(stored) = runtime.heap.get_mut(resumption)?
                        else {
                            unreachable!()
                        };
                        stored.used = true;
                        if let Object::CpsContinuation {
                            state: Continuation::Delimiter { resumptions, .. },
                            ..
                        } = runtime.heap.get_mut(state.delimiter)?
                        {
                            resumptions.retain(|&handle| handle != resumption);
                        }
                        Ok(Some((
                            state.continuation,
                            state.handlers,
                            state.delimiter,
                            state.activation,
                        )))
                    });
                    let Some((continuation, handlers, delimiter, activation)) = state else {
                        break 0;
                    };
                    let empty_arm = next.is_none()
                        && arm_activation != Handle::INVALID
                        && arm_activation != activation
                        && with_runtime(|runtime| {
                            runtime
                                .activation(arm_activation)
                                .is_ok_and(|state| state.cleanups.is_empty())
                                && !runtime
                                    .concurrent_scopes
                                    .iter()
                                    .any(|scope| scope.activation == arm_activation)
                                && !runtime
                                    .foreign_calls
                                    .values()
                                    .any(|call| call.activation == arm_activation)
                        });
                    if empty_arm {
                        close_empty_activation(arm_activation);
                    }
                    let next = if !empty_arm
                        && next.is_none()
                        && arm_activation != Handle::INVALID
                        && arm_activation != activation
                    {
                        let finish = handle(|runtime| {
                            runtime.allocate(Object::CpsContinuation {
                                state: Continuation::FinishArm {
                                    activation: arm_activation,
                                    delimiter,
                                },
                                used: false,
                            })
                        });
                        if finish == 0 {
                            break 0;
                        }
                        Some(Handle(finish))
                    } else {
                        next
                    };
                    if let Some(next) = next {
                        let valid: bool = guarded(|runtime| {
                            if !matches!(
                                runtime.heap.get(delimiter)?,
                                Object::CpsContinuation {
                                    state: Continuation::Delimiter { .. },
                                    ..
                                }
                            ) {
                                return Err(RuntimeError::internal(
                                    "resumption answer has no delimiter",
                                ));
                            }
                            runtime.heap.get(next)?;
                            runtime.cps_resume_returns.push((delimiter, next));
                            Ok(true)
                        });
                        if !valid {
                            break 0;
                        }
                    }
                    with_runtime(|runtime| runtime.cps_activation = activation);
                    set_handlers(handlers);
                    return_step(continuation, value.0)
                }
            };
        };
        if result == 0
            && let Some(next) = exits::recover(previous_exit_depth)
        {
            current = next;
            continue;
        }
        if result == 0 && fault_unwinding {
            let checkpoint = with_runtime(|runtime| {
                (
                    runtime.cps_activation,
                    runtime.cps_delimiters.clone(),
                    runtime.cps_resume_returns.clone(),
                )
            });
            if checkpoint.0 == previous_activation
                && checkpoint.1 == previous_scopes
                && checkpoint.2.len() == previous_return_depth
            {
                break 0;
            }
            // A cleanup's nonlocal exit may replace the scheduled fault
            // unwind. Continue the remaining outer region, but never retry a
            // corrupt control graph that made no progress.
            if fault_checkpoint.as_ref() == Some(&checkpoint) {
                break 0;
            }
        }
        if result == 0
            && let Some(next) = concurrent::recover(previous_concurrent_depth)
        {
            current = next;
            continue;
        }
        if result == 0 && ril_rt_status() != 0 {
            fault_unwinding = true;
            fault_checkpoint = Some(with_runtime(|runtime| {
                (
                    runtime.cps_activation,
                    runtime.cps_delimiters.clone(),
                    runtime.cps_resume_returns.clone(),
                )
            }));
            current = exits::unwind_fault(
                previous_activation,
                previous_scopes.clone(),
                previous_budget_depth,
            );
            continue;
        }
        break result;
    };
    let result =
        if result != 0 && with_runtime(|runtime| runtime.cps_exits.len() != previous_exit_depth) {
            with_runtime(|runtime| {
                runtime.fault = Some(RuntimeError::internal(
                    "native computation completed with unfinished logical cleanup",
                ))
            });
            0
        } else {
            result
        };
    set_handlers(previous);
    with_runtime(|runtime| {
        runtime.cps_resume_returns.truncate(previous_return_depth);
        runtime.cps_delimiters.truncate(previous_delimiter_depth);
        runtime.cps_activation = previous_activation;
    });
    driver.completed = true;
    std::task::Poll::Ready(ril_rt_leave(result))
}

/// The logical runtime owns all suspended roots and moves with the driver.
/// Host waits are still synchronous until their pending-operation adapters land.
struct NativeComputation {
    runtime: Option<Runtime>,
    driver: Option<Driver>,
    initial: u64,
}

struct NativeCompletion {
    runtime: Runtime,
    value: u64,
}

fn native_executor() -> Result<crate::scheduler::Executor> {
    RUNTIME.with_borrow_mut(|runtime| {
        if runtime.executor.is_none() {
            runtime.executor =
                Some(crate::scheduler::native_executor().map_err(RuntimeError::internal)?);
        }
        Ok(runtime
            .executor
            .as_ref()
            .expect("initialized executor")
            .clone())
    })
}

/// Short native setup/publication with a task-owned Runtime. Restore the
/// worker's previous TLS state even if an unexpected host failure occurs.
fn with_owned_runtime<T>(runtime: &mut Runtime, operation: impl FnOnce() -> T) -> T {
    let previous =
        RUNTIME.with_borrow_mut(|current| std::mem::replace(current, std::mem::take(runtime)));
    let outcome = catch_unwind(AssertUnwindSafe(operation));
    *runtime = RUNTIME.with_borrow_mut(|current| std::mem::replace(current, previous));
    match outcome {
        Ok(value) => value,
        Err(error) => std::panic::resume_unwind(error),
    }
}

impl NativeComputation {
    fn new(runtime: Runtime, initial: u64) -> Self {
        Self {
            runtime: Some(runtime),
            driver: None,
            initial,
        }
    }
}

impl std::future::Future for NativeComputation {
    type Output = NativeCompletion;

    fn poll(
        self: std::pin::Pin<&mut Self>,
        context: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        let this = self.get_mut();
        let runtime = this
            .runtime
            .take()
            .expect("completed native computation polled again");
        let previous = RUNTIME.with_borrow_mut(|current| std::mem::replace(current, runtime));
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            let driver = this
                .driver
                .get_or_insert_with(|| start_driver(this.initial));
            drive_with_context(driver, std::num::NonZeroUsize::new(64).unwrap(), context)
        }));
        let mut runtime = RUNTIME.with_borrow_mut(|current| std::mem::replace(current, previous));
        match outcome {
            Ok(std::task::Poll::Pending) => {
                this.runtime = Some(runtime);
                if this
                    .driver
                    .as_ref()
                    .is_none_or(|driver| driver.pending.is_none())
                {
                    context.waker().wake_by_ref();
                }
                std::task::Poll::Pending
            }
            Ok(std::task::Poll::Ready(value)) => {
                std::task::Poll::Ready(NativeCompletion { runtime, value })
            }
            Err(_) => {
                runtime.fault = Some(RuntimeError::internal(
                    "unexpected Rust panic in native trampoline",
                ));
                std::task::Poll::Ready(NativeCompletion { runtime, value: 0 })
            }
        }
    }
}

fn run(initial: u64) -> u64 {
    let runtime = RUNTIME.with_borrow_mut(std::mem::take);
    let mut computation = std::pin::pin!(NativeComputation::new(runtime, initial));
    let wake = std::sync::Arc::new(DriverWake::default());
    let waker = std::task::Waker::from(wake.clone());
    let mut context = std::task::Context::from_waker(&waker);
    loop {
        if let std::task::Poll::Ready(NativeCompletion { runtime, value }) =
            std::future::Future::poll(computation.as_mut(), &mut context)
        {
            RUNTIME.with_borrow_mut(|current| *current = runtime);
            return value;
        }
        wake.wait();
    }
}

#[derive(Default)]
struct DriverWake {
    notified: std::sync::Mutex<bool>,
    wake: std::sync::Condvar,
}
impl DriverWake {
    fn wait(&self) {
        let mut notified = self.notified.lock().unwrap_or_else(|e| e.into_inner());
        while !*notified {
            notified = self.wake.wait(notified).unwrap_or_else(|e| e.into_inner());
        }
        *notified = false;
    }
}
impl std::task::Wake for DriverWake {
    fn wake(self: std::sync::Arc<Self>) {
        self.wake_by_ref();
    }
    fn wake_by_ref(self: &std::sync::Arc<Self>) {
        *self.notified.lock().unwrap_or_else(|e| e.into_inner()) = true;
        self.wake.notify_one();
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_run(initial: u64) -> u64 {
    match catch_unwind(AssertUnwindSafe(|| run(initial))) {
        Ok(value) => value,
        Err(_) => {
            with_runtime(|runtime| {
                runtime.fault = Some(RuntimeError::internal(
                    "unexpected Rust panic in native trampoline",
                ))
            });
            0
        }
    }
}

#[cfg(test)]
#[path = "cps_cleanup_tests.rs"]
mod cleanup_tests;
#[cfg(test)]
#[path = "ffi_driver_tests.rs"]
mod driver_tests;
#[cfg(test)]
#[path = "cps_redirect_tests.rs"]
mod redirect_tests;
#[cfg(test)]
mod tests {
    use super::*;
    fn args(value: u64) -> Vec<Handle> {
        with_runtime(|runtime| runtime.sequence(Handle(value)).unwrap())
    }
    extern "C" fn after(environment: u64, arguments: u64) -> u64 {
        ril_rt_enter();
        ril_rt_root(0, environment);
        ril_rt_root(1, arguments);
        let value = args(arguments)[0].0;
        for _ in 0..1500 {
            ril_rt_unit();
        }
        let two = ril_rt_int(2, 0, 64, 1);
        let value = ril_rt_binary(BinaryOp::Multiply as u32, value, two);
        let step = ril_rt_cps_return(environment, value);
        ril_rt_leave(step)
    }
    extern "C" fn request(_environment: u64, arguments: u64) -> u64 {
        ril_rt_enter();
        ril_rt_root(0, arguments);
        let outer = args(arguments).last().unwrap().0;
        let continuation = ril_rt_cps_continuation(after as *const () as usize as u64, outer);
        let argument = ril_rt_int(7, 0, 64, 1);
        let arguments = ril_rt_sequence(1);
        ril_rt_push(arguments, argument);
        let step = ril_rt_cps_perform(7, arguments, continuation);
        ril_rt_leave(step)
    }
    extern "C" fn resume_plus_one(_environment: u64, arguments: u64) -> u64 {
        ril_rt_enter();
        ril_rt_root(0, arguments);
        let arguments = args(arguments);
        let one = ril_rt_int(1, 0, 64, 1);
        let value = ril_rt_binary(BinaryOp::Add as u32, arguments[0].0, one);
        let step = ril_rt_cps_resume(arguments[1].0, value);
        ril_rt_leave(step)
    }
    extern "C" fn abort(_environment: u64, arguments: u64) -> u64 {
        ril_rt_enter();
        ril_rt_root(0, arguments);
        let arguments = args(arguments);
        let value = ril_rt_int(99, 0, 64, 1);
        let step = ril_rt_cps_return(arguments.last().unwrap().0, value);
        ril_rt_leave(step)
    }
    fn callable(address: extern "C" fn(u64, u64) -> u64, environment: u64) -> u64 {
        ril_rt_cps_callable(address as *const () as usize as u64, environment)
    }
    #[test]
    fn tail_resumption_continues_native_code_and_abort_skips_the_suspended_continuation() {
        for (handler, expected) in [
            (resume_plus_one as extern "C" fn(u64, u64) -> u64, 16),
            (abort, 99),
        ] {
            ril_rt_init();
            ril_rt_enter();
            let environment = ril_rt_unit();
            let body = callable(request, environment);
            let arm = callable(handler, environment);
            let table = ril_rt_cps_handlers();
            ril_rt_cps_handler_add(table, 7, arm);
            let end = ril_rt_cps_end();
            let step = ril_rt_cps_handle(body, table, end, 0);
            let value = ril_rt_cps_run(step);
            assert_ne!(value, 0);
            assert_eq!(ril_rt_status(), 0);
            with_runtime(|runtime| {
                assert_eq!(runtime.as_integer(Handle(value)).unwrap(), expected)
            });
            ril_rt_leave(value);
        }
    }
    extern "C" fn countdown(environment: u64, arguments: u64) -> u64 {
        ril_rt_enter();
        ril_rt_root(0, environment);
        ril_rt_root(1, arguments);
        let outer = args(arguments).last().unwrap().0;
        let remaining = handle(|runtime| runtime.field(Handle(environment), "remaining"));
        let left = with_runtime(|runtime| runtime.as_integer(Handle(remaining)).unwrap());
        let step = if left == 0 {
            let value = handle(|runtime| runtime.field(Handle(environment), "value"));
            ril_rt_cps_return(outer, value)
        } else {
            let remaining = ril_rt_int((left - 1) as u64, 0, 64, 1);
            handle(|runtime| {
                runtime.set_field(Handle(environment), "remaining".into(), Handle(remaining))
            });
            let callback = handle(|runtime| runtime.field(Handle(environment), "self"));
            let arguments = ril_rt_sequence(1);
            ril_rt_cps_call(callback, arguments, outer)
        };
        ril_rt_leave(step)
    }
    #[test]
    fn trampoline_has_bounded_native_stack_and_precisely_roots_suspended_cycles() {
        trampoline_roots(false);
    }
    #[test]
    fn shared_heap_trampoline_keeps_suspended_cycles_precisely_rooted() {
        trampoline_roots(true);
    }
    fn trampoline_roots(shared: bool) {
        ril_rt_init();
        if shared {
            with_runtime(crate::shared::activate);
        }
        ril_rt_enter();
        let environment = handle(|runtime| {
            let remaining = runtime.int(5000)?;
            let value = runtime.string("survives".into())?;
            runtime.allocate(Object::Record(
                [("remaining".into(), remaining), ("value".into(), value)].into(),
            ))
        });
        let callback = callable(countdown, environment);
        handle(|runtime| runtime.set_field(Handle(environment), "self".into(), Handle(callback)));
        let end = ril_rt_cps_end();
        let arguments = ril_rt_sequence(1);
        let step = ril_rt_cps_call(callback, arguments, end);
        ril_rt_root(0, step);
        ril_rt_statement_end();
        let value = ril_rt_cps_run(step);
        assert_ne!(value, 0);
        assert_eq!(ril_rt_status(), 0);
        with_runtime(|runtime| assert_eq!(runtime.as_string(Handle(value)).unwrap(), "survives"));
        ril_rt_leave(value);
    }
    #[test]
    fn resumption_is_affine_even_if_a_malformed_native_client_reuses_it() {
        ril_rt_init();
        ril_rt_enter();
        let end = ril_rt_cps_end();
        let delimiter = handle(|runtime| {
            runtime.allocate(Object::CpsContinuation {
                state: Continuation::Delimiter {
                    outer: Handle(end),
                    handlers: Handle::INVALID,
                    activation: Handle::INVALID,
                    resumptions: vec![],
                    budget_depth: runtime.budgets.depth(),
                },
                used: false,
            })
        });
        let resumption = handle(|runtime| {
            runtime.allocate(Object::CpsResumption(Resumption {
                non_resumable: false,
                continuation: Handle(end),
                handlers: Handle::INVALID,
                used: false,
                delimiter: Handle(delimiter),
                activation: Handle::INVALID,
            }))
        });
        with_runtime(|runtime| {
            let Object::CpsContinuation {
                state: Continuation::Delimiter { resumptions, .. },
                ..
            } = runtime.heap.get_mut(Handle(delimiter)).unwrap()
            else {
                unreachable!()
            };
            resumptions.push(Handle(resumption));
        });
        let value = ril_rt_int(42, 0, 64, 1);
        let step = ril_rt_cps_resume(resumption, value);
        assert_eq!(ril_rt_cps_run(step), value);
        let step = ril_rt_cps_resume(resumption, value);
        assert_eq!(ril_rt_cps_run(step), 0);
        with_runtime(|runtime| {
            assert_eq!(
                runtime.fault.as_ref().unwrap().message,
                "resumption used more than once"
            )
        });
        ril_rt_leave(0);
    }
    extern "C" fn forward_to_outer(_environment: u64, arguments: u64) -> u64 {
        ril_rt_enter();
        ril_rt_root(0, arguments);
        let args = args(arguments);
        let value = handle(|runtime| {
            let value = runtime.as_integer(args[0])?;
            if value > 20 {
                return Err(RuntimeError::panic("handler masking failed"));
            }
            runtime.int(value + 1)
        });
        let request_args = ril_rt_sequence(1);
        ril_rt_push(request_args, value);
        let step = ril_rt_cps_perform(7, request_args, args.last().unwrap().0);
        ril_rt_leave(step)
    }
    extern "C" fn resume_plus_hundred(_environment: u64, arguments: u64) -> u64 {
        ril_rt_enter();
        ril_rt_root(0, arguments);
        let args = args(arguments);
        let hundred = ril_rt_int(100, 0, 64, 1);
        let value = ril_rt_binary(BinaryOp::Add as u32, args[0].0, hundred);
        let step = ril_rt_cps_resume(args[1].0, value);
        ril_rt_leave(step)
    }
    extern "C" fn inner_handler(table: u64, arguments: u64) -> u64 {
        ril_rt_enter();
        ril_rt_root(0, table);
        ril_rt_root(1, arguments);
        let outer = args(arguments).last().unwrap().0;
        let environment = ril_rt_unit();
        let body = callable(request, environment);
        let step = ril_rt_cps_handle(body, table, outer, 0);
        ril_rt_leave(step)
    }
    #[test]
    fn an_arm_runs_outside_its_selected_handler_and_resume_restores_the_request_chain() {
        ril_rt_init();
        ril_rt_enter();
        let environment = ril_rt_unit();
        let inner = ril_rt_cps_handlers();
        let forward = callable(forward_to_outer, environment);
        ril_rt_cps_handler_add(inner, 7, forward);
        let body = callable(inner_handler, inner);
        let outer = ril_rt_cps_handlers();
        let resume = callable(resume_plus_hundred, environment);
        ril_rt_cps_handler_add(outer, 7, resume);
        let end = ril_rt_cps_end();
        let initial = ril_rt_cps_handle(body, outer, end, 0);
        let value = ril_rt_cps_run(initial);
        assert_eq!(ril_rt_status(), 0);
        assert_ne!(value, 0);
        with_runtime(|runtime| assert_eq!(runtime.as_integer(Handle(value)).unwrap(), 108));
        ril_rt_leave(value);
    }
    extern "C" fn arm_after_resume(abort: u64, arguments: u64) -> u64 {
        ril_rt_enter();
        ril_rt_root(0, abort);
        ril_rt_root(1, arguments);
        let value = args(arguments)[0].0;
        let one = ril_rt_int(1, 0, 64, 1);
        let value = ril_rt_binary(BinaryOp::Add as u32, value, one);
        let step = ril_rt_cps_return(abort, value);
        ril_rt_leave(step)
    }
    extern "C" fn resume_then_continue(_environment: u64, arguments: u64) -> u64 {
        ril_rt_enter();
        ril_rt_root(0, arguments);
        let args = args(arguments);
        let one = ril_rt_int(1, 0, 64, 1);
        let value = ril_rt_binary(BinaryOp::Add as u32, args[0].0, one);
        let after = ril_rt_cps_continuation(
            arm_after_resume as *const () as usize as u64,
            args.last().unwrap().0,
        );
        let step = ril_rt_cps_resume_then(args[1].0, value, after);
        ril_rt_leave(step)
    }
    #[test]
    fn explicit_resume_answer_returns_to_the_arm_before_its_final_delimited_answer() {
        ril_rt_init();
        ril_rt_enter();
        let environment = ril_rt_unit();
        let body = callable(request, environment);
        let arm = callable(resume_then_continue, environment);
        let table = ril_rt_cps_handlers();
        ril_rt_cps_handler_add(table, 7, arm);
        let end = ril_rt_cps_end();
        let initial = ril_rt_cps_handle(body, table, end, 0);
        let value = ril_rt_cps_run(initial);
        assert_eq!(ril_rt_status(), 0);
        assert_ne!(value, 0);
        with_runtime(|runtime| {
            assert_eq!(runtime.as_integer(Handle(value)).unwrap(), 17);
            assert!(runtime.cps_resume_returns.is_empty());
        });
        ril_rt_leave(value);
    }
    #[test]
    fn the_default_environment_services_only_the_reserved_cooperative_yield_identity() {
        ril_rt_init();
        ril_rt_enter();
        let args = ril_rt_sequence(1);
        let end = ril_rt_cps_end();
        let step = ril_rt_cps_perform(u64::MAX, args, end);
        let value = ril_rt_cps_run(step);
        assert_eq!(ril_rt_status(), 0);
        with_runtime(|runtime| assert_eq!(runtime.heap.get(Handle(value)).unwrap(), &Object::Unit));
        let end = ril_rt_cps_end();
        let step = ril_rt_cps_perform(42, args, end);
        assert_eq!(ril_rt_cps_run(step), 0);
        with_runtime(|runtime| {
            assert_eq!(
                runtime.fault.as_ref().unwrap().message,
                "unhandled effect operation 42"
            )
        });
        ril_rt_leave(0);
    }
    #[test]
    fn abort_expires_unused_resumptions_before_their_native_continuation_can_run() {
        ril_rt_init();
        ril_rt_enter();
        let end = ril_rt_cps_end();
        let delimiter = handle(|runtime| {
            runtime.allocate(Object::CpsContinuation {
                state: Continuation::Delimiter {
                    outer: Handle(end),
                    handlers: Handle::INVALID,
                    activation: Handle::INVALID,
                    resumptions: vec![],
                    budget_depth: runtime.budgets.depth(),
                },
                used: false,
            })
        });
        let continuation = ril_rt_cps_continuation(after as *const () as usize as u64, delimiter);
        let resumption = handle(|runtime| {
            runtime.allocate(Object::CpsResumption(Resumption {
                non_resumable: false,
                continuation: Handle(continuation),
                handlers: Handle::INVALID,
                used: false,
                delimiter: Handle(delimiter),
                activation: Handle::INVALID,
            }))
        });
        let value = ril_rt_int(99, 0, 64, 1);
        let abort = ril_rt_cps_return(delimiter, value);
        assert_eq!(ril_rt_cps_run(abort), value);
        let stale = ril_rt_cps_resume(resumption, value);
        assert_eq!(ril_rt_cps_run(stale), 0);
        with_runtime(|runtime| {
            assert_eq!(
                runtime.fault.as_ref().unwrap().message,
                "resumption scope has ended"
            );
            assert!(matches!(
                runtime.heap.get(Handle(continuation)).unwrap(),
                Object::CpsContinuation { used: false, .. }
            ));
        });
        ril_rt_leave(0);
    }
}
