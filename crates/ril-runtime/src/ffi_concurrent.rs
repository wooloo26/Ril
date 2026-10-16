//! Structured boundaries inside the one native-step trampoline. Scope bodies
//! keep their caller's handlers; child tasks start fresh execution contexts.
use super::*;
use crate::concurrent::{ActiveScope, Scope, Task, fault_rank};
use std::sync::Arc;

pub(super) fn dispatch(
    callable: Handle,
    arguments: Handle,
    continuation: Handle,
    handlers: Handle,
) -> Option<u64> {
    let name = with_runtime(|runtime| match runtime.heap.get(callable) {
        Ok(Object::Builtin(name)) => {
            Some(name.strip_prefix("Prelude::").unwrap_or(name).to_owned())
        }
        _ => None,
    })?;
    match name.as_str() {
        "Concurrent::scope" => Some(enter(arguments, continuation, handlers)),
        "Concurrent::fork" => Some(fork(arguments, continuation)),
        "Concurrent::join" => Some(join(arguments, continuation)),
        _ => None,
    }
}

fn enter(arguments: Handle, continuation: Handle, handlers: Handle) -> u64 {
    RUNTIME.with_borrow_mut(crate::shared::activate);
    handle(|runtime| {
        let arguments = runtime.sequence(arguments)?;
        let [body] = arguments.as_slice() else {
            return Err(RuntimeError::internal("scope requires one body"));
        };
        let parent_cancellation = runtime.cancellation.clone();
        let scope = Scope::new(&parent_cancellation)?;
        let value = runtime.allocate(Object::TaskScope(scope.clone()))?;
        let parent_activation = runtime.cps_activation;
        let activation = runtime.new_activation()?;
        runtime.cps_activation = activation;
        runtime.cancellation = scope.body_cancellation.clone();
        let lineage_depth = runtime.scope_lineage.len();
        runtime.scope_lineage.push(scope.id());
        runtime.scope_registry.push(scope.clone());
        runtime.concurrent_scopes.push(ActiveScope {
            scope,
            value,
            continuation,
            handlers,
            activation,
            parent_activation,
            parent_cancellation,
            lineage_depth,
            delimiters: runtime.cps_delimiters.clone(),
            budget_depth: runtime.budgets.depth(),
        });
        let finish = runtime.allocate(Object::CpsContinuation {
            state: Continuation::ConcurrentFinish { scope: value },
            used: false,
        })?;
        let args = runtime.allocate(Object::Tuple(vec![value]))?;
        runtime.allocate(Object::CpsStep(Step::Call {
            callable: *body,
            arguments: args,
            continuation: finish,
            handlers,
            callback_entry: false,
        }))
    })
}

fn fork(arguments: Handle, continuation: Handle) -> u64 {
    let prepared: Option<(Handle, Handle, Arc<Task>)> = guarded(|runtime| {
        let arguments = runtime.sequence(arguments)?;
        let [scope_handle, action] = arguments.as_slice() else {
            return Err(RuntimeError::internal(
                "fork requires a scope and an action",
            ));
        };
        let Object::TaskScope(scope) = runtime.heap.get(*scope_handle)? else {
            return Err(RuntimeError::internal("fork receiver is not a scope"));
        };
        let task = scope.reserve(*action, runtime.task_owner)?;
        let value = runtime.allocate(Object::Task(task.clone()))?;
        Ok(Some((*scope_handle, value, task)))
    });
    let Some((scope_handle, value, task)) = prepared else {
        return 0;
    };
    let executor = match native_executor() {
        Ok(executor) => executor,
        Err(error) => {
            let _ = task.complete(Err(error.clone()));
            with_runtime(|runtime| runtime.fault = Some(error));
            return 0;
        }
    };
    // Registration locks the shared group, so it must not run inside a heap access.
    let child = RUNTIME.with_borrow(|runtime| {
        crate::shared::fork_runtime(
            runtime,
            &[scope_handle, value, task.action()],
            task.cancellation.clone(),
        )
    });
    let mut child = match child {
        Ok(child) => child,
        Err(error) => {
            let _ = with_runtime(|_| task.complete(Err(error.clone())));
            with_runtime(|runtime| runtime.fault = Some(error));
            return 0;
        }
    };
    child.task_owner = task.owner();
    let owning_scope = with_runtime(|runtime| match runtime.heap.get(scope_handle) {
        Ok(Object::TaskScope(scope)) => Some(scope.id()),
        _ => None,
    });
    let Some(scope_end) = child
        .scope_lineage
        .iter()
        .position(|scope| Some(*scope) == owning_scope)
    else {
        let error = RuntimeError::internal("fork scope is not an active ancestor");
        let _ = with_runtime(|_| task.complete(Err(error.clone())));
        with_runtime(|runtime| runtime.fault = Some(error));
        return 0;
    };
    child.scope_lineage.truncate(scope_end + 1);
    child.scope_registry.truncate(scope_end + 1);
    let captured = with_runtime(|runtime| {
        runtime.transfer_captured_tickets(
            task.action(),
            crate::channel::Context {
                owner: child.task_owner,
                lineage: &child.scope_lineage,
            },
        )
    });
    match captured {
        Ok(tickets) => child.owned_tickets.extend(tickets),
        Err(error) => {
            let _ = with_runtime(|_| task.complete(Err(error.clone())));
            with_runtime(|runtime| runtime.fault = Some(error));
            return 0;
        }
    }
    // Construct the guard before submission: a refused/never-polled task still
    // owns transferred channel authority and must release it before retiring.
    let state = TaskExecution {
        runtime: Some(child),
        task: task.clone(),
        published: false,
    };
    let worker = executor.spawn(execute_task(state));
    match worker {
        Ok(worker) => {
            if let Err(error) = task.install_scheduled(worker) {
                with_runtime(|runtime| runtime.fault = Some(error));
                return 0;
            }
        }
        Err(error) => {
            let error = RuntimeError::internal(format!("cannot submit task worker: {error:?}"));
            let _ = with_runtime(|_| task.complete(Err(error.clone())));
            with_runtime(|runtime| runtime.fault = Some(error));
            return 0;
        }
    }
    return_step(continuation, value.0)
}

struct TaskExecution {
    runtime: Option<Runtime>,
    task: Arc<Task>,
    published: bool,
}
impl Drop for TaskExecution {
    fn drop(&mut self) {
        if !self.published {
            if let Some(runtime) = &mut self.runtime {
                let _ = catch_unwind(AssertUnwindSafe(|| {
                    with_owned_runtime(runtime, cleanup_task_channels)
                }));
            }
            let _ = self.task.complete(Err(RuntimeError::internal(
                "task execution did not publish its outcome",
            )));
        }
    }
}
async fn execute_task(mut state: TaskExecution) -> Result<()> {
    let action = state.task.action();
    let initial = with_owned_runtime(
        state.runtime.as_mut().expect("unstarted task runtime"),
        || {
            handle(|runtime| {
                let continuation = runtime.allocate(Object::CpsContinuation {
                    state: Continuation::End,
                    used: false,
                })?;
                let arguments = runtime.allocate(Object::Tuple(vec![]))?;
                runtime.allocate(Object::CpsStep(Step::Call {
                    callable: action,
                    arguments,
                    continuation,
                    handlers: Handle::INVALID,
                    callback_entry: false,
                }))
            })
        },
    );
    let NativeCompletion { runtime, value } =
        NativeComputation::new(state.runtime.take().expect("task runtime"), initial).await;
    state.runtime = Some(runtime);
    let result = with_owned_runtime(
        state.runtime.as_mut().expect("completed task runtime"),
        || {
            let outcome = with_runtime(|runtime| match runtime.fault.take() {
                Some(error) => Err(error),
                None if value == 0 => Err(RuntimeError::internal("task returned no managed value")),
                None => {
                    let lineage = runtime.scope_lineage.clone();
                    runtime.reissue_returned_tickets(
                        Handle(value),
                        crate::channel::Context {
                            owner: state.task.creator(),
                            lineage: &lineage,
                        },
                    )
                }
            });
            cleanup_task_channels();
            // Publication and the temporary result root overlap under the heap gate.
            with_runtime(|_| state.task.complete(outcome))
        },
    );
    state.published = result.is_ok();
    // Scope draining awaits this future's completion as well as its outcome,
    // so all task-specific roots retire before the owning scope can close.
    result
}

fn join_target(
    runtime: &Runtime,
    arguments: Handle,
) -> Result<(Arc<Task>, Arc<crate::process_io::Cancellation>)> {
    let arguments = runtime.sequence(arguments)?;
    let [task] = arguments.as_slice() else {
        return Err(RuntimeError::internal("join requires one task"));
    };
    let Object::Task(task) = runtime.heap.get(*task)? else {
        return Err(RuntimeError::internal("join receiver is not a task"));
    };
    if task.creator() != runtime.task_owner || !runtime.scope_lineage.contains(&task.scope_id()) {
        return Err(RuntimeError::panic("task join crossed its owner or scope"));
    }
    Ok((task.clone(), runtime.cancellation.clone()))
}

pub(super) fn prepare_join(
    runtime: &Runtime,
    arguments: Handle,
) -> Result<crate::concurrent::JoinFuture> {
    let (task, cancellation) = join_target(runtime, arguments)?;
    Ok(task.join_async(cancellation))
}

fn join(arguments: Handle, continuation: Handle) -> u64 {
    let prepared: Option<(Arc<Task>, Arc<crate::process_io::Cancellation>)> =
        guarded(|runtime| join_target(runtime, arguments).map(Some));
    let Some((task, cancellation)) = prepared else {
        return 0;
    };
    let outcome = task.join(&cancellation);
    finish_join(outcome, continuation)
}

pub(super) fn finish_join(outcome: Result<Result<Handle>>, continuation: Handle) -> u64 {
    let value = handle(|runtime| match outcome? {
        Ok(value) => {
            runtime.adopt_received_tickets(value)?;
            runtime.variant("Ok", vec![value])
        }
        Err(error) => {
            let fault = encode_fault(runtime, &error)?;
            runtime.variant("Err", vec![fault])
        }
    });
    if value == 0 {
        0
    } else {
        return_step(continuation, value)
    }
}

pub(super) fn finish(scope: Handle, body: Option<Handle>) -> u64 {
    // Recovery still carries the failed scope's cancelled body token. The
    // mandatory drain restores its parent token before ordinary cancellation
    // points resume; allocating this control step must not restart recovery.
    guarded_control(|runtime| {
        runtime
            .allocate(Object::CpsStep(Step::ConcurrentDrain { scope, body }))
            .map(|step| step.0)
    })
}

pub(super) struct PendingFinish {
    future: crate::concurrent::FinishFuture,
    context: ActiveScope,
    body: Option<Handle>,
    body_fault: Option<RuntimeError>,
}

pub(super) fn prepare_finish(scope: Handle, body: Option<Handle>) -> Result<PendingFinish> {
    let context = with_runtime(|runtime| runtime.concurrent_scopes.last().cloned());
    let Some(context) = context.filter(|context| context.value == scope) else {
        return Err(RuntimeError::internal(
            "scope completion belongs to another boundary",
        ));
    };
    let body_fault =
        with_runtime(|runtime| body.map(|body| decode_body(runtime, body)).transpose())?.flatten();
    let future = context
        .scope
        .finish_async(body_fault.is_some() || body.is_none());
    Ok(PendingFinish {
        future,
        context,
        body,
        body_fault,
    })
}

pub(super) fn poll_finish(
    pending: &mut PendingFinish,
    context: &mut std::task::Context<'_>,
) -> std::task::Poll<u64> {
    let std::task::Poll::Ready(children) =
        std::future::Future::poll(std::pin::Pin::new(&mut pending.future), context)
    else {
        return std::task::Poll::Pending;
    };
    std::task::Poll::Ready(complete_finish(
        pending.context.clone(),
        pending.body,
        pending.body_fault.clone(),
        children,
    ))
}

fn complete_finish(
    context: ActiveScope,
    body: Option<Handle>,
    body_fault: Option<RuntimeError>,
    children: Result<Option<RuntimeError>>,
) -> u64 {
    let result = with_runtime(|runtime| {
        runtime.cancellation = context.parent_cancellation.clone();
        let child = children?;
        if let Some(error) = &child
            && error.tag == OutcomeTag::InternalFault
        {
            return Err(error.clone());
        }
        let selected = match (&body_fault, &child) {
            (Some(body), Some(child)) => fault_rank(child) > fault_rank(body),
            (None, Some(_)) => true,
            _ => false,
        };
        let value = if selected {
            let fault = encode_fault(runtime, child.as_ref().expect("selected child failure"))?;
            runtime.variant("Err", vec![fault])?
        } else if let Some(body) = body {
            body
        } else {
            return Err(RuntimeError::internal(
                "cancelled scope has no failure cause",
            ));
        };
        for root in context.references() {
            runtime.keep_temporary(root);
        }
        runtime.keep_temporary(value);
        runtime.concurrent_scopes.pop();
        runtime.scope_lineage.truncate(context.lineage_depth);
        runtime.scope_registry.truncate(context.lineage_depth);
        retire_scope_channels(runtime, context.scope.id());
        Ok(value)
    });
    let value = match result {
        Ok(value) => value,
        Err(error) => {
            with_runtime(|runtime| runtime.fault = Some(error));
            return 0;
        }
    };
    exits::close_return(
        context.activation,
        context.continuation,
        value,
        Some(context.handlers),
    )
}

pub(super) fn closing_step(owner: u64, activation: Handle) -> Option<u64> {
    let context = with_runtime(|runtime| runtime.concurrent_scopes.last().cloned());
    let context = context.filter(|context| context.activation == activation)?;
    Some(handle(|runtime| {
        runtime.allocate(Object::CpsStep(Step::ConcurrentClose {
            scope: context.value,
            activation,
            owner,
        }))
    }))
}

pub(super) struct PendingClose {
    future: crate::concurrent::FinishFuture,
    context: ActiveScope,
    owner: u64,
}
pub(super) fn prepare_close(scope: Handle, activation: Handle, owner: u64) -> Result<PendingClose> {
    let context = with_runtime(|runtime| runtime.concurrent_scopes.last().cloned());
    let context = context
        .filter(|context| context.value == scope && context.activation == activation)
        .ok_or_else(|| RuntimeError::internal("scope close belongs to another boundary"))?;
    let future = context.scope.finish_async(true);
    Ok(PendingClose {
        future,
        context,
        owner,
    })
}
pub(super) fn poll_close(
    pending: &mut PendingClose,
    context: &mut std::task::Context<'_>,
) -> std::task::Poll<u64> {
    let std::task::Poll::Ready(children) =
        std::future::Future::poll(std::pin::Pin::new(&mut pending.future), context)
    else {
        return std::task::Poll::Pending;
    };
    std::task::Poll::Ready(exits::complete_scope_close(
        pending.owner,
        pending.context.clone(),
        children,
    ))
}
pub(super) fn complete_close(context: ActiveScope, children: Result<Option<RuntimeError>>) {
    with_runtime(|runtime| {
        runtime.cancellation = context.parent_cancellation;
        runtime.concurrent_scopes.pop();
        runtime.scope_lineage.truncate(context.lineage_depth);
        runtime.scope_registry.truncate(context.lineage_depth);
        retire_scope_channels(runtime, context.scope.id());
        if let Some(mut error) = children.unwrap_or_else(Some)
            && error.tag == OutcomeTag::InternalFault
        {
            error.primary = runtime.fault.take().map(Box::new);
            runtime.fault = Some(error);
        }
    });
}

fn retire_scope_channels(runtime: &mut Runtime, scope: u64) {
    runtime
        .owned_endpoints
        .retain(|(_, endpoint)| endpoint.scope_id() != scope);
    runtime
        .owned_tickets
        .retain(|(_, ticket)| ticket.scope_id() != scope);
}

fn cleanup_task_channels() {
    let (owner, endpoints, tickets) = with_runtime(|runtime| {
        (
            runtime.task_owner,
            runtime.owned_endpoints.clone(),
            runtime.owned_tickets.clone(),
        )
    });
    // Retain the managed descriptors until host-side release has completed.
    for (_, endpoint) in endpoints {
        endpoint.close_if_owned(owner);
    }
    for (_, ticket) in tickets {
        ticket.close_if_owned(owner);
    }
    with_runtime(|runtime| {
        runtime.owned_endpoints.clear();
        runtime.owned_tickets.clear();
    });
}

/// Child failure cancels this body but is contained as the owning scope's Err.
/// Parent cancellation, body panic and effect abort continue outward unchanged.
pub(super) fn recover(minimum_depth: usize) -> Option<u64> {
    let context = with_runtime(|runtime| {
        (runtime
            .fault
            .as_ref()
            .is_some_and(|error| error.tag == OutcomeTag::Cancelled)
            && runtime.concurrent_scopes.len() > minimum_depth)
            .then(|| runtime.concurrent_scopes.last().cloned())
            .flatten()
    })?;
    if context.parent_cancellation.requested() {
        return Some(exits::transition(
            exits::region_work(
                context.parent_activation,
                context.delimiters,
                context.budget_depth,
            ),
            After::RecoverScope {
                scope: None,
                minimum_depth,
            },
            Handle::INVALID,
        ));
    }
    if !context.scope.failed() {
        return None;
    }
    Some(exits::transition(
        exits::region_work(context.activation, context.delimiters, context.budget_depth),
        After::RecoverScope {
            scope: Some(context.value),
            minimum_depth,
        },
        Handle::INVALID,
    ))
}
pub(super) fn after_unwind(scope: Option<Handle>, minimum_depth: usize) -> u64 {
    if let Some(scope) = scope {
        let recoverable = with_runtime(|runtime| {
            if runtime
                .fault
                .as_ref()
                .is_some_and(|error| error.tag == OutcomeTag::Cancelled)
                && runtime.concurrent_scopes.last().is_some_and(|context| {
                    context.value == scope && !context.parent_cancellation.requested()
                })
            {
                runtime.fault = None;
                true
            } else {
                false
            }
        });
        if recoverable {
            return finish(scope, None);
        }
    }
    recover(minimum_depth).unwrap_or(0)
}

fn panic_info(runtime: &mut Runtime, error: &RuntimeError) -> Result<Handle> {
    let message = runtime.string(error.message.clone())?;
    let index = if let Some(index) = error.index {
        let index = runtime.int(index as i128)?;
        runtime.variant("Some", vec![index])?
    } else {
        runtime.variant("None", vec![])?
    };
    runtime.allocate(Object::Record(
        [("message".into(), message), ("index".into(), index)].into(),
    ))
}
fn encode_cause(runtime: &mut Runtime, error: &RuntimeError) -> Result<Handle> {
    match error.tag {
        OutcomeTag::LanguagePanic => {
            let info = panic_info(runtime, error)?;
            runtime.variant("Concurrent::UnwindCause::Panicked", vec![info])
        }
        OutcomeTag::EffectAborted => {
            runtime.variant("Concurrent::UnwindCause::EffectAborted", vec![])
        }
        OutcomeTag::Cancelled => runtime.variant("Concurrent::UnwindCause::Cancelled", vec![]),
        _ => Err(error.clone()),
    }
}
fn encode_fault(runtime: &mut Runtime, error: &RuntimeError) -> Result<Handle> {
    match error.tag {
        OutcomeTag::LanguagePanic => {
            let info = panic_info(runtime, error)?;
            runtime.variant("Concurrent::TaskFault::Panicked", vec![info])
        }
        OutcomeTag::Cancelled => runtime.variant("Concurrent::TaskFault::Cancelled", vec![]),
        OutcomeTag::DoubleFault => {
            let primary = encode_cause(
                runtime,
                error
                    .primary
                    .as_deref()
                    .ok_or_else(|| RuntimeError::internal("double fault has no primary cause"))?,
            )?;
            let cleanup = panic_info(
                runtime,
                error
                    .cleanup
                    .as_deref()
                    .ok_or_else(|| RuntimeError::internal("double fault has no cleanup cause"))?,
            )?;
            let info = runtime.allocate(Object::Record(
                [("primary".into(), primary), ("cleanup".into(), cleanup)].into(),
            ))?;
            runtime.variant("Concurrent::TaskFault::DoubleFaultFatal", vec![info])
        }
        _ => Err(error.clone()),
    }
}
fn decode_body(runtime: &Runtime, value: Handle) -> Result<Option<RuntimeError>> {
    let Object::Variant { tag, fields } = runtime.heap.get(value)? else {
        return Err(RuntimeError::internal("scope body must return Result"));
    };
    match (tag.as_str(), fields.as_slice()) {
        ("Ok", [_]) => Ok(None),
        ("Err", [fault]) => decode_fault(runtime, *fault).map(Some),
        _ => Err(RuntimeError::internal("invalid scope result shape")),
    }
}
fn record_field(runtime: &Runtime, value: Handle, name: &str) -> Result<Handle> {
    let Object::Record(fields) = runtime.heap.get(value)? else {
        return Err(RuntimeError::internal("invalid fault record"));
    };
    fields
        .get(name)
        .copied()
        .ok_or_else(|| RuntimeError::internal("missing fault field"))
}
fn decode_panic(runtime: &Runtime, info: Handle) -> Result<RuntimeError> {
    let mut error = RuntimeError::panic(
        runtime
            .as_string(record_field(runtime, info, "message")?)?
            .to_owned(),
    );
    let Object::Variant { tag, fields } =
        runtime.heap.get(record_field(runtime, info, "index")?)?
    else {
        return Err(RuntimeError::internal("invalid panic index"));
    };
    error.index = match (tag.as_str(), fields.as_slice()) {
        ("None", []) => None,
        ("Some", [value]) => Some(
            usize::try_from(runtime.as_integer(*value)?)
                .map_err(|_| RuntimeError::internal("invalid panic index"))?,
        ),
        _ => return Err(RuntimeError::internal("invalid panic index")),
    };
    Ok(error)
}
fn decode_cause(runtime: &Runtime, value: Handle) -> Result<RuntimeError> {
    let Object::Variant { tag, fields } = runtime.heap.get(value)? else {
        return Err(RuntimeError::internal("invalid unwind cause"));
    };
    match (tag.as_str(), fields.as_slice()) {
        ("Concurrent::UnwindCause::Panicked", [info]) => decode_panic(runtime, *info),
        ("Concurrent::UnwindCause::Cancelled", []) => Ok(RuntimeError::cancelled()),
        ("Concurrent::UnwindCause::EffectAborted", []) => Ok(RuntimeError {
            tag: OutcomeTag::EffectAborted,
            message: "effect aborted".into(),
            location: None,
            index: None,
            primary: None,
            cleanup: None,
        }),
        _ => Err(RuntimeError::internal("invalid unwind cause shape")),
    }
}
fn decode_fault(runtime: &Runtime, value: Handle) -> Result<RuntimeError> {
    let Object::Variant { tag, fields } = runtime.heap.get(value)? else {
        return Err(RuntimeError::internal("invalid task fault"));
    };
    match (tag.as_str(), fields.as_slice()) {
        ("Concurrent::TaskFault::Panicked", [info]) => decode_panic(runtime, *info),
        ("Concurrent::TaskFault::Cancelled", []) => Ok(RuntimeError::cancelled()),
        ("Concurrent::TaskFault::DoubleFaultFatal", [info]) => Ok(RuntimeError::double_fault(
            decode_cause(runtime, record_field(runtime, *info, "primary")?)?,
            decode_panic(runtime, record_field(runtime, *info, "cleanup")?)?,
        )),
        _ => Err(RuntimeError::internal("invalid task fault shape")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    extern "C" fn unused_task(_: u64, _: u64) -> u64 {
        handle(Runtime::unit)
    }
    #[test]
    fn refused_submission_closes_transferred_authority_and_completes_reserved_task() {
        ril_rt_init();
        RUNTIME.with_borrow_mut(crate::shared::activate);
        let executor =
            crate::scheduler::Executor::new(std::num::NonZeroUsize::new(1).unwrap()).unwrap();
        executor.shutdown_idle().unwrap();
        let (scope, args, ticket, receiver) = with_runtime(|runtime| {
            runtime.executor = Some(executor);
            let scope = Scope::new(&runtime.cancellation).unwrap();
            let scope_value = runtime.allocate(Object::TaskScope(scope.clone())).unwrap();
            runtime.scope_lineage.push(scope.id());
            runtime.scope_registry.push(scope.clone());
            let pair = runtime.create_channel(1).unwrap();
            let pair = runtime.sequence(pair).unwrap();
            let sender = runtime.channel_endpoint(pair[0]).unwrap();
            let ticket = sender.detach(runtime.channel_context()).unwrap();
            let ticket_value = runtime.allocate_channel_ticket(ticket.clone()).unwrap();
            let action = runtime
                .allocate(Object::Closure {
                    function: unused_task as *const () as usize as u64,
                    environment: ticket_value,
                })
                .unwrap();
            let Object::ChannelReceiver(receiver) = runtime.heap.get(pair[1]).unwrap() else {
                panic!();
            };
            let receiver = receiver.clone();
            (
                scope,
                runtime
                    .allocate(Object::Tuple(vec![scope_value, action]))
                    .unwrap(),
                ticket,
                receiver,
            )
        });
        assert_eq!(fork(args, Handle::INVALID), 0);
        assert_eq!(
            with_runtime(|runtime| runtime.fault.as_ref().unwrap().tag),
            OutcomeTag::InternalFault
        );
        assert!(scope.failed());
        let context = crate::channel::Context {
            owner: Default::default(),
            lineage: &[scope.id()],
        };
        assert!(
            ticket.attach(context).is_err(),
            "transfer must not revive the caller's consumed alias"
        );
        assert!(
            receiver
                .recv(context, &Default::default())
                .unwrap()
                .is_none(),
            "refused task must close its received sender authority"
        );
        assert_eq!(
            scope.finish(false).unwrap().unwrap().tag,
            OutcomeTag::InternalFault
        );
    }
}
