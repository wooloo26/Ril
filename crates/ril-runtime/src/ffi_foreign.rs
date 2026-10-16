//! Provider waits suspend the native driver with no managed heap borrow.
//! Callbacks return as native steps on the owning task with affine reply IDs.
use super::*;
use crate::{
    foreign_codec as codec,
    foreign_process::{Failure, Reply, Request},
    foreign_runtime::{Invocation, Transport},
    host_job::Job,
};
use ril_runtime_api::foreign::{
    Argument, BoundCall, ClientMessage, PROTOCOL_VERSION, ProviderMessage,
};
use std::{
    collections::BTreeMap,
    future::Future,
    pin::Pin,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
    task::{Context, Poll},
};

static NEXT_CALL: AtomicU64 = AtomicU64::new(1);
fn host_failure(error: Failure) -> RuntimeError {
    match error {
        Failure::Binding(message) => {
            RuntimeError::panic(format!("external provider failed: {message}"))
        }
        Failure::Cancelled => RuntimeError::cancelled(),
        Failure::Internal(message) => RuntimeError::internal(message),
    }
}
fn protocol(message: &str) -> RuntimeError {
    RuntimeError::panic(format!("external provider protocol violation: {message}"))
}

#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_foreign_install(configuration: u64) -> u64 {
    handle(|runtime| {
        if !runtime.foreign_calls.is_empty() {
            return Err(RuntimeError::internal(
                "binding installation during an active invocation",
            ));
        }
        let bindings: Vec<BoundCall> =
            serde_json::from_str(runtime.as_string(Handle(configuration))?).map_err(|error| {
                RuntimeError::internal(format!("invalid emitted external bindings: {error}"))
            })?;
        let mut instances = std::collections::BTreeSet::new();
        for binding in &bindings {
            let instance = serde_json::to_string(&binding.static_arguments).map_err(|error| {
                RuntimeError::internal(format!("invalid external static arguments: {error}"))
            })?;
            if !instances.insert((&binding.declaration, instance))
                || !binding.provider.program.is_absolute()
                || binding.provider.max_frame_bytes == 0
                || binding.export.is_empty()
            {
                return Err(RuntimeError::internal(
                    "invalid emitted external provider configuration",
                ));
            }
            codec::validate_signature(&binding.signature)?;
            codec::validate_static_arguments(&binding.signature, &binding.static_arguments)?;
            if binding.kind == ril_runtime_api::foreign::EntryKind::Constant
                && (!binding.signature.parameters.is_empty()
                    || !binding.signature.callbacks.is_empty())
            {
                return Err(RuntimeError::internal(
                    "external constant has invocation parameters",
                ));
            }
        }
        runtime.foreign_bindings = Arc::new(bindings.into_iter().map(Arc::new).collect());
        runtime.unit()
    })
}

pub(super) fn dispatch(
    callable: Handle,
    arguments: Handle,
    continuation: Handle,
    handlers: Handle,
) -> Option<u64> {
    let selected = with_runtime(
        |runtime| matches!(runtime.heap.get(callable), Ok(Object::Builtin(name)) if name == "\0ril.foreign.invoke"),
    );
    selected.then(|| enter(arguments, continuation, handlers))
}
fn enter(arguments: Handle, continuation: Handle, handlers: Handle) -> u64 {
    guarded(|runtime| {
        if runtime.budgets.is_active() {
            return Err(RuntimeError::internal(
                "external invocation has no finite budget coverage",
            ));
        }
        let arguments = runtime.sequence(arguments)?;
        let [binding, arguments] = arguments.as_slice() else {
            return Err(RuntimeError::internal("invalid foreign adapter arguments"));
        };
        let index = usize::try_from(runtime.as_integer(*binding)?)
            .map_err(|_| RuntimeError::internal("invalid external binding index"))?;
        let binding = runtime
            .foreign_bindings
            .get(index)
            .cloned()
            .ok_or_else(|| RuntimeError::internal("external binding is not installed"))?;
        let values = runtime.sequence(*arguments)?;
        if values.len() != binding.signature.parameters.len() {
            return Err(RuntimeError::internal(
                "external adapter supplied wrong arity",
            ));
        }
        let call = NEXT_CALL
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |call| {
                call.checked_add(1)
            })
            .map_err(|_| RuntimeError::internal("external call identity exhausted"))?;
        let mut callbacks = BTreeMap::new();
        let mut data = Vec::new();
        let mut outgoing = Vec::new();
        for (index, (&value, &ty)) in values.iter().zip(&binding.signature.parameters).enumerate() {
            if let Some((slot_index, _)) = binding
                .signature
                .callbacks
                .iter()
                .enumerate()
                .find(|(_, slot)| slot.argument as usize == index)
            {
                if !matches!(
                    runtime.heap.get(value)?,
                    Object::Closure { .. }
                        | Object::CpsClosure { .. }
                        | Object::BudgetClosure { .. }
                        | Object::RetainedClosure { .. }
                        | Object::Builtin(_)
                        | Object::CpsOperation(_)
                        | Object::DataConstructor { .. }
                ) {
                    return Err(RuntimeError::internal(
                        "external callback value is not callable",
                    ));
                }
                let token = index as u64 + 1;
                callbacks.insert(token, (value, slot_index));
                outgoing.push(Argument::Callback(token));
            } else {
                outgoing.push(Argument::Value(data.len() as u32));
                data.push((value, ty));
            }
        }
        let graph = codec::encode(runtime, &binding.signature, &data)?;
        for argument in &mut outgoing {
            if let Argument::Value(index) = argument {
                *index = graph.roots[*index as usize];
            }
        }
        let message = ClientMessage::Invoke {
            version: PROTOCOL_VERSION,
            call,
            entry: binding.kind,
            declaration: binding.declaration.clone(),
            export: binding.export.clone(),
            signature: binding.signature.clone(),
            static_arguments: binding.static_arguments.clone(),
            values: graph,
            arguments: outgoing,
        };
        let activation = runtime.new_activation()?;
        let cancellation = runtime
            .host_cancellation()
            .child()
            .map_err(|error| RuntimeError::internal(error.to_string()))?;
        runtime.foreign_calls.insert(
            call,
            Invocation {
                binding: binding.clone(),
                transport: Transport::Ready {
                    ticket: 0,
                    request: Box::new(Request::Start {
                        provider: binding.provider.clone(),
                        cancellation: cancellation.clone(),
                        message,
                    }),
                },
                next_ticket: 1,
                cancellation,
                arguments: *arguments,
                continuation,
                handlers,
                activation,
                callbacks,
                next_request: 1,
                pending_request: None,
            },
        );
        Ok(runtime.allocate(Object::CpsStep(Step::Foreign { call }))?.0)
    })
}

fn ticket(invocation: &mut Invocation) -> Result<u64> {
    let ticket = invocation.next_ticket;
    invocation.next_ticket = ticket
        .checked_add(1)
        .ok_or_else(|| RuntimeError::internal("external wait identity exhausted"))?;
    Ok(ticket)
}
fn queue(
    runtime: &mut Runtime,
    call: u64,
    make: impl FnOnce(crate::foreign_process::Session) -> Request,
) -> Result<Handle> {
    let state = runtime.foreign_calls.get_mut(&call).ok_or_else(|| {
        RuntimeError::internal("foreign invocation ended before its next request")
    })?;
    if !matches!(state.transport, Transport::Callback(_)) {
        return Err(RuntimeError::internal(
            "foreign transport is not available for a request",
        ));
    }
    let ticket = ticket(state)?;
    let Transport::Callback(session) = std::mem::replace(&mut state.transport, Transport::Closed)
    else {
        unreachable!()
    };
    state.transport = Transport::Ready {
        ticket,
        request: Box::new(make(session)),
    };
    runtime.allocate(Object::CpsStep(Step::Foreign { call }))
}

enum PendingState {
    Running(Job<Reply>),
    Discarding { job: Job<()>, error: RuntimeError },
    Complete,
}
pub(super) struct PendingForeign {
    call: u64,
    ticket: u64,
    state: PendingState,
}
pub(super) fn prepare(call: u64) -> Result<PendingForeign> {
    let (ticket, request, cancellation) = with_runtime(|runtime| {
        let state = runtime
            .foreign_calls
            .get_mut(&call)
            .ok_or_else(|| RuntimeError::internal("unknown foreign invocation"))?;
        let Transport::Ready { ticket, .. } = &state.transport else {
            return Err(RuntimeError::internal(
                "foreign wait was replayed or is not ready",
            ));
        };
        let ticket = *ticket;
        let Transport::Ready { request, .. } =
            std::mem::replace(&mut state.transport, Transport::Waiting { ticket })
        else {
            unreachable!()
        };
        Ok((ticket, request, state.cancellation.clone()))
    })?;
    match Job::start(
        move || request.perform().map_err(host_failure),
        cancellation,
        |reply| reply.discard().map_err(host_failure),
    ) {
        Ok(job) => Ok(PendingForeign {
            call,
            ticket,
            state: PendingState::Running(job),
        }),
        Err(error) => {
            with_runtime(|runtime| {
                if let Some(state) = runtime.foreign_calls.get_mut(&call)
                    && matches!(state.transport, Transport::Waiting { ticket: current } if current == ticket)
                {
                    state.transport = Transport::Closed;
                }
            });
            Err(error)
        }
    }
}
fn expected_wait(runtime: &mut Runtime, call: u64, ticket: u64) -> Result<&mut Invocation> {
    let state = runtime
        .foreign_calls
        .get_mut(&call)
        .ok_or_else(|| RuntimeError::internal("foreign reply lost its invocation"))?;
    if !matches!(state.transport, Transport::Waiting { ticket: current } if current == ticket) {
        return Err(RuntimeError::internal(
            "foreign reply has a stale wait identity",
        ));
    }
    Ok(state)
}
pub(super) fn poll(pending: &mut PendingForeign, context: &mut Context<'_>) -> Poll<u64> {
    match &mut pending.state {
        PendingState::Running(job) => {
            let Poll::Ready(result) = Pin::new(job).poll(context) else {
                return Poll::Pending;
            };
            pending.state = PendingState::Complete;
            let mut unpublished = match result {
                Ok(reply) => Some(reply),
                Err(error) => {
                    let closed = with_runtime(|runtime| {
                        expected_wait(runtime, pending.call, pending.ticket)?.transport =
                            Transport::Closed;
                        Ok(())
                    });
                    return Poll::Ready(fail(pending.call, closed.err().unwrap_or(error)));
                }
            };
            // A completed host operation has retired before managed state changes.
            // Its reply must still match the one exact outstanding request.
            let valid = with_runtime(|runtime| {
                expected_wait(runtime, pending.call, pending.ticket).map(|_| ())
            });
            if let Err(error) = valid {
                if let Some(reply) = unpublished.take() {
                    match Job::start(
                        move || reply.discard().map_err(host_failure),
                        Arc::default(),
                        |()| Ok(()),
                    ) {
                        Ok(job) => {
                            pending.state = PendingState::Discarding { job, error };
                            return poll(pending, context);
                        }
                        Err(mut cleanup) => {
                            cleanup.primary = Some(Box::new(error));
                            return Poll::Ready(fail(pending.call, cleanup));
                        }
                    }
                }
                return Poll::Ready(fail(pending.call, error));
            }
            let Some(reply) = unpublished else {
                unreachable!("host errors are handled before consuming the reply")
            };
            match reply {
                Reply::Event { session, event } => {
                    with_runtime(|runtime| {
                        expected_wait(runtime, pending.call, pending.ticket)
                            .expect("checked wait")
                            .transport = Transport::Callback(*session);
                    });
                    Poll::Ready(event_step(pending.call, event))
                }
                Reply::Finished(values) => {
                    let decoded = with_runtime(|runtime| {
                        let state = expected_wait(runtime, pending.call, pending.ticket)?;
                        state.transport = Transport::Closed;
                        let binding = state.binding.clone();
                        codec::decode(
                            runtime,
                            &binding.signature,
                            &values,
                            &[binding.signature.result],
                        )
                        .map(|values| values[0])
                    });
                    Poll::Ready(match decoded {
                        Ok(value) => finish(pending.call, value),
                        Err(error) => fail(pending.call, error),
                    })
                }
            }
        }
        PendingState::Discarding { job, error } => {
            let Poll::Ready(result) = Pin::new(job).poll(context) else {
                return Poll::Pending;
            };
            let original = error.clone();
            pending.state = PendingState::Complete;
            let error = match result {
                Ok(()) => original,
                Err(mut error) => {
                    error.primary = Some(Box::new(original));
                    error
                }
            };
            Poll::Ready(fail(pending.call, error))
        }
        PendingState::Complete => Poll::Ready(fail(
            pending.call,
            RuntimeError::internal("foreign wait polled after completion"),
        )),
    }
}
fn event_step(call: u64, event: ProviderMessage) -> u64 {
    match event {
        ProviderMessage::Callback {
            call: received,
            request,
            token,
            arguments,
        } if received == call => {
            let step = with_runtime(|runtime| {
                let state = runtime.foreign_calls.get(&call).ok_or_else(|| {
                    RuntimeError::internal("foreign invocation ended before callback")
                })?;
                if state.pending_request.is_some() || request != state.next_request {
                    return Err(protocol("callback request was replayed or out of order"));
                }
                let &(callback, slot) = state
                    .callbacks
                    .get(&token)
                    .ok_or_else(|| protocol("callback token is not live in this invocation"))?;
                let binding = state.binding.clone();
                let handlers = state.handlers;
                let values = codec::decode(
                    runtime,
                    &binding.signature,
                    &arguments,
                    &binding.signature.callbacks[slot].parameters,
                )?;
                let state = runtime.foreign_calls.get_mut(&call).expect("live call");
                state.next_request = request
                    .checked_add(1)
                    .ok_or_else(|| protocol("callback request identity exhausted"))?;
                state.pending_request = Some((request, slot));
                let arguments = runtime.allocate(Object::Tuple(values))?;
                let continuation = runtime.allocate(Object::CpsContinuation {
                    state: Continuation::ForeignCallback { call, request },
                    used: false,
                })?;
                runtime.allocate(Object::CpsStep(Step::Call {
                    callable: callback,
                    arguments,
                    continuation,
                    handlers,
                    callback_entry: true,
                }))
            });
            match step {
                Ok(step) => step.0,
                Err(error) => fail(call, error),
            }
        }
        ProviderMessage::Return {
            call: received,
            values,
        } if received == call => {
            let queued = with_runtime(|runtime| {
                let state = runtime.foreign_calls.get(&call).ok_or_else(|| {
                    RuntimeError::internal("foreign invocation ended before return")
                })?;
                if state.pending_request.is_some() {
                    return Err(protocol("return while a callback is pending"));
                }
                queue(runtime, call, |session| Request::Finish { session, values })
            });
            match queued {
                Ok(step) => step.0,
                Err(error) => fail(call, error),
            }
        }
        ProviderMessage::Panic {
            call: received,
            message,
        } if received == call => fail(
            call,
            RuntimeError::panic(format!("external provider panic: {message}")),
        ),
        _ => fail(
            call,
            protocol("unexpected message or wrong invocation identity"),
        ),
    }
}
pub(super) fn callback_return(call: u64, request: u64, value: Handle) -> u64 {
    let queued = with_runtime(|runtime| {
        let state = runtime
            .foreign_calls
            .get(&call)
            .ok_or_else(|| protocol("callback outlived its foreign invocation"))?;
        let Some((expected, slot)) = state.pending_request else {
            return Err(protocol("unsolicited callback return"));
        };
        if expected != request {
            return Err(protocol("wrong callback return identity"));
        }
        let values = codec::encode(
            runtime,
            &state.binding.signature,
            &[(value, state.binding.signature.callbacks[slot].result)],
        )?;
        let message = ClientMessage::CallbackReturn {
            call,
            request,
            values,
        };
        let step = queue(runtime, call, |session| Request::Exchange {
            session,
            message,
        })?;
        runtime
            .foreign_calls
            .get_mut(&call)
            .expect("live callback")
            .pending_request = None;
        Ok(step)
    });
    match queued {
        Ok(step) => step.0,
        Err(error) => fail(call, error),
    }
}
fn finish(call: u64, value: Handle) -> u64 {
    let state = with_runtime(|runtime| {
        let state = runtime.foreign_calls.remove(&call).expect("finished call");
        for root in state.references() {
            runtime.keep_temporary(root);
        }
        runtime.keep_temporary(value);
        state
    });
    exits::close_return(
        state.activation,
        state.continuation,
        value,
        Some(state.handlers),
    )
}
fn fail(_call: u64, error: RuntimeError) -> u64 {
    with_runtime(|runtime| {
        let mut error = error;
        error.location.get_or_insert(runtime.source_location);
        runtime.fault = Some(error);
    });
    0
}

pub(super) struct PendingForeignClose {
    calls: Vec<(u64, u64)>,
    job: Job<()>,
    complete: bool,
}
pub(super) fn needs_close(activation: Handle) -> bool {
    with_runtime(|runtime| {
        runtime
            .foreign_calls
            .values()
            .any(|call| call.activation == activation)
    })
}
pub(super) fn prepare_close(activation: Handle) -> Result<PendingForeignClose> {
    let (calls, requests, sessions) = with_runtime(|runtime| {
        let calls: Vec<_> = runtime
            .foreign_calls
            .iter()
            .filter_map(|(&call, state)| (state.activation == activation).then_some(call))
            .collect();
        // Validate the whole group before moving any native ownership.
        for call in &calls {
            let state = &runtime.foreign_calls[call];
            if matches!(
                state.transport,
                Transport::Waiting { .. } | Transport::Closing { .. }
            ) {
                return Err(RuntimeError::internal(
                    "foreign close overlaps an outstanding host request",
                ));
            }
            if state.next_ticket == u64::MAX {
                return Err(RuntimeError::internal("external wait identity exhausted"));
            }
        }
        let mut identities = Vec::new();
        let mut requests = Vec::new();
        let mut sessions = Vec::new();
        for call in calls {
            let state = runtime.foreign_calls.get_mut(&call).expect("checked call");
            let ticket = ticket(state)?;
            match std::mem::replace(&mut state.transport, Transport::Closing { ticket }) {
                Transport::Ready { request, .. } => requests.push(request),
                Transport::Callback(session) => sessions.push(session),
                Transport::Closed => {}
                Transport::Waiting { .. } | Transport::Closing { .. } => {
                    unreachable!("validated transport group")
                }
            }
            identities.push((call, ticket));
        }
        Ok((identities, requests, sessions))
    })?;
    let job = Job::start(
        move || {
            let mut failure = None;
            for request in requests {
                if let Err(error) = request.discard() {
                    failure = Some(host_failure(error));
                }
            }
            for mut session in sessions {
                if let Err(error) = session.abort() {
                    failure = Some(host_failure(error));
                }
            }
            match failure {
                Some(error) => Err(error),
                None => Ok(()),
            }
        },
        Arc::default(),
        |()| Ok(()),
    );
    match job {
        Ok(job) => Ok(PendingForeignClose {
            calls,
            job,
            complete: false,
        }),
        Err(error) => {
            // Job admission drains the owned operation before returning an error.
            complete_close(&calls)?;
            Err(error)
        }
    }
}
fn complete_close(calls: &[(u64, u64)]) -> Result<()> {
    with_runtime(|runtime| {
        for &(call, ticket) in calls {
            if !runtime.foreign_calls.get(&call).is_some_and(|state| matches!(state.transport, Transport::Closing { ticket: current } if current == ticket)) {
                return Err(RuntimeError::internal("foreign close has a stale wait identity"));
            }
        }
        for &(call, _) in calls {
            let state = runtime.foreign_calls.remove(&call).expect("checked close");
            for root in state.references() {
                runtime.keep_temporary(root);
            }
        }
        Ok(())
    })
}
pub(super) fn poll_close(
    pending: &mut PendingForeignClose,
    context: &mut Context<'_>,
) -> Poll<Result<()>> {
    if pending.complete {
        return Poll::Ready(Err(RuntimeError::internal(
            "foreign close polled after completion",
        )));
    }
    let Poll::Ready(result) = Pin::new(&mut pending.job).poll(context) else {
        return Poll::Pending;
    };
    pending.complete = true;
    let removed = complete_close(&pending.calls);
    Poll::Ready(removed.and(result))
}

#[cfg(test)]
#[path = "ffi_foreign_tests.rs"]
mod tests;
