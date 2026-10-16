//! Resumable logical cleanup. Each callback returns to the owner's trampoline;
//! masks and outcomes live in task state, not a recursively invoked Rust runner.
use super::*;
use crate::cps_exit::{After, Frame, Waiting, Work};
#[cfg(test)]
#[path = "ffi_exit_tests.rs"]
mod tests;

fn fatal(error: &RuntimeError) -> bool {
    matches!(
        error.tag,
        OutcomeTag::DoubleFault | OutcomeTag::InternalFault
    )
}
fn record(primary: &mut Option<RuntimeError>, error: RuntimeError) {
    if error.tag == OutcomeTag::InternalFault {
        *primary = Some(error);
    } else if primary.as_ref().is_none_or(|error| !fatal(error)) {
        *primary = Some(match primary.take() {
            _ if error.tag == OutcomeTag::DoubleFault => error,
            Some(previous) => RuntimeError::double_fault(previous, error),
            None => error,
        });
    }
}
fn inherit(primary: &mut Option<RuntimeError>, incoming: Option<RuntimeError>) {
    if let Some(error) = incoming {
        // An effect abort cannot catch a panic/cancellation already being
        // unwound, and two nested aborts are not a cleanup panic.
        if error.tag != OutcomeTag::EffectAborted || primary.is_none() {
            record(primary, error);
        }
    }
}
fn abandon_previous(runtime: &mut Runtime, owner: u64, activation: Handle) -> Result<()> {
    let mut inherited = None;
    let mut replaced = false;
    for frame in &mut runtime.cps_exits {
        if frame.id != owner
            && !frame.abandoned
            && frame.scope.is_some_and(|(scope, _)| scope == activation)
        {
            frame.abandoned = true;
            replaced = true;
            inherit(&mut inherited, frame.primary.take());
        }
    }
    if replaced {
        let frame = active(runtime, owner)?;
        inherit(&mut inherited, frame.primary.take());
        frame.primary = inherited;
    }
    Ok(())
}
fn active(runtime: &mut Runtime, owner: u64) -> Result<&mut Frame> {
    runtime
        .cps_exits
        .last_mut()
        .filter(|frame| frame.id == owner)
        .ok_or_else(|| RuntimeError::internal("cleanup continuation belongs to another exit"))
}
fn retire_delimiter(runtime: &mut Runtime, delimiter: Handle) -> Result<()> {
    let Object::CpsContinuation {
        state: Continuation::Delimiter { resumptions, .. },
        used,
    } = runtime.heap.get_mut(delimiter)?
    else {
        return Err(RuntimeError::internal(
            "cleanup retired an invalid delimiter",
        ));
    };
    *used = true;
    resumptions.clear();
    runtime.cps_delimiters.retain(|&value| value != delimiter);
    runtime
        .cps_resume_returns
        .retain(|(owner, _)| *owner != delimiter);
    Ok(())
}
fn answer_activation(runtime: &Runtime, next: Handle, checkpoint: Handle) -> Result<Handle> {
    match runtime.heap.get(next)? {
        Object::CpsContinuation {
            state:
                Continuation::Native { activation, .. } | Continuation::FinishArm { activation, .. },
            ..
        } => Ok(*activation),
        Object::CpsContinuation {
            state: Continuation::End,
            ..
        } => Ok(checkpoint),
        _ => Err(RuntimeError::internal(
            "invalid resumption answer continuation",
        )),
    }
}
fn publish(result: Result<Handle>) -> u64 {
    match result {
        Ok(value) => value.0,
        Err(mut error) => {
            with_runtime(|runtime| {
                error.location.get_or_insert(runtime.source_location);
                runtime.fault = Some(error);
            });
            0
        }
    }
}
fn begin(work: Vec<Work>, after: After, value: Handle) -> u64 {
    publish(with_runtime(|runtime| {
        let owner = runtime
            .next_cps_exit
            .checked_add(1)
            .ok_or_else(|| RuntimeError::internal("cleanup identity exhausted"))?;
        let previous = runtime.cancellation_mask;
        let masked = previous
            .checked_add(1)
            .ok_or_else(|| RuntimeError::internal("cleanup cancellation mask exhausted"))?;
        runtime.next_cps_exit = owner;
        runtime.cancellation_mask = masked;
        let allowances = runtime.budgets.suspend_for_cleanup();
        let primary = runtime.fault.take();
        runtime.cps_exits.push(Frame {
            id: owner,
            abandoned: false,
            work,
            after,
            value,
            primary,
            allowances,
            cancellation_mask: previous,
            scope: None,
            waiting: None,
        });
        runtime.allocate(Object::CpsStep(Step::Exit { owner }))
    }))
}
pub(super) fn transition(mut work: Vec<Work>, after: After, value: Handle) -> u64 {
    work.reverse();
    begin(work, after, value)
}
pub(super) fn close_return(
    activation: Handle,
    continuation: Handle,
    value: Handle,
    handlers: Option<Handle>,
) -> u64 {
    begin(
        vec![Work::Close(activation)],
        After::Return {
            continuation,
            handlers,
            activation: None,
        },
        value,
    )
}

// Kept separate from the old synchronous ABI during migration. The backend
// switches to this four-argument entry only when every abnormal exit is ready.
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_scope_leave_then(
    activation: u64,
    marker: u64,
    value: u64,
    continuation: u64,
) -> u64 {
    match catch_unwind(AssertUnwindSafe(|| {
        scope_leave_then(activation, marker, value, continuation)
    })) {
        Ok(step) => step,
        Err(_) => publish(Err(RuntimeError::internal(
            "unexpected Rust panic in logical scope exit",
        ))),
    }
}
fn scope_leave_then(activation: u64, marker: u64, value: u64, continuation: u64) -> u64 {
    let depth: Option<u32> = guarded(|runtime| match runtime.heap.get(Handle(marker))? {
        Object::CpsScope {
            activation: owner,
            depth,
        } if owner.0 == activation => Ok(Some(*depth)),
        _ => Err(RuntimeError::internal(
            "logical scope marker belongs to another activation",
        )),
    });
    let Some(marker) = depth else {
        return 0;
    };
    begin(
        vec![Work::Scope {
            activation: Handle(activation),
            marker,
        }],
        After::Return {
            continuation: Handle(continuation),
            handlers: None,
            activation: None,
        },
        Handle(value),
    )
}

enum Action {
    Continue,
    Close(Handle),
    Host,
    Call(Handle),
    Finish,
}
fn plan(runtime: &mut Runtime, owner: u64) -> Result<Action> {
    if let Some((activation, marker)) = active(runtime, owner)?.scope {
        if active(runtime, owner)?.primary.as_ref().is_some_and(fatal) {
            runtime.abandon_cleanup_stack(Some(activation), marker);
            active(runtime, owner)?.scope = None;
            return Ok(Action::Continue);
        }
        let Some(resource) = runtime.pop_cleanup_stack(Some(activation), marker)? else {
            active(runtime, owner)?.scope = None;
            return Ok(Action::Continue);
        };
        let waiting = Waiting {
            resource,
            activation: runtime.cps_activation,
            handlers: runtime.cps_handlers,
            concurrent_depth: runtime.concurrent_scopes.len(),
            delimiters: runtime.cps_delimiters.clone(),
            budget_depth: runtime.budgets.depth(),
        };
        active(runtime, owner)?.waiting = Some(waiting);
        if crate::host_cleanup::prepare(runtime, resource)?.is_some() {
            return Ok(Action::Host);
        }
        let callable = runtime.field(resource, "on_close")?;
        let arguments = runtime.allocate(Object::Tuple(vec![]))?;
        let continuation = runtime.allocate(Object::CpsContinuation {
            state: Continuation::Cleanup { owner },
            used: false,
        })?;
        Ok(Action::Call(runtime.allocate(Object::CpsStep(
            Step::Call {
                callable,
                arguments,
                continuation,
                handlers: runtime.cps_handlers,
                callback_entry: true,
            },
        ))?))
    } else {
        let Some(work) = active(runtime, owner)?.work.pop() else {
            return Ok(Action::Finish);
        };
        match work {
            Work::Scope { activation, marker } => {
                runtime.attach_activation(activation)?;
                runtime.cps_handlers = runtime.activation(activation)?.handlers;
                active(runtime, owner)?.scope = Some((activation, marker));
            }
            Work::Close(activation) if activation != Handle::INVALID => {
                runtime.activation(activation)?;
                abandon_previous(runtime, owner, activation)?;
                return Ok(Action::Close(activation));
            }
            Work::Close(_) => {}
            Work::Closed { activation, parent } => {
                let Object::CpsActivation(state) = runtime.heap.get_mut(activation)? else {
                    return Err(RuntimeError::internal(
                        "logical cleanup lost its activation",
                    ));
                };
                state.closed = true;
                runtime.cps_activation = parent;
            }
            Work::Unwind(target) => {
                let current = runtime.cps_activation;
                if current != target {
                    if current == Handle::INVALID {
                        return Err(RuntimeError::internal(
                            "cleanup crossed an unrelated activation",
                        ));
                    }
                    active(runtime, owner)?
                        .work
                        .extend([Work::Unwind(target), Work::Close(current)]);
                }
            }
            Work::Region { target, scopes } => {
                if let Some(Crossing {
                    delimiter,
                    checkpoint,
                    ..
                }) = find_crossing(runtime, target, &scopes, 0)?
                {
                    if let Object::CpsContinuation {
                        state: Continuation::Delimiter { resumptions, .. },
                        ..
                    } = runtime.heap.get_mut(delimiter)?
                    {
                        resumptions.clear();
                    }
                    active(runtime, owner)?.work.extend([
                        Work::Region { target, scopes },
                        Work::FinishCross {
                            delimiter,
                            checkpoint,
                        },
                        Work::Unwind(checkpoint),
                    ]);
                } else {
                    active(runtime, owner)?.work.push(Work::Unwind(target));
                }
            }
            Work::BeginAbort => {
                if active(runtime, owner)?.primary.is_none() {
                    active(runtime, owner)?.primary = Some(RuntimeError {
                        tag: OutcomeTag::EffectAborted,
                        message: "effect operation aborted its delimited computation".into(),
                        location: Some(runtime.source_location),
                        index: None,
                        primary: None,
                        cleanup: None,
                    });
                }
            }
            Work::EndAbort => {
                if active(runtime, owner)?
                    .primary
                    .as_ref()
                    .is_some_and(|error| error.tag == OutcomeTag::EffectAborted)
                {
                    active(runtime, owner)?.primary = None;
                }
            }
            Work::RequireSuccess => {
                if active(runtime, owner)?.primary.is_some() {
                    active(runtime, owner)?.work.clear();
                }
            }
            Work::Budgets(depth) => {
                for boundary in runtime.budgets.abandon_since(depth)? {
                    if let Ok(Object::CpsBudgetBoundary(state)) = runtime.heap.get_mut(boundary) {
                        state.active = false;
                    }
                }
            }
            Work::FinishCross {
                delimiter,
                checkpoint,
            } => {
                if let Some(index) = runtime
                    .cps_resume_returns
                    .iter()
                    .rposition(|(owner, _)| *owner == delimiter)
                {
                    let (_, next) = runtime.cps_resume_returns.remove(index);
                    let arm = answer_activation(runtime, next, checkpoint)?;
                    let frame = active(runtime, owner)?;
                    frame.work.push(Work::FinishCross {
                        delimiter,
                        checkpoint,
                    });
                    if arm != checkpoint && arm != Handle::INVALID {
                        frame
                            .work
                            .extend([Work::Unwind(checkpoint), Work::Close(arm)]);
                    }
                } else {
                    retire_delimiter(runtime, delimiter)?;
                }
            }
            Work::Cross {
                target,
                scopes,
                base,
                aborted: inherited,
            } => {
                if active(runtime, owner)?.primary.is_some() {
                    return Ok(Action::Continue);
                }
                if let Some(Crossing {
                    delimiter,
                    checkpoint,
                    aborted,
                }) = find_crossing(runtime, target, &scopes, base)?
                {
                    if let Object::CpsContinuation {
                        state: Continuation::Delimiter { resumptions, .. },
                        ..
                    } = runtime.heap.get_mut(delimiter)?
                    {
                        resumptions.clear();
                    }
                    let mut selected = Vec::new();
                    if aborted || inherited {
                        selected.push(Work::BeginAbort);
                    }
                    selected.push(Work::Unwind(checkpoint));
                    selected.push(Work::FinishCross {
                        delimiter,
                        checkpoint,
                    });
                    if aborted || inherited {
                        selected.push(Work::EndAbort);
                    }
                    selected.push(Work::Cross {
                        target,
                        scopes,
                        base,
                        aborted: inherited,
                    });
                    selected.reverse();
                    active(runtime, owner)?.work.extend(selected);
                }
            }
        }
        Ok(Action::Continue)
    }
}
pub(super) fn advance(owner: u64) -> u64 {
    loop {
        let action = with_runtime(|runtime| plan(runtime, owner));
        match action {
            Ok(Action::Continue) => {}
            Ok(Action::Call(step)) => return step.0,
            Ok(Action::Finish) => return finish(owner),
            Ok(Action::Host) => {
                return handle_control(|runtime| {
                    runtime.allocate(Object::CpsStep(Step::HostCleanup { owner }))
                });
            }
            Ok(Action::Close(activation)) => {
                if let Some(step) = concurrent::closing_step(owner, activation) {
                    return step;
                }
                match close_activation(owner, activation, None) {
                    Ok(Some(step)) => return step,
                    Ok(None) => {}
                    Err(error) => return publish(Err(error)),
                }
            }
            Err(error) => return publish(Err(error)),
        }
    }
}

pub(super) fn prepare_host_cleanup(owner: u64) -> Result<crate::host_job::Job<()>> {
    let action = with_runtime(|runtime| {
        let resource = active(runtime, owner)?
            .waiting
            .as_ref()
            .ok_or_else(|| RuntimeError::internal("host cleanup lost its resource"))?
            .resource;
        crate::host_cleanup::prepare(runtime, resource)?
            .ok_or_else(|| RuntimeError::internal("pending cleanup is not a host resource"))
    })?;
    crate::host_job::Job::start(
        move || action.perform(),
        std::sync::Arc::default(),
        |()| Ok(()),
    )
}
pub(super) fn complete_host_cleanup(owner: u64, result: Result<()>) -> u64 {
    let completed = with_runtime(|runtime| {
        let frame = active(runtime, owner)?;
        frame.waiting = None;
        if let Err(error) = result {
            record(&mut frame.primary, error);
        }
        Ok(())
    });
    match completed {
        Ok(()) => advance(owner),
        Err(error) => publish(Err(error)),
    }
}

pub(super) fn complete_scope_close(
    owner: u64,
    context: crate::concurrent::ActiveScope,
    children: Result<Option<RuntimeError>>,
) -> u64 {
    match close_activation(owner, context.activation, Some((context, children))) {
        Ok(Some(step)) => step,
        Ok(None) => advance(owner),
        Err(error) => publish(Err(error)),
    }
}
fn close_activation(
    owner: u64,
    activation: Handle,
    children: Option<(crate::concurrent::ActiveScope, Result<Option<RuntimeError>>)>,
) -> Result<Option<u64>> {
    // The primary outcome stays in its exit frame throughout the pending drain.
    with_runtime(|runtime| {
        runtime.fault = active(runtime, owner)
            .ok()
            .and_then(|frame| frame.primary.take());
    });
    if let Some((context, children)) = children {
        concurrent::complete_close(context, children);
    }
    with_runtime(|runtime| {
        let primary = runtime.fault.take();
        active(runtime, owner)?.primary = primary;
        Ok::<(), RuntimeError>(())
    })?;
    if foreign::needs_close(activation) {
        return Ok(Some(handle_control(|runtime| {
            runtime.allocate(Object::CpsStep(Step::ForeignClose { owner, activation }))
        })));
    }
    finish_activation_close(owner, activation)?;
    Ok(None)
}
pub(super) fn complete_foreign_close(owner: u64, activation: Handle, result: Result<()>) -> u64 {
    let result = with_runtime(|runtime| {
        let frame = active(runtime, owner)?;
        if let Err(error) = result {
            record(&mut frame.primary, error);
        }
        Ok(())
    })
    .and_then(|()| finish_activation_close(owner, activation));
    match result {
        Ok(()) => advance(owner),
        Err(error) => publish(Err(error)),
    }
}
fn finish_activation_close(owner: u64, activation: Handle) -> Result<()> {
    with_runtime(|runtime| {
        runtime.end_buffered_reads(activation);
        let state = runtime.activation(activation)?.clone();
        runtime.cps_activation = activation;
        runtime.cps_handlers = state.handlers;
        let frame = active(runtime, owner)?;
        frame.work.push(Work::Closed {
            activation,
            parent: state.parent,
        });
        if !state.closed {
            frame.scope = Some((activation, 0));
        }
        Ok(())
    })
}

fn finish(owner: u64) -> u64 {
    let frame = with_runtime(|runtime| {
        active(runtime, owner)?;
        let frame = runtime.cps_exits.pop().expect("checked exit frame");
        for root in frame.references() {
            runtime.keep_temporary(root);
        }
        runtime.budgets.restore_after_cleanup(frame.allowances);
        runtime.cancellation_mask = frame.cancellation_mask;
        let mut primary = frame.primary;
        while runtime
            .cps_exits
            .last()
            .is_some_and(|frame| frame.abandoned)
        {
            let abandoned = runtime.cps_exits.pop().expect("abandoned exit");
            for root in abandoned.references() {
                runtime.keep_temporary(root);
            }
            runtime.budgets.restore_after_cleanup(abandoned.allowances);
            runtime.cancellation_mask = abandoned.cancellation_mask;
            if abandoned.primary.is_some() {
                let current = primary.take();
                primary = abandoned.primary;
                inherit(&mut primary, current);
            }
        }
        runtime.fault = primary;
        Ok((frame.after, frame.value))
    });
    let (after, value) = match frame {
        Ok(frame) => frame,
        Err(error) => return publish(Err(error)),
    };
    match after {
        After::DelimiterAnswer {
            delimiter,
            outer,
            handlers,
            checkpoint,
        } => {
            if ril_rt_status() != 0 {
                // A cleanup operation may replace an already-failing exit.
                // Its saved handler arms still own mandatory cleanup even
                // when the original unwind frame has been abandoned.
                return transition(
                    vec![Work::FinishCross {
                        delimiter,
                        checkpoint,
                    }],
                    After::Stop,
                    value,
                );
            }
            let next = with_runtime(|runtime| {
                // Cleanup can add an answer redirect for this handler while
                // another handler's answer is pending. Resolve by owner only
                // after the protected body has completely unwound.
                if let Some(index) = runtime
                    .cps_resume_returns
                    .iter()
                    .rposition(|(owner, _)| *owner == delimiter)
                {
                    let (_, next) = runtime.cps_resume_returns.remove(index);
                    runtime.cps_activation = answer_activation(runtime, next, checkpoint)?;
                    runtime.keep_temporary(next);
                    Ok(next)
                } else {
                    retire_delimiter(runtime, delimiter)?;
                    runtime.cps_handlers = handlers;
                    Ok(outer)
                }
            });
            match next {
                Ok(next) => return_step(next, value.0),
                Err(error) => publish(Err(error)),
            }
        }
        After::Return {
            continuation,
            handlers,
            activation,
        } => {
            if ril_rt_status() != 0 {
                return 0;
            }
            if let Some(handlers) = handlers {
                set_handlers(handlers);
            }
            if let Some(activation) = activation {
                with_runtime(|runtime| runtime.cps_activation = activation);
            }
            return_step(continuation, value.0)
        }
        After::Native {
            function,
            environment,
            handlers,
        } => {
            if ril_rt_status() != 0 {
                return 0;
            }
            set_handlers(handlers);
            let arguments = handle(|runtime| runtime.allocate(Object::Tuple(vec![value])));
            if arguments == 0 {
                0
            } else {
                invoke_address(function, environment.0, arguments)
            }
        }
        After::Stop => 0,
        After::RecoverScope {
            scope,
            minimum_depth,
        } => concurrent::after_unwind(scope, minimum_depth),
        After::Budget {
            boundary,
            state,
            aborted,
        } => {
            if ril_rt_status() != 0 {
                0
            } else {
                budget::after_cleanup(boundary, *state, value, aborted)
            }
        }
        After::Complete => {
            handle(|runtime| runtime.allocate(Object::CpsStep(Step::Complete { value })))
        }
        After::CallbackComplete { owner, waiting } => {
            let result = with_runtime(|runtime| {
                runtime.cps_activation = waiting.activation;
                runtime.cps_handlers = waiting.handlers;
                let inner: Vec<_> = runtime
                    .cps_delimiters
                    .iter()
                    .copied()
                    .filter(|delimiter| !waiting.delimiters.contains(delimiter))
                    .collect();
                for delimiter in inner {
                    if let Ok(Object::CpsContinuation {
                        state: Continuation::Delimiter { resumptions, .. },
                        used,
                    }) = runtime.heap.get_mut(delimiter)
                    {
                        *used = true;
                        resumptions.clear();
                    }
                }
                runtime
                    .cps_delimiters
                    .retain(|delimiter| waiting.delimiters.contains(delimiter));
                // An enclosing handler may have resumed this cleanup call.
                // Its new answer redirect belongs to the caller's delimited
                // computation and remains live until that computation ends.
                runtime
                    .cps_resume_returns
                    .retain(|(delimiter, _)| waiting.delimiters.contains(delimiter));
                let error = runtime.fault.take();
                let frame = active(runtime, owner)?;
                if let Some(error) = error {
                    record(&mut frame.primary, error);
                }
                runtime.allocate(Object::CpsStep(Step::Exit { owner }))
            });
            publish(result)
        }
    }
}

pub(super) fn region_work(target: Handle, scopes: Vec<Handle>, budget_depth: usize) -> Vec<Work> {
    vec![Work::Region { target, scopes }, Work::Budgets(budget_depth)]
}
pub(super) fn callback_return(owner: u64, value: Handle) -> u64 {
    let prepared = with_runtime(|runtime| {
        let waiting = active(runtime, owner)?
            .waiting
            .take()
            .ok_or_else(|| RuntimeError::internal("unsolicited cleanup callback result"))?;
        let work = if runtime.fault.is_some() {
            let mut work = region_work(
                waiting.activation,
                waiting.delimiters.clone(),
                waiting.budget_depth,
            );
            work.reverse();
            work
        } else {
            vec![
                Work::Budgets(waiting.budget_depth),
                Work::Unwind(waiting.activation),
                Work::RequireSuccess,
                Work::Cross {
                    target: waiting.activation,
                    scopes: waiting.delimiters.clone(),
                    base: 0,
                    aborted: false,
                },
            ]
        };
        Ok((work, waiting))
    });
    match prepared {
        Ok((work, waiting)) => begin(work, After::CallbackComplete { owner, waiting }, value),
        Err(error) => publish(Err(error)),
    }
}

pub(super) fn unwind_fault(target: Handle, scopes: Vec<Handle>, budget_depth: usize) -> u64 {
    transition(
        region_work(target, scopes, budget_depth),
        After::Stop,
        Handle::INVALID,
    )
}
pub(super) fn recover(minimum_depth: usize) -> Option<u64> {
    let pending = with_runtime(|runtime| {
        runtime.fault.as_ref()?;
        if runtime.cps_exits.len() <= minimum_depth {
            return None;
        }
        let frame = runtime.cps_exits.last()?;
        Some((frame.id, frame.waiting.clone()))
    })?;
    let (owner, waiting) = pending;
    if let Some(waiting) = waiting {
        // A callback's inner task scope owns its child barrier and recovery;
        // only an escaping callback fault combines with the saved outer cause.
        if let Some(next) = concurrent::recover(waiting.concurrent_depth) {
            return Some(next);
        }
        Some(callback_return(owner, Handle::INVALID))
    } else {
        with_runtime(|runtime| {
            if let Some(error) = runtime.fault.take()
                && let Ok(frame) = active(runtime, owner)
            {
                record(&mut frame.primary, error);
            }
        });
        Some(advance(owner))
    }
}
