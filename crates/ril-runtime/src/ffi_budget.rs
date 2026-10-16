//! Budget transitions stay in the existing native-step trampoline. Cleanup and
//! native calls occur after every managed-heap borrow has ended.
use super::*;
use crate::{
    budget::{Decision, Exhaustion},
    cps::{BudgetBoundary, BudgetHandler},
};
use ril_runtime_api::abi::BudgetEvent;
#[cfg(test)]
#[path = "ffi_budget_tests.rs"]
mod tests;

#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_budget(
    limit: u64,
    action: u64,
    continuation: u64,
    operation: u64,
) -> u64 {
    step(|runtime| Step::Budget {
        limit: Handle(limit),
        action: Handle(action),
        continuation: Handle(continuation),
        operation,
        handlers: runtime.cps_handlers,
        activation: runtime.cps_activation,
        delimiters: runtime.cps_delimiters.clone(),
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cps_charge(event: u32, next: u64) -> u64 {
    handle(|runtime| {
        let event = BudgetEvent::from_raw(event)
            .ok_or_else(|| RuntimeError::internal("invalid abstract budget event"))?;
        runtime.heap.get(Handle(next))?;
        runtime.allocate(Object::CpsStep(Step::Charge {
            event,
            next: Handle(next),
        }))
    })
}
fn exhaust_step(runtime: &mut Runtime, exhaustion: Exhaustion) -> Result<Handle> {
    runtime.allocate(Object::CpsStep(Step::BudgetExhaust {
        boundary: exhaustion.boundary,
        abandoned: exhaustion
            .abandoned
            .into_iter()
            .map(|(_, boundary)| boundary)
            .collect(),
    }))
}
fn selected(runtime: &Runtime, operation: u64, handlers: Handle) -> Result<Option<BudgetHandler>> {
    let mut cursor = handlers;
    let mut visited = std::collections::BTreeSet::new();
    while cursor != Handle::INVALID {
        if !visited.insert(cursor) {
            return Err(RuntimeError::internal("cyclic budget handler chain"));
        }
        let Object::CpsHandlerFrame(frame) = runtime.heap.get(cursor)? else {
            return Err(RuntimeError::internal("invalid budget handler frame"));
        };
        let Object::CpsHandlers(table) = runtime.heap.get(frame.table)? else {
            return Err(RuntimeError::internal("invalid budget handler table"));
        };
        if let Some(&arm) = table.get(&operation) {
            return Ok(Some(BudgetHandler {
                frame: cursor,
                arm,
                parent: frame.parent,
                delimiter: frame.delimiter,
            }));
        }
        cursor = frame.parent;
    }
    Ok(None)
}
pub(super) fn enter(
    limit: Handle,
    action: Handle,
    continuation: Handle,
    operation: u64,
    handlers: Handle,
    activation: Handle,
    delimiters: Vec<Handle>,
) -> u64 {
    handle(|runtime| {
        if let Decision::Exhaust(exhaustion) = runtime.budgets.charge(BudgetEvent::BudgetEntry) {
            return exhaust_step(runtime, exhaustion);
        }
        let limit = u64::try_from(runtime.as_integer(limit)?)
            .map_err(|_| RuntimeError::panic("negative budget limit"))?;
        let selection = selected(runtime, operation, handlers)?;
        let boundary = runtime.allocate(Object::CpsBudgetBoundary(BudgetBoundary {
            id: None,
            active: true,
            continuation,
            operation,
            handlers,
            activation,
            delimiters,
            selection,
        }))?;
        let id = runtime.budgets.begin(limit, boundary)?;
        let Object::CpsBudgetBoundary(stored) = runtime.heap.get_mut(boundary)? else {
            return Err(RuntimeError::internal("lost budget boundary"));
        };
        stored.id = Some(id);
        if limit == 0 {
            let exhaustion = runtime.budgets.exhaust_zero(id)?;
            return exhaust_step(runtime, exhaustion);
        }
        let continuation = runtime.allocate(Object::CpsContinuation {
            state: Continuation::BudgetFinish { boundary },
            used: false,
        })?;
        let arguments = runtime.allocate(Object::Tuple(vec![]))?;
        runtime.allocate(Object::CpsStep(Step::Call {
            callable: action,
            arguments,
            continuation,
            handlers,
            callback_entry: true,
        }))
    })
}
pub(super) fn charge(event: BudgetEvent, next: Handle) -> u64 {
    handle(|runtime| match runtime.budgets.charge(event) {
        Decision::Exhaust(exhaustion) => exhaust_step(runtime, exhaustion),
        Decision::Execute => {
            let value = runtime.unit()?;
            runtime.allocate(Object::CpsStep(Step::Return {
                continuation: next,
                value,
            }))
        }
    })
}
pub(super) fn before_callback() -> Option<u64> {
    guarded_control(
        |runtime| match runtime.budgets.charge(BudgetEvent::FunctionEntry) {
            Decision::Execute => Ok(None),
            Decision::Exhaust(exhaustion) => {
                exhaust_step(runtime, exhaustion).map(|step| Some(step.0))
            }
        },
    )
}
fn boundary(runtime: &Runtime, handle: Handle) -> Result<BudgetBoundary> {
    let Object::CpsBudgetBoundary(state) = runtime.heap.get(handle)? else {
        return Err(RuntimeError::internal("invalid budget boundary"));
    };
    if !state.active || state.id.is_none() {
        return Err(RuntimeError::internal(
            "budget boundary is no longer active",
        ));
    }
    Ok(state.clone())
}
fn close_action(boundary: Handle, state: BudgetBoundary, value: Handle, aborted: bool) -> u64 {
    let mut work = vec![
        Work::Cross {
            target: state.activation,
            scopes: state.delimiters.clone(),
            base: state.delimiters.len(),
            aborted,
        },
        Work::RequireSuccess,
    ];
    if aborted {
        work.push(Work::BeginAbort);
    }
    work.push(Work::Unwind(state.activation));
    if aborted {
        work.push(Work::EndAbort);
    }
    exits::transition(
        work,
        After::Budget {
            boundary,
            state: Box::new(state),
            aborted,
        },
        value,
    )
}
pub(super) fn finish(handle_value: Handle, value: Handle) -> u64 {
    let state: Option<BudgetBoundary> =
        guarded(|runtime| boundary(runtime, handle_value).map(Some));
    let Some(state) = state else {
        return 0;
    };
    close_action(handle_value, state, value, false)
}
pub(super) fn after_cleanup(
    handle_value: Handle,
    state: BudgetBoundary,
    value: Handle,
    aborted: bool,
) -> u64 {
    if aborted {
        return dispatch_exhaustion(state);
    }
    guarded(|runtime| {
        runtime.budgets.finish(
            state
                .id
                .ok_or_else(|| RuntimeError::internal("missing budget owner"))?,
        )?;
        let Object::CpsBudgetBoundary(stored) = runtime.heap.get_mut(handle_value)? else {
            return Err(RuntimeError::internal("lost completed budget boundary"));
        };
        stored.active = false;
        runtime.cps_handlers = state.handlers;
        runtime.cps_delimiters = state.delimiters;
        Ok(())
    });
    if ril_rt_status() != 0 {
        return 0;
    }
    return_step(state.continuation, value.0)
}
pub(super) fn abandon(handle_value: Handle, abandoned: Vec<Handle>) -> u64 {
    let state: Option<BudgetBoundary> = guarded(|runtime| {
        let state = boundary(runtime, handle_value)?;
        for handle in abandoned {
            let Object::CpsBudgetBoundary(stored) = runtime.heap.get_mut(handle)? else {
                return Err(RuntimeError::internal("lost abandoned budget boundary"));
            };
            stored.active = false;
        }
        Ok(Some(state))
    });
    let Some(state) = state else {
        return 0;
    };
    let value = handle(Runtime::unit);
    if value == 0 {
        return 0;
    }
    close_action(handle_value, state, Handle(value), true)
}
fn dispatch_exhaustion(state: BudgetBoundary) -> u64 {
    handle(|runtime| {
        runtime.cps_handlers = state.handlers;
        runtime.cps_delimiters = state.delimiters;
        let Some(selection) = state.selection else {
            return Err(RuntimeError::panic("unhandled Div exhaustion"));
        };
        let resumption = runtime.allocate(Object::CpsResumption(Resumption {
            non_resumable: true,
            continuation: state.continuation,
            handlers: state.handlers,
            used: false,
            delimiter: selection.delimiter,
            activation: state.activation,
        }))?;
        let Object::CpsContinuation {
            state: Continuation::Delimiter { resumptions, .. },
            used: false,
        } = runtime.heap.get_mut(selection.delimiter)?
        else {
            return Err(RuntimeError::internal(
                "selected budget exhaustion handler has expired",
            ));
        };
        resumptions.push(resumption);
        let arguments = runtime.allocate(Object::Tuple(vec![resumption]))?;
        runtime.allocate(Object::CpsStep(Step::Call {
            callable: selection.arm,
            arguments,
            continuation: selection.delimiter,
            handlers: selection.parent,
            callback_entry: false,
        }))
    })
}
