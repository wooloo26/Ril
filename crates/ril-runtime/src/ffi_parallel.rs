//! Parallel callbacks run as task-owned native computations on the CPU pool.
//! The coordinator parks until every started worker retires, before arbitration.
use super::*;
use crate::parallel::{Group, Job};
use std::{
    future::Future,
    pin::Pin,
    task::{Context, Poll},
};

pub(super) struct PendingParallel {
    operation: Pin<Box<dyn Future<Output = Result<Handle>> + Send>>,
    continuation: Handle,
}
pub(super) fn prepare(
    callable: Handle,
    arguments: Handle,
    continuation: Handle,
) -> Option<PendingParallel> {
    let name = with_runtime(|runtime| match runtime.heap.get(callable) {
        Ok(Object::Builtin(name)) => {
            Some(name.strip_prefix("Prelude::").unwrap_or(name).to_owned())
        }
        _ => None,
    })?;
    let operation = name.strip_prefix("Parallel::")?;
    if !matches!(
        operation,
        "map" | "map_bounded" | "find" | "first" | "any" | "fold" | "join" | "join3" | "for_each"
    ) {
        return None;
    }
    RUNTIME.with_borrow_mut(crate::shared::activate);
    let arguments: Option<Vec<Handle>> = guarded(|runtime| runtime.sequence(arguments).map(Some));
    let arguments = arguments?;
    let operation = operation.to_owned();
    Some(PendingParallel {
        operation: Box::pin(async move { execute_async(&operation, &arguments).await }),
        continuation,
    })
}
pub(super) fn poll(pending: &mut PendingParallel, context: &mut Context<'_>) -> Poll<u64> {
    let Poll::Ready(outcome) = pending.operation.as_mut().poll(context) else {
        return Poll::Pending;
    };
    let value = finish_host(outcome, |_runtime, value| Ok(value));
    Poll::Ready(if value == 0 {
        0
    } else {
        return_step(pending.continuation, value)
    })
}

async fn execute_async(operation: &str, arguments: &[Handle]) -> Result<Handle> {
    if operation == "join" || operation == "join3" {
        let arity = if operation == "join" { 2 } else { 3 };
        if arguments.len() != arity {
            return Err(RuntimeError::internal("invalid parallel join arity"));
        }
        let jobs = arguments
            .iter()
            .map(|&callable| Job::Call {
                callable,
                arguments: vec![],
            })
            .collect();
        let outcomes = run_jobs_async(jobs, arity).await?;
        let values = complete_independent(outcomes)?;
        return with_runtime(|runtime| runtime.allocate(Object::Tuple(values)));
    }
    let (&items, rest) = arguments
        .split_first()
        .ok_or_else(|| RuntimeError::internal("parallel call requires items"))?;
    let items = with_runtime(|runtime| runtime.sequence(items))?;
    if operation == "fold" {
        let &[init, local, merge] = rest else {
            return Err(RuntimeError::internal("invalid parallel fold arity"));
        };
        return fold_async(items, init, local, merge).await;
    }
    let (callback, concurrency) = if operation == "map_bounded" {
        let &[bound, callback] = rest else {
            return Err(RuntimeError::internal("invalid parallel map_bounded arity"));
        };
        let bound = with_runtime(|runtime| runtime.as_integer(bound))?;
        if bound <= 0 {
            return Err(RuntimeError::panic("nonpositive bound"));
        }
        (
            callback,
            usize::try_from(bound)
                .unwrap_or(usize::MAX)
                .min(default_concurrency()),
        )
    } else {
        let &[callback] = rest else {
            return Err(RuntimeError::internal("invalid parallel callback arity"));
        };
        (callback, default_concurrency())
    };
    let jobs = items
        .iter()
        .map(|&item| Job::Call {
            callable: callback,
            arguments: vec![item],
        })
        .collect();
    let outcomes = run_jobs_async(jobs, concurrency).await?;
    if operation == "for_each" {
        complete_independent(outcomes)?;
        return with_runtime(|runtime| runtime.allocate(Object::Unit));
    }
    if operation == "map" || operation == "map_bounded" {
        let values: Result<Vec<_>> = outcomes.into_iter().collect();
        return with_runtime(|runtime| runtime.allocate(Object::Array(values?)));
    }
    for (item, outcome) in items.into_iter().zip(outcomes) {
        let predicate = outcome?;
        if with_runtime(|runtime| runtime.truth(predicate))? {
            return with_runtime(|runtime| {
                if operation == "any" {
                    runtime.allocate(Object::Bool(true))
                } else {
                    runtime.variant("Some", vec![item])
                }
            });
        }
    }
    with_runtime(|runtime| {
        if operation == "any" {
            runtime.allocate(Object::Bool(false))
        } else {
            runtime.variant("None", vec![])
        }
    })
}

fn complete_independent(outcomes: Vec<Result<Handle>>) -> Result<Vec<Handle>> {
    let mut fault = None;
    let mut values = Vec::with_capacity(outcomes.len());
    for outcome in outcomes {
        match outcome {
            Ok(value) => values.push(value),
            Err(error) => fault = crate::concurrent::choose_fault(fault, Some(error)),
        }
    }
    if let Some(fault) = fault {
        Err(fault)
    } else {
        Ok(values)
    }
}

async fn fold_async(
    items: Vec<Handle>,
    init: Handle,
    local: Handle,
    merge: Handle,
) -> Result<Handle> {
    let jobs = if items.is_empty() {
        vec![Job::Fold {
            init,
            local,
            items: vec![],
            start: 0,
        }]
    } else {
        items
            .chunks(64)
            .enumerate()
            .map(|(group, items)| Job::Fold {
                init,
                local,
                items: items.to_vec(),
                start: group * 64,
            })
            .collect()
    };
    let mut values: Vec<_> = run_jobs_async(jobs, default_concurrency())
        .await?
        .into_iter()
        .collect::<Result<_>>()?;
    while values.len() > 1 {
        let jobs = values
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| Job::Merge {
                callable: merge,
                arguments: pair.to_vec(),
            })
            .collect();
        let mut next: Vec<_> = run_jobs_async(jobs, default_concurrency())
            .await?
            .into_iter()
            .collect::<Result<_>>()?;
        if values.len() % 2 != 0 {
            next.push(*values.last().expect("nonempty merge level"));
        }
        values = next;
    }
    Ok(values[0])
}

fn default_concurrency() -> usize {
    std::thread::available_parallelism()
        .map_or(2, usize::from)
        .max(2)
}

async fn run_jobs_async(jobs: Vec<Job>, concurrency: usize) -> Result<Vec<Result<Handle>>> {
    let workers = jobs.len().min(concurrency);
    if workers == 0 {
        return Ok(vec![]);
    }
    let group = Group::new(jobs);
    let root = with_runtime(|runtime| runtime.allocate(Object::ParallelGroup(group.clone())))?;
    let cancellation = RUNTIME.with_borrow(Runtime::host_cancellation);
    let executor = native_executor()?;
    let mut running = Vec::with_capacity(workers);
    let mut infrastructure_fault = None;
    for _ in 0..workers {
        let child = RUNTIME.with_borrow(|runtime| {
            crate::shared::fork_runtime(runtime, &[root], cancellation.clone())
        });
        let mut child = match child {
            Ok(child) => child,
            Err(error) => {
                infrastructure_fault = Some(error);
                break;
            }
        };
        let executing = group.clone();
        let worker = executor.spawn(async move {
            crate::shared::with_runtime(&mut child, |runtime| runtime.root(0, root))
                .expect("registered parallel group root");
            while let Some((index, job)) = executing.claim() {
                let (runtime, outcome) = evaluate_async(job, child).await;
                child = runtime;
                crate::shared::with_runtime(&mut child, |runtime| {
                    executing.complete(index, outcome);
                    runtime.fault = None;
                    runtime.statement_end();
                });
            }
        });
        match worker {
            Ok(worker) => running.push(worker),
            Err(error) => {
                infrastructure_fault = Some(RuntimeError::internal(format!(
                    "cannot submit parallel worker: {error:?}"
                )));
                break;
            }
        }
    }
    for worker in running {
        if worker.await.is_err() {
            infrastructure_fault = Some(RuntimeError::internal(
                "unexpected Rust panic in parallel worker",
            ));
        }
    }
    if let Some(error) = infrastructure_fault {
        return Err(error);
    }
    let outcomes = group.outcomes()?;
    // Language panic/double-fault selection is operation-specific. A host or
    // runtime invariant failure is never a suppressible callback outcome.
    if let Some(error) = outcomes
        .iter()
        .filter_map(|outcome| outcome.as_ref().err())
        .find(|error| error.tag == OutcomeTag::InternalFault)
    {
        return Err(error.clone());
    }
    Ok(outcomes)
}

async fn evaluate_async(job: Job, mut runtime: Runtime) -> (Runtime, Result<Handle>) {
    match job {
        Job::Call {
            callable,
            arguments,
        } => invoke_async(runtime, callable, arguments).await,
        Job::Merge {
            callable,
            arguments,
        } => {
            let (runtime, result) = invoke_async(runtime, callable, arguments).await;
            (
                runtime,
                result.map_err(|mut error| {
                    set_index(&mut error, None);
                    error
                }),
            )
        }
        Job::Fold {
            init,
            local,
            items,
            start,
        } => {
            let (initial_runtime, result) = invoke_async(runtime, init, vec![]).await;
            runtime = initial_runtime;
            let mut accumulator = match result {
                Ok(value) => value,
                Err(mut error) => {
                    set_index(&mut error, None);
                    return (runtime, Err(error));
                }
            };
            for (offset, item) in items.into_iter().enumerate() {
                let (next_runtime, result) =
                    invoke_async(runtime, local, vec![accumulator, item]).await;
                runtime = next_runtime;
                match result {
                    Ok(value) => accumulator = value,
                    Err(mut error) => {
                        set_index(&mut error, Some(start + offset));
                        return (runtime, Err(error));
                    }
                }
            }
            (runtime, Ok(accumulator))
        }
    }
}

fn set_index(error: &mut RuntimeError, index: Option<usize>) {
    error.index = index;
    if let Some(primary) = &mut error.primary {
        set_index(primary, index);
    }
    if let Some(cleanup) = &mut error.cleanup {
        set_index(cleanup, index);
    }
}

async fn invoke_async(
    mut runtime: Runtime,
    callable: Handle,
    arguments: Vec<Handle>,
) -> (Runtime, Result<Handle>) {
    let initial = with_owned_runtime(&mut runtime, || {
        handle(|runtime| {
            let continuation = runtime.allocate(Object::CpsContinuation {
                state: Continuation::End,
                used: false,
            })?;
            let arguments = runtime.allocate(Object::Tuple(arguments))?;
            runtime.allocate(Object::CpsStep(Step::Call {
                callable,
                arguments,
                continuation,
                handlers: Handle::INVALID,
                callback_entry: true,
            }))
        })
    });
    let NativeCompletion { mut runtime, value } = NativeComputation::new(runtime, initial).await;
    let outcome = crate::shared::with_runtime(&mut runtime, |runtime| match runtime.fault.take() {
        Some(error) => Err(error),
        None if value == 0 => Err(RuntimeError::internal(
            "parallel callback returned no managed value",
        )),
        None => {
            // Keep the fold accumulator across the next callback's allocations.
            let value = runtime.root(1, Handle(value))?;
            runtime.statement_end();
            Ok(value)
        }
    });
    (runtime, outcome)
}

#[cfg(test)]
fn await_test<T>(future: impl Future<Output = T>) -> T {
    let mut future = std::pin::pin!(future);
    let wake = std::sync::Arc::new(DriverWake::default());
    let waker = std::task::Waker::from(wake.clone());
    let mut context = Context::from_waker(&waker);
    loop {
        if let Poll::Ready(value) = future.as_mut().poll(&mut context) {
            return value;
        }
        wake.wait();
    }
}
#[cfg(test)]
fn execute(operation: &str, arguments: &[Handle]) -> Result<Handle> {
    await_test(execute_async(operation, arguments))
}
#[cfg(test)]
fn fold(items: Vec<Handle>, init: Handle, local: Handle, merge: Handle) -> Result<Handle> {
    await_test(fold_async(items, init, local, merge))
}
#[cfg(test)]
fn run_jobs(jobs: Vec<Job>, concurrency: usize) -> Result<Vec<Result<Handle>>> {
    await_test(run_jobs_async(jobs, concurrency))
}

#[cfg(test)]
#[path = "ffi_parallel_tests.rs"]
mod tests;
