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
    if name != "\0ril.control.parallel_run" {
        return None;
    }
    RUNTIME.with_borrow_mut(crate::shared::activate);
    let arguments: Option<Vec<Handle>> = guarded(|runtime| runtime.sequence(arguments).map(Some));
    let arguments = arguments?;
    Some(PendingParallel {
        operation: Box::pin(async move { execute_batch(&arguments).await }),
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

async fn execute_batch(arguments: &[Handle]) -> Result<Handle> {
    let (jobs, concurrency) = with_runtime(|runtime| {
        let [actions, bound] = arguments else {
            return Err(RuntimeError::internal(
                "independent branches require actions and a bound",
            ));
        };
        let bound = runtime.as_integer(*bound)?;
        if bound <= 0 {
            return Err(RuntimeError::panic("nonpositive concurrency bound"));
        }
        let jobs = runtime
            .sequence(*actions)?
            .into_iter()
            .map(|callable| Job {
                callable,
                arguments: vec![],
            })
            .collect();
        let concurrency = usize::try_from(bound)
            .unwrap_or(usize::MAX)
            .min(default_concurrency());
        Ok((jobs, concurrency))
    })?;
    let outcomes = run_jobs_async(jobs, concurrency).await?;
    with_runtime(|runtime| {
        let mut values = Vec::with_capacity(outcomes.len());
        for outcome in outcomes {
            values.push(runtime.branch_outcome(outcome)?);
        }
        runtime.allocate(Object::Array(values))
    })
}
fn default_concurrency() -> usize {
    std::thread::available_parallelism()
        .map_or(2, usize::from)
        .max(2)
}

async fn run_jobs_async(jobs: Vec<Job>, concurrency: usize) -> Result<Vec<Result<Handle>>> {
    if concurrency == 0 {
        return Err(RuntimeError::panic("nonpositive concurrency bound"));
    }
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
        .find_map(RuntimeError::internal_fault)
    {
        return Err(error.clone());
    }
    Ok(outcomes)
}

async fn evaluate_async(job: Job, runtime: Runtime) -> (Runtime, Result<Handle>) {
    invoke_async(runtime, job.callable, job.arguments).await
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
            // Root the result until its completion is published to the group.
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
fn run_jobs(jobs: Vec<Job>, concurrency: usize) -> Result<Vec<Result<Handle>>> {
    await_test(run_jobs_async(jobs, concurrency))
}

#[cfg(test)]
#[path = "ffi_parallel_tests.rs"]
mod tests;
