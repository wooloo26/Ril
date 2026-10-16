//! Owned host requests execute away from CPU workers. Completion means the
//! operation and its host worker have finished, including mandatory reaping.
//! Only host data may be captured by `start`; callers retain managed roots.
use crate::{
    process_io::Cancellation,
    value::{Result, RuntimeError},
};
use std::{
    future::Future,
    panic::{AssertUnwindSafe, catch_unwind},
    pin::Pin,
    sync::{Arc, Mutex},
    task::{Context, Poll, Waker},
    thread::JoinHandle,
    time::Duration,
};

struct Completion<T> {
    result: Option<Result<T>>,
    waker: Option<Waker>,
}
pub(crate) struct Job<T> {
    completion: Arc<Mutex<Completion<T>>>,
    worker: Option<JoinHandle<()>>,
    cancellation: Arc<Cancellation>,
    discard: fn(T) -> Result<()>,
    retirement: Option<crate::timer::Sleep>,
    failure: Option<RuntimeError>,
    discarding: Option<Box<Job<()>>>,
}
impl<T: Send + 'static> Job<T> {
    pub(crate) fn start(
        operation: impl FnOnce() -> Result<T> + Send + 'static,
        cancellation: Arc<Cancellation>,
        discard: fn(T) -> Result<()>,
    ) -> Result<Self> {
        let completion = Arc::new(Mutex::new(Completion {
            result: None,
            waker: None,
        }));
        let publishing = completion.clone();
        // Retain ownership if the OS refuses to start a thread. An unstarted
        // mandatory discard may itself own a live child process.
        let operation = Arc::new(Mutex::new(Some(operation)));
        let executing = operation.clone();
        let worker = std::thread::Builder::new()
            .name("ril-host-request".into())
            .spawn(move || {
                let operation = executing
                    .lock()
                    .unwrap_or_else(|error| error.into_inner())
                    .take()
                    .expect("unstarted host operation");
                let result = catch_unwind(AssertUnwindSafe(operation)).unwrap_or_else(|_| {
                    Err(RuntimeError::internal(
                        "unexpected Rust panic in host request",
                    ))
                });
                let wake = {
                    let mut state = publishing.lock().unwrap_or_else(|error| error.into_inner());
                    state.result = Some(result);
                    state.waker.take()
                };
                if let Some(wake) = wake {
                    wake.wake();
                }
            });
        let worker = match worker {
            Ok(worker) => worker,
            Err(error) => {
                cancellation.request();
                let admission =
                    RuntimeError::internal(format!("cannot start host request: {error}"));
                let operation = operation
                    .lock()
                    .unwrap_or_else(|error| error.into_inner())
                    .take()
                    .expect("unstarted host operation");
                // Emergency containment runs with no managed borrow. Ordinary
                // requests see cancellation; mandatory discard completes here.
                let outcome = catch_unwind(AssertUnwindSafe(operation)).unwrap_or_else(|_| {
                    Err(RuntimeError::internal(
                        "unexpected Rust panic while draining unstarted host request",
                    ))
                });
                let cleanup = match outcome {
                    Ok(reply) => discard(reply),
                    Err(error) => Err(error),
                };
                if let Err(mut error) = cleanup
                    && error.tag == ril_runtime_api::abi::OutcomeTag::InternalFault
                {
                    error.primary = Some(Box::new(admission));
                    return Err(error);
                }
                return Err(admission);
            }
        };
        Ok(Self {
            completion,
            worker: Some(worker),
            cancellation,
            discard,
            retirement: None,
            failure: None,
            discarding: None,
        })
    }
}
impl<T: Send + 'static> Future for Job<T> {
    type Output = Result<T>;
    fn poll(self: Pin<&mut Self>, context: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.get_mut();
        if let Some(discarding) = &mut this.discarding {
            let Poll::Ready(result) = Pin::new(discarding.as_mut()).poll(context) else {
                return Poll::Pending;
            };
            this.discarding = None;
            let mut failure = this
                .failure
                .take()
                .expect("failed host reply awaiting discard");
            if let Err(error) = result {
                failure.primary = Some(Box::new(error));
            }
            return Poll::Ready(Err(failure));
        }
        let Some(worker) = &this.worker else {
            return Poll::Ready(Err(RuntimeError::internal(
                "host request polled after completion",
            )));
        };
        {
            let mut state = this
                .completion
                .lock()
                .unwrap_or_else(|error| error.into_inner());
            if state.result.is_none() {
                if state
                    .waker
                    .as_ref()
                    .is_none_or(|old| !old.will_wake(context.waker()))
                {
                    state.waker = Some(context.waker().clone());
                }
                return Poll::Pending;
            }
            state.waker = None;
        }
        if !worker.is_finished() {
            if this.retirement.is_none() {
                match crate::timer::Sleep::new(Duration::from_millis(1), Arc::default()) {
                    Ok(timer) => this.retirement = Some(timer),
                    Err(error) => {
                        this.failure = Some(error);
                        context.waker().wake_by_ref();
                        return Poll::Pending;
                    }
                }
            }
            match Pin::new(this.retirement.as_mut().expect("retirement timer")).poll(context) {
                Poll::Pending => return Poll::Pending,
                Poll::Ready(result) => {
                    this.retirement = None;
                    if let Err(error) = result {
                        this.failure = Some(error);
                    }
                    context.waker().wake_by_ref();
                    return Poll::Pending;
                }
            }
        }
        this.retirement = None;
        if this
            .worker
            .take()
            .expect("live host worker")
            .join()
            .is_err()
        {
            this.failure = Some(RuntimeError::internal(
                "unexpected Rust panic while completing host request",
            ));
        }
        let result = this
            .completion
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .result
            .take()
            .unwrap_or_else(|| {
                Err(RuntimeError::internal(
                    "host worker completed without a reply",
                ))
            });
        if let Some(mut failure) = this.failure.take() {
            match result {
                Ok(reply) => {
                    let discard = this.discard;
                    match Job::start(move || discard(reply), Arc::default(), |()| Ok(())) {
                        Ok(job) => {
                            this.failure = Some(failure);
                            this.discarding = Some(Box::new(job));
                            context.waker().wake_by_ref();
                            return Poll::Pending;
                        }
                        Err(error) => {
                            failure.primary = Some(Box::new(error));
                        }
                    }
                }
                Err(error) => failure.primary = Some(Box::new(error)),
            }
            return Poll::Ready(Err(failure));
        }
        Poll::Ready(result)
    }
}
impl<T> Drop for Job<T> {
    fn drop(&mut self) {
        if let Some(worker) = self.worker.take() {
            // Normal execution always awaits the operation. This is the final
            // containment path if an unexpected host failure drops its driver:
            // request cancellation, finish/reap, then discard unpublished data.
            self.cancellation.request();
            let _ = worker.join();
            let result = self
                .completion
                .lock()
                .unwrap_or_else(|error| error.into_inner())
                .result
                .take();
            if let Some(Ok(reply)) = result {
                let _ = (self.discard)(reply);
            }
        }
    }
}

#[cfg(test)]
mod tests;
