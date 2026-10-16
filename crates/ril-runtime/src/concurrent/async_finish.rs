//! Scope draining never observes a task's language Result. Children remain
//! rooted by their scope until completion and worker retirement have finished.
use super::*;
use std::{
    future::Future,
    pin::Pin,
    task::{Context, Poll},
};

pub(crate) struct FinishFuture {
    scope: Arc<Scope>,
    tasks: Vec<Arc<Task>>,
    index: usize,
    completion: Option<JoinFuture>,
    waiting_worker: bool,
    #[cfg(test)]
    retirement_timer: Option<crate::timer::Sleep>,
    failure: Option<RuntimeError>,
    done: bool,
}
impl Scope {
    pub(crate) fn finish_async(self: &Arc<Self>, cancel: bool) -> FinishFuture {
        if cancel {
            self.cancel_children();
        }
        let tasks = {
            let mut state = self.state.lock().unwrap_or_else(|error| error.into_inner());
            state.finishing = true;
            state.tasks.clone()
        };
        FinishFuture {
            scope: self.clone(),
            tasks,
            index: 0,
            completion: None,
            waiting_worker: false,
            #[cfg(test)]
            retirement_timer: None,
            failure: None,
            done: false,
        }
    }
}
impl Future for FinishFuture {
    type Output = Result<Option<RuntimeError>>;
    fn poll(self: Pin<&mut Self>, context: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.get_mut();
        if this.done {
            return Poll::Ready(Err(RuntimeError::internal(
                "scope drain polled after completion",
            )));
        }
        let mut retired = 0;
        while let Some(task) = this.tasks.get(this.index) {
            if retired == 64 {
                context.waker().wake_by_ref();
                return Poll::Pending;
            }
            if !this.waiting_worker {
                let completion = this
                    .completion
                    .get_or_insert_with(|| task.completion_async());
                let Poll::Ready(outcome) = Pin::new(completion).poll(context) else {
                    return Poll::Pending;
                };
                this.completion = None;
                if let Err(error) = outcome.and_then(|result| result) {
                    this.failure = choose_fault(this.failure.take(), Some(error));
                }
                this.waiting_worker = true;
            }
            #[cfg(test)]
            if let Some(timer) = &mut this.retirement_timer {
                let Poll::Ready(result) = Pin::new(timer).poll(context) else {
                    return Poll::Pending;
                };
                this.retirement_timer = None;
                if let Err(error) = result {
                    this.failure = choose_fault(this.failure.take(), Some(error));
                }
            }
            let mut worker = task
                .worker
                .lock()
                .unwrap_or_else(|error| error.into_inner());
            #[cfg(test)]
            if matches!(worker.as_ref(), Some(TaskWorker::Thread(worker)) if !worker.is_finished())
            {
                drop(worker);
                // Transitional OS task workers publish before retiring roots.
                // A timer parks this waiter until is_finished permits a quick
                // join; never wait on a live worker on a CPU executor thread.
                match crate::timer::Sleep::new(Duration::from_millis(1), Arc::default()) {
                    Ok(timer) => this.retirement_timer = Some(timer),
                    Err(error) => {
                        // Resource exhaustion must not skip mandatory retirement.
                        this.failure = choose_fault(this.failure.take(), Some(error));
                        context.waker().wake_by_ref();
                        return Poll::Pending;
                    }
                }
                continue;
            }
            let outcome = match worker.as_mut() {
                Some(TaskWorker::Scheduled(worker)) => match Pin::new(worker).poll(context) {
                    Poll::Pending => return Poll::Pending,
                    Poll::Ready(Ok(result)) => result,
                    Poll::Ready(Err(_)) => Err(RuntimeError::internal(
                        "unexpected Rust panic in task worker",
                    )),
                },
                #[cfg(test)]
                Some(TaskWorker::Thread(_)) => worker.take().expect("finished test worker").wait(),
                None => Ok(()),
            };
            worker.take();
            drop(worker);
            if let Err(error) = outcome {
                this.failure = choose_fault(this.failure.take(), Some(error));
            }
            this.waiting_worker = false;
            this.index += 1;
            retired += 1;
        }
        this.scope.close_channels();
        this.done = true;
        Poll::Ready(Ok(this.failure.take()))
    }
}

#[cfg(test)]
mod tests;
