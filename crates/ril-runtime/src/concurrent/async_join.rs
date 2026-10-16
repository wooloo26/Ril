//! Completion subscriptions do not block a worker or inspect a task twice.
use super::*;
use std::{
    future::Future,
    pin::Pin,
    task::{Context, Poll},
};

pub(crate) struct JoinFuture {
    task: Arc<Task>,
    cancellation: Arc<Cancellation>,
    cancel_wake: Option<crate::process_io::CancellationWake>,
    waiter: Option<u64>,
    observe: bool,
}
impl Task {
    pub(crate) fn join_async(self: &Arc<Self>, cancellation: Arc<Cancellation>) -> JoinFuture {
        JoinFuture {
            task: self.clone(),
            cancellation,
            cancel_wake: None,
            waiter: None,
            observe: true,
        }
    }
    pub(super) fn completion_async(self: &Arc<Self>) -> JoinFuture {
        let mut future = self.join_async(Arc::default());
        future.observe = false;
        future
    }
}
impl Drop for JoinFuture {
    fn drop(&mut self) {
        if let Some(id) = self.waiter {
            self.task
                .completion
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .waiters
                .remove(&id);
        }
    }
}
impl Future for JoinFuture {
    type Output = Result<Result<Handle>>;
    fn poll(self: Pin<&mut Self>, context: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.get_mut();
        if let Some(wake) = &mut this.cancel_wake {
            wake.refresh(context.waker());
        } else {
            match this.cancellation.subscribe(context.waker()) {
                Ok(wake) => this.cancel_wake = Some(wake),
                Err(error) => return Poll::Ready(Err(RuntimeError::internal(error.to_string()))),
            }
        }
        let mut completion = this
            .task
            .completion
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let result = if let Some(outcome) = completion.outcome.clone() {
            if !this.observe {
                Ok(outcome)
            } else if completion.observed {
                Err(RuntimeError::panic("task result already observed"))
            } else {
                completion.observed = true;
                Ok(outcome)
            }
        } else if this.cancellation.requested() {
            Err(RuntimeError::cancelled())
        } else {
            let id = if let Some(id) = this.waiter {
                id
            } else {
                let Some(id) = completion.next_waiter.checked_add(1) else {
                    return Poll::Ready(Err(RuntimeError::internal(
                        "task completion wake identity exhausted",
                    )));
                };
                completion.next_waiter = id;
                this.waiter = Some(id);
                id
            };
            let old = completion.waiters.get(&id);
            if old.is_none_or(|old| !old.will_wake(context.waker())) {
                completion.waiters.insert(id, context.waker().clone());
            }
            return Poll::Pending;
        };
        if let Some(id) = this.waiter.take() {
            completion.waiters.remove(&id);
        }
        drop(completion);
        this.cancel_wake = None;
        Poll::Ready(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn cancellation_or_dropping_a_wait_does_not_observe_the_task_result() {
        let scope = Scope::new(&Arc::default()).unwrap();
        let task = scope
            .reserve(Handle::INVALID, TaskOwner::default())
            .unwrap();
        let cancellation = Arc::new(Cancellation::default());
        let mut pending = task.join_async(cancellation.clone());
        let mut context = Context::from_waker(std::task::Waker::noop());
        assert!(Pin::new(&mut pending).poll(&mut context).is_pending());
        assert_eq!(task.completion.lock().unwrap().waiters.len(), 1);
        cancellation.request();
        let Poll::Ready(Err(error)) = Pin::new(&mut pending).poll(&mut context) else {
            panic!();
        };
        assert_eq!(error.tag, OutcomeTag::Cancelled);
        assert!(!task.completion.lock().unwrap().observed);
        assert!(task.completion.lock().unwrap().waiters.is_empty());
        let mut pending = task.join_async(Arc::default());
        assert!(Pin::new(&mut pending).poll(&mut context).is_pending());
        drop(pending);
        assert!(task.completion.lock().unwrap().waiters.is_empty());
        task.complete(Ok(Handle::INVALID)).unwrap();
        assert!(task.join(&Cancellation::default()).unwrap().is_ok());
    }

    #[test]
    fn completion_wakes_every_waiter_but_only_one_can_observe() {
        let scope = Scope::new(&Arc::default()).unwrap();
        let task = scope
            .reserve(Handle::INVALID, TaskOwner::default())
            .unwrap();
        let executor =
            crate::scheduler::Executor::new(std::num::NonZeroUsize::new(1).unwrap()).unwrap();
        let cancellation = Arc::new(Cancellation::default());
        let first = executor
            .spawn(task.join_async(cancellation.clone()))
            .unwrap();
        let second = executor
            .spawn(task.join_async(cancellation.clone()))
            .unwrap();
        let producer = task.clone();
        let (send, receive) = std::sync::mpsc::channel();
        let complete = executor
            .spawn(async move {
                producer.complete(Ok(Handle::INVALID)).unwrap();
                send.send(()).unwrap();
            })
            .unwrap();
        let progress = receive.recv_timeout(std::time::Duration::from_secs(2));
        if progress.is_err() {
            cancellation.request();
        }
        progress.unwrap();
        complete.wait().unwrap();
        let outcomes = [first.wait().unwrap(), second.wait().unwrap()];
        assert_eq!(outcomes.iter().filter(|value| value.is_ok()).count(), 1);
        assert!(
            outcomes
                .iter()
                .any(|value| matches!(value, Err(error) if error.tag == OutcomeTag::LanguagePanic))
        );
        assert!(task.completion.lock().unwrap().waiters.is_empty());
        executor.shutdown_idle().unwrap();
    }
}
