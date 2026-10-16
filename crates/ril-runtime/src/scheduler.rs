//! Safe cooperative execution infrastructure for native task integration.
//! Polls must not block. Managed roots and language cancellation belong to the
//! task being polled; this scheduler grants no Ril authority or GC protection.
use std::{
    collections::{BTreeMap, VecDeque},
    future::Future,
    io,
    num::NonZeroUsize,
    panic::{AssertUnwindSafe, catch_unwind},
    pin::Pin,
    sync::{Arc, Condvar, Mutex, Weak},
    task::{Context, Poll, Wake, Waker},
    thread::{self, JoinHandle},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JoinError {
    /// An unexpected host panic, including dropping a completed future.
    Panicked,
    AlreadyJoined,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubmitError {
    Closed,
    IdentityExhausted,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Busy;

trait Runnable: Send + Sync {
    fn run(self: Arc<Self>);
}

struct Queue {
    accepting: bool,
    next_id: u64,
    ready: VecDeque<Arc<dyn Runnable>>,
    // Parked work must live even if an external completion has only a Weak
    // wake reference. This is also the owner of its task-specific root state.
    active: BTreeMap<u64, Arc<dyn Runnable>>,
}
struct Shared {
    queue: Mutex<Queue>,
    wake: Condvar,
}
struct Owner {
    shared: Arc<Shared>,
    workers: Mutex<Vec<JoinHandle<()>>>,
}
impl Drop for Owner {
    fn drop(&mut self) {
        // Existing tasks drain. Never drop a parked language task as a substitute
        // for cancellation/cleanup, and never join our own worker during Drop.
        self.shared
            .queue
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .accepting = false;
        self.shared.wake.notify_all();
    }
}

#[derive(Clone)]
pub struct Executor(Arc<Owner>);
impl std::fmt::Debug for Executor {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_struct("Executor").finish_non_exhaustive()
    }
}
pub(crate) fn native_executor() -> Result<Executor, String> {
    static EXECUTOR: std::sync::OnceLock<Result<Executor, String>> = std::sync::OnceLock::new();
    EXECUTOR
        .get_or_init(|| {
            let count = thread::available_parallelism()
                .map_or(2, usize::from)
                .max(2);
            Executor::new(NonZeroUsize::new(count).expect("positive worker count"))
                .map_err(|error| error.to_string())
        })
        .clone()
}
impl Executor {
    pub fn new(workers: NonZeroUsize) -> io::Result<Self> {
        let shared = Arc::new(Shared {
            queue: Mutex::new(Queue {
                accepting: true,
                next_id: 1,
                ready: VecDeque::new(),
                active: BTreeMap::new(),
            }),
            wake: Condvar::new(),
        });
        let mut handles = Vec::new();
        for index in 0..workers.get() {
            let queue = shared.clone();
            match thread::Builder::new()
                .name(format!("ril-executor-{index}"))
                .spawn(move || worker(queue))
            {
                Ok(handle) => handles.push(handle),
                Err(error) => {
                    shared
                        .queue
                        .lock()
                        .unwrap_or_else(|e| e.into_inner())
                        .accepting = false;
                    shared.wake.notify_all();
                    for handle in handles {
                        let _ = handle.join();
                    }
                    return Err(error);
                }
            }
        }
        Ok(Self(Arc::new(Owner {
            shared,
            workers: Mutex::new(handles),
        })))
    }

    pub fn spawn<T: Send + 'static>(
        &self,
        future: impl Future<Output = T> + Send + 'static,
    ) -> Result<Join<T>, SubmitError> {
        let completion = Arc::new(Completion {
            state: Mutex::new(CompletionState {
                done: false,
                result: None,
                waiter: None,
            }),
            wake: Condvar::new(),
        });
        let mut queue = self
            .0
            .shared
            .queue
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        if !queue.accepting {
            return Err(SubmitError::Closed);
        }
        let id = queue.next_id;
        queue.next_id = id.checked_add(1).ok_or(SubmitError::IdentityExhausted)?;
        let task = Arc::new(Task {
            id,
            shared: Arc::downgrade(&self.0.shared),
            state: Mutex::new(TaskState {
                future: Some(Box::pin(future)),
                queued: true,
                polling: false,
                notified: false,
                done: false,
            }),
            completion: completion.clone(),
        });
        queue.active.insert(id, task.clone());
        queue.ready.push_back(task);
        drop(queue);
        self.0.shared.wake.notify_one();
        Ok(Join { completion })
    }

    /// Close only after task-specific cancellation and cleanup have completed.
    /// A busy executor is left unchanged; no pending task is silently discarded.
    pub fn shutdown_idle(&self) -> Result<(), Busy> {
        let mut queue = self
            .0
            .shared
            .queue
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        if !queue.active.is_empty() {
            return Err(Busy);
        }
        queue.accepting = false;
        drop(queue);
        self.0.shared.wake.notify_all();
        let workers =
            std::mem::take(&mut *self.0.workers.lock().unwrap_or_else(|e| e.into_inner()));
        for worker in workers {
            // No task is polling when active is empty, so this is never the
            // worker currently calling this method from one of its tasks.
            let _ = worker.join();
        }
        Ok(())
    }
}

fn worker(shared: Arc<Shared>) {
    loop {
        let task = {
            let mut queue = shared.queue.lock().unwrap_or_else(|e| e.into_inner());
            loop {
                if let Some(task) = queue.ready.pop_front() {
                    break task;
                }
                if !queue.accepting && queue.active.is_empty() {
                    return;
                }
                queue = shared.wake.wait(queue).unwrap_or_else(|e| e.into_inner());
            }
        };
        // Task polling classifies host panics. This outer boundary also keeps a
        // completed, abandoned output's destructor from killing a pool worker.
        let _ = catch_unwind(AssertUnwindSafe(|| task.run()));
    }
}

type TaskFuture<T> = Pin<Box<dyn Future<Output = T> + Send>>;
struct TaskState<T> {
    future: Option<TaskFuture<T>>,
    queued: bool,
    polling: bool,
    notified: bool,
    done: bool,
}
struct Task<T> {
    id: u64,
    shared: Weak<Shared>,
    state: Mutex<TaskState<T>>,
    completion: Arc<Completion<T>>,
}
impl<T: Send + 'static> Task<T> {
    fn enqueue(self: &Arc<Self>) {
        if let Some(shared) = self.shared.upgrade() {
            shared
                .queue
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .ready
                .push_back(self.clone());
            shared.wake.notify_one();
        }
    }
    fn finish(&self, result: Result<T, JoinError>) {
        {
            let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
            state.done = true;
            state.polling = false;
        }
        // Retire active work before publishing completion, so a successful join
        // also permits idle shutdown. The task itself remains alive through run.
        if let Some(shared) = self.shared.upgrade() {
            shared
                .queue
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .active
                .remove(&self.id);
            shared.wake.notify_all();
        }
        let waiter = {
            let mut state = self
                .completion
                .state
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            state.result = Some(result);
            state.done = true;
            state.waiter.take()
        };
        self.completion.wake.notify_all();
        if let Some(waiter) = waiter {
            waiter.wake();
        }
    }
}
impl<T: Send + 'static> Wake for Task<T> {
    fn wake(self: Arc<Self>) {
        self.wake_by_ref();
    }
    fn wake_by_ref(self: &Arc<Self>) {
        let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        if state.done || state.queued {
            return;
        }
        if state.polling {
            state.notified = true;
            return;
        }
        state.queued = true;
        drop(state);
        self.enqueue();
    }
}
impl<T: Send + 'static> Runnable for Task<T> {
    fn run(self: Arc<Self>) {
        let future = {
            let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
            if state.done {
                return;
            }
            state.queued = false;
            state.polling = true;
            state.notified = false;
            state.future.take()
        };
        let Some(mut future) = future else {
            self.finish(Err(JoinError::Panicked));
            return;
        };
        let waker = Waker::from(self.clone());
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            future.as_mut().poll(&mut Context::from_waker(&waker))
        }));
        match outcome {
            Ok(Poll::Pending) => {
                let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
                state.future = Some(future);
                state.polling = false;
                let notified = state.notified;
                state.queued = notified;
                drop(state);
                if notified {
                    self.enqueue();
                }
            }
            Ok(Poll::Ready(value)) => {
                if catch_unwind(AssertUnwindSafe(|| drop(future))).is_err() {
                    let _ = catch_unwind(AssertUnwindSafe(|| drop(value)));
                    self.finish(Err(JoinError::Panicked));
                } else {
                    self.finish(Ok(value));
                }
            }
            Err(_) => {
                let _ = catch_unwind(AssertUnwindSafe(|| drop(future)));
                self.finish(Err(JoinError::Panicked));
            }
        }
    }
}

struct CompletionState<T> {
    done: bool,
    result: Option<Result<T, JoinError>>,
    waiter: Option<Waker>,
}
struct Completion<T> {
    state: Mutex<CompletionState<T>>,
    wake: Condvar,
}
pub struct Join<T> {
    completion: Arc<Completion<T>>,
}
impl<T> std::fmt::Debug for Join<T> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_struct("Join").finish_non_exhaustive()
    }
}
impl<T> Join<T> {
    /// For an outer synchronous driver only. Cooperative tasks must await the
    /// Join future instead of blocking the executor's CPU workers here.
    pub fn wait(self) -> Result<T, JoinError> {
        let mut state = self
            .completion
            .state
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        while !state.done {
            state = self
                .completion
                .wake
                .wait(state)
                .unwrap_or_else(|e| e.into_inner());
        }
        state.result.take().unwrap_or(Err(JoinError::AlreadyJoined))
    }
}
impl<T> Future for Join<T> {
    type Output = Result<T, JoinError>;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut state = self
            .completion
            .state
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        if state.done {
            Poll::Ready(state.result.take().unwrap_or(Err(JoinError::AlreadyJoined)))
        } else {
            if state
                .waiter
                .as_ref()
                .is_none_or(|waiter| !waiter.will_wake(cx.waker()))
            {
                state.waiter = Some(cx.waker().clone());
            }
            Poll::Pending
        }
    }
}

#[cfg(test)]
mod tests;
