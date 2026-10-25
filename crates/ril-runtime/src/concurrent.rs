//! Structured task state. Managed handles in pending work and completed results
//! are traced through the owning Scope/Task objects, independently of workers.
//! Host waits never run while the managed heap gate is held.
use crate::{
    heap::Handle,
    process_io::Cancellation,
    value::{Result, RuntimeError},
};
use ril_runtime_api::abi::OutcomeTag;
use std::{
    sync::{
        Arc, Condvar, Mutex, Weak,
        atomic::{AtomicBool, AtomicU64, Ordering},
    },
    time::Duration,
};

mod async_finish;
mod async_join;
#[cfg(test)]
#[path = "concurrent_tests.rs"]
mod tests;
pub(crate) use async_finish::FinishFuture;
pub(crate) use async_join::JoinFuture;

static NEXT_SCOPE: AtomicU64 = AtomicU64::new(1);

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct TaskOwner {
    pub scope: u64,
    pub ordinal: u64,
}

#[derive(Debug)]
pub struct Scope {
    id: u64,
    pub(crate) body_cancellation: Arc<Cancellation>,
    children_cancellation: Arc<Cancellation>,
    failed: AtomicBool,
    state: Mutex<ScopeState>,
}

#[derive(Debug, Default)]
struct ScopeState {
    finishing: bool,
    closed: bool,
    tasks: Vec<Arc<Task>>,
    channels: Vec<(Handle, crate::channel::Endpoint)>,
}

impl PartialEq for Scope {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

#[derive(Debug)]
pub struct Task {
    scope: Weak<Scope>,
    scope_id: u64,
    ordinal: usize,
    creator: TaskOwner,
    action: Handle,
    pub(crate) cancellation: Arc<Cancellation>,
    completion: Mutex<Completion>,
    wake: Condvar,
    worker: Mutex<Option<TaskWorker>>,
}

#[derive(Debug)]
enum TaskWorker {
    Scheduled(crate::scheduler::Join<Result<()>>),
    #[cfg(test)]
    Thread(std::thread::JoinHandle<()>),
}
#[cfg(test)]
impl TaskWorker {
    fn wait(self) -> Result<()> {
        match self {
            Self::Thread(worker) => worker
                .join()
                .map_err(|_| RuntimeError::internal("unexpected Rust panic in task worker")),
            Self::Scheduled(worker) => worker
                .wait()
                .map_err(|_| RuntimeError::internal("unexpected Rust panic in task worker"))?,
        }
    }
}

#[derive(Debug, Default)]
struct Completion {
    outcome: Option<Result<Handle>>,
    observed: bool,
    next_waiter: u64,
    waiters: std::collections::BTreeMap<u64, std::task::Waker>,
}

#[derive(Debug, Clone)]
pub(crate) struct ActiveScope {
    pub scope: Arc<Scope>,
    pub value: Handle,
    pub continuation: Handle,
    pub handlers: Handle,
    pub activation: Handle,
    pub parent_activation: Handle,
    pub parent_cancellation: Arc<Cancellation>,
    pub lineage_depth: usize,
    pub delimiters: Vec<Handle>,
    pub budget_depth: usize,
}
impl ActiveScope {
    pub(crate) fn references(&self) -> impl Iterator<Item = Handle> {
        [
            self.value,
            self.continuation,
            self.handlers,
            self.activation,
            self.parent_activation,
        ]
        .into_iter()
        .chain(self.delimiters.iter().copied())
        .filter(|&handle| handle != Handle::INVALID)
    }
}

impl PartialEq for Task {
    fn eq(&self, other: &Self) -> bool {
        self.scope_id == other.scope_id && self.ordinal == other.ordinal
    }
}

impl Scope {
    pub(crate) fn id(&self) -> u64 {
        self.id
    }
    pub(crate) fn new(parent: &Arc<Cancellation>) -> Result<Arc<Self>> {
        let id = NEXT_SCOPE
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .map_err(|_| RuntimeError::internal("task scope identity exhausted"))?;
        let body = parent
            .child()
            .map_err(|error| RuntimeError::internal(error.to_string()))?;
        let children = parent
            .child()
            .map_err(|error| RuntimeError::internal(error.to_string()))?;
        Ok(Arc::new(Self {
            id,
            body_cancellation: body,
            children_cancellation: children,
            failed: AtomicBool::new(false),
            state: Mutex::default(),
        }))
    }

    pub(crate) fn reserve(
        self: &Arc<Self>,
        action: Handle,
        creator: TaskOwner,
    ) -> Result<Arc<Task>> {
        let mut state = self.state.lock().unwrap_or_else(|error| error.into_inner());
        if state.finishing || state.closed || self.failed() || self.body_cancellation.requested() {
            return Err(RuntimeError::cancelled());
        }
        let cancellation = self
            .children_cancellation
            .child()
            .map_err(|error| RuntimeError::internal(error.to_string()))?;
        let task = Arc::new(Task {
            scope: Arc::downgrade(self),
            scope_id: self.id,
            ordinal: state.tasks.len(),
            creator,
            action,
            cancellation,
            completion: Mutex::default(),
            wake: Condvar::new(),
            worker: Mutex::default(),
        });
        state.tasks.push(task.clone());
        Ok(task)
    }

    pub(crate) fn cancel_children(&self) {
        self.children_cancellation.request();
    }

    fn fail(&self) {
        self.failed.store(true, Ordering::Release);
        self.body_cancellation.request();
        self.cancel_children();
    }

    pub(crate) fn failed(&self) -> bool {
        self.failed.load(Ordering::Acquire)
    }

    pub(crate) fn references(&self) -> Vec<Handle> {
        let state = self.state.lock().unwrap_or_else(|error| error.into_inner());
        state
            .tasks
            .iter()
            .flat_map(|task| task.references())
            .chain(state.channels.iter().map(|(handle, _)| *handle))
            .collect()
    }

    pub(crate) fn register_channel(
        &self,
        value: Handle,
        endpoint: crate::channel::Endpoint,
    ) -> Result<()> {
        let mut state = self.state.lock().unwrap_or_else(|error| error.into_inner());
        if state.closed {
            return Err(RuntimeError::cancelled());
        }
        state.channels.push((value, endpoint));
        Ok(())
    }

    /// Wait for every completion, then reap every native worker. The caller
    /// decides whether a body panic/abort propagates or a TaskFault is returned.
    #[cfg(test)]
    pub(crate) fn finish(&self, cancel: bool) -> Result<Option<RuntimeError>> {
        if cancel {
            self.cancel_children();
        }
        let tasks = {
            let mut state = self.state.lock().unwrap_or_else(|error| error.into_inner());
            state.finishing = true;
            state.tasks.clone()
        };
        let mut failure = None;
        for task in tasks {
            if let Err(error) = task.wait(None) {
                failure = choose_fault(failure, Some(error));
            }
            if let Some(worker) = task
                .worker
                .lock()
                .unwrap_or_else(|error| error.into_inner())
                .take()
                && worker.wait().is_err()
            {
                failure = choose_fault(
                    failure,
                    Some(RuntimeError::internal(
                        "unexpected Rust panic in task worker",
                    )),
                );
            }
        }
        self.close_channels();
        Ok(failure)
    }
    fn close_channels(&self) {
        let channels = {
            let mut state = self.state.lock().unwrap_or_else(|error| error.into_inner());
            state.closed = true;
            state.channels.clone()
        };
        for (_, endpoint) in channels {
            endpoint.close_in_scope(self.id);
        }
        // Keep descriptors traced throughout host-side queue/resource release.
        self.state
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .channels
            .clear();
    }
}

impl Task {
    pub(crate) fn creator(&self) -> TaskOwner {
        self.creator
    }
    pub(crate) fn scope_id(&self) -> u64 {
        self.scope_id
    }
    pub(crate) fn owner(&self) -> TaskOwner {
        TaskOwner {
            scope: self.scope_id,
            ordinal: self.ordinal as u64,
        }
    }
    pub(crate) fn action(&self) -> Handle {
        self.action
    }

    #[cfg(test)]
    pub(crate) fn install_worker(&self, worker: std::thread::JoinHandle<()>) -> Result<()> {
        self.install(TaskWorker::Thread(worker))
    }
    pub(crate) fn install_scheduled(
        &self,
        worker: crate::scheduler::Join<Result<()>>,
    ) -> Result<()> {
        self.install(TaskWorker::Scheduled(worker))
    }
    fn install(&self, worker: TaskWorker) -> Result<()> {
        let mut slot = self
            .worker
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        if slot.is_some() {
            return Err(RuntimeError::internal("task worker installed twice"));
        }
        *slot = Some(worker);
        Ok(())
    }

    /// Call under the managed heap gate when publishing an ordinary result so
    /// the worker's temporary root and the task's result root overlap.
    pub(crate) fn complete(&self, outcome: Result<Handle>) -> Result<()> {
        let failed = outcome.is_err();
        let waiters = {
            let mut completion = self
                .completion
                .lock()
                .unwrap_or_else(|error| error.into_inner());
            if completion.outcome.is_some() {
                return Err(RuntimeError::internal("task completed twice"));
            }
            // Publish permanent scope failure before exposing the outcome. A
            // subsequent fork cannot race through the failure-to-cancel gap.
            if failed && let Some(scope) = self.scope.upgrade() {
                scope.fail();
            }
            completion.outcome = Some(outcome);
            self.wake.notify_all();
            std::mem::take(&mut completion.waiters)
        };
        for waiter in waiters.into_values() {
            waiter.wake();
        }
        Ok(())
    }

    pub(crate) fn references(&self) -> Vec<Handle> {
        let completion = self
            .completion
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        std::iter::once(self.action)
            .chain(
                completion
                    .outcome
                    .as_ref()
                    .and_then(|outcome| outcome.as_ref().ok())
                    .copied(),
            )
            .filter(|&handle| handle != Handle::INVALID)
            .collect()
    }

    fn wait(&self, cancellation: Option<&Cancellation>) -> Result<Handle> {
        let mut completion = self
            .completion
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        loop {
            if let Some(outcome) = &completion.outcome {
                return outcome.clone();
            }
            if cancellation.is_some_and(Cancellation::requested) {
                return Err(RuntimeError::cancelled());
            }
            (completion, _) = self
                .wake
                .wait_timeout(completion, Duration::from_millis(5))
                .unwrap_or_else(|error| error.into_inner());
        }
    }

    pub(crate) fn join(&self, cancellation: &Cancellation) -> Result<Result<Handle>> {
        let outcome = self.wait(Some(cancellation));
        if matches!(&outcome, Err(error) if error.tag == OutcomeTag::Cancelled)
            && self
                .completion
                .lock()
                .unwrap_or_else(|error| error.into_inner())
                .outcome
                .is_none()
        {
            return Err(RuntimeError::cancelled());
        }
        let mut completion = self
            .completion
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        if completion.observed {
            return Err(RuntimeError::panic("task result already observed"));
        }
        completion.observed = true;
        Ok(outcome)
    }
}

/// Earlier means creation order, with an explicit body TaskFault inserted first.
pub(crate) fn choose_fault(
    earlier: Option<RuntimeError>,
    later: Option<RuntimeError>,
) -> Option<RuntimeError> {
    let selected = match (earlier, later) {
        (Some(a), Some(b)) => Some(if fault_rank(&b) > fault_rank(&a) {
            b
        } else {
            a
        }),
        (a, b) => a.or(b),
    };
    selected.map(|error| error.internal_fault().cloned().unwrap_or(error))
}
pub(crate) fn fault_rank(error: &RuntimeError) -> u8 {
    if error.internal_fault().is_some() {
        return 4;
    }
    match error.tag {
        OutcomeTag::InternalFault => 4,
        OutcomeTag::DoubleFault => 3,
        OutcomeTag::LanguagePanic => 2,
        _ => 1,
    }
}
