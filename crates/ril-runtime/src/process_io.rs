//! Process transfer workers own host pipes and bytes only; managed values never
//! cross the thread boundary. Every failed/canceled run terminates and reaps its
//! child before returning, and joins all canceled transfer workers.
use crate::platform_io::{self, Pipe};
#[cfg(test)]
mod tests;
use std::{
    io::{self, Read, Write},
    process::{Child, Command, ExitStatus},
    sync::{
        Arc, Condvar, Mutex, Weak,
        atomic::{AtomicBool, AtomicUsize, Ordering},
    },
    thread::{self, JoinHandle},
    time::Duration,
};
#[derive(Debug, Default)]
pub struct Cancellation {
    requested: AtomicBool,
    lock: Mutex<()>,
    wake: Condvar,
    children: Mutex<CancellationChildren>,
    async_waiters: Mutex<CancellationWaiters>,
    parent: Option<(Weak<Cancellation>, u64)>,
}
#[derive(Debug, Default)]
struct CancellationWaiters {
    next: u64,
    live: std::collections::BTreeMap<u64, std::task::Waker>,
}

/// A pending operation owns this registration. Completion removes its wake
/// edge, preventing a cancelled or completed task from being kept alive here.
pub(crate) struct CancellationWake {
    token: Weak<Cancellation>,
    id: Option<u64>,
}
impl Drop for CancellationWake {
    fn drop(&mut self) {
        if let (Some(token), Some(id)) = (self.token.upgrade(), self.id) {
            token
                .async_waiters
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .live
                .remove(&id);
        }
    }
}
impl CancellationWake {
    pub(crate) fn refresh(&mut self, waker: &std::task::Waker) {
        let Some(token) = self.token.upgrade() else {
            return;
        };
        let mut waiters = token
            .async_waiters
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        if token.requested() {
            drop(waiters);
            waker.wake_by_ref();
        } else if let Some(stored) = self.id.and_then(|id| waiters.live.get_mut(&id))
            && !stored.will_wake(waker)
        {
            *stored = waker.clone();
        }
    }
}
#[derive(Debug, Default)]
struct CancellationChildren {
    next: u64,
    live: std::collections::BTreeMap<u64, Weak<Cancellation>>,
}
impl Drop for Cancellation {
    fn drop(&mut self) {
        if let Some((parent, id)) = &self.parent
            && let Some(parent) = parent.upgrade()
        {
            parent
                .children
                .lock()
                .unwrap_or_else(|error| error.into_inner())
                .live
                .remove(id);
        }
    }
}
impl Cancellation {
    /// A scope/body token may cancel its descendants without cancelling its
    /// parent. Registration and an already requested parent cannot lose a race.
    pub fn child(self: &Arc<Self>) -> io::Result<Arc<Self>> {
        let mut children = self
            .children
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        let id = children
            .next
            .checked_add(1)
            .ok_or_else(|| io::Error::other("cancellation identity exhausted"))?;
        children.next = id;
        let child = Arc::new(Self {
            requested: AtomicBool::new(false),
            lock: Mutex::new(()),
            wake: Condvar::new(),
            children: Mutex::default(),
            async_waiters: Mutex::default(),
            parent: Some((Arc::downgrade(self), id)),
        });
        children.live.insert(id, Arc::downgrade(&child));
        let requested = self.requested();
        drop(children);
        if requested {
            child.request();
        }
        Ok(child)
    }
    pub fn request(&self) {
        let mut pending = self.mark_requested();
        while let Some(child) = pending.pop() {
            pending.extend(child.mark_requested());
        }
    }
    fn mark_requested(&self) -> Vec<Arc<Self>> {
        // Synchronize with the predicate-to-wait transition. Atomic visibility
        // alone cannot prevent a Condvar notification from being lost.
        let children = {
            let _guard = self.lock.lock().unwrap_or_else(|error| error.into_inner());
            if self.requested.swap(true, Ordering::AcqRel) {
                self.wake.notify_all();
                return vec![];
            }
            self.wake.notify_all();
            self.children
                .lock()
                .unwrap_or_else(|error| error.into_inner())
                .live
                .values()
                .filter_map(Weak::upgrade)
                .collect::<Vec<_>>()
        };
        let waiters = std::mem::take(
            &mut self
                .async_waiters
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .live,
        );
        // Wakers run outside every cancellation lock, including user-supplied
        // host wakers used by the outer synchronous trampoline.
        for waiter in waiters.into_values() {
            waiter.wake();
        }
        children
    }
    pub(crate) fn subscribe(
        self: &Arc<Self>,
        waker: &std::task::Waker,
    ) -> io::Result<CancellationWake> {
        let mut waiters = self.async_waiters.lock().unwrap_or_else(|e| e.into_inner());
        if self.requested() {
            drop(waiters);
            waker.wake_by_ref();
            return Ok(CancellationWake {
                token: Arc::downgrade(self),
                id: None,
            });
        }
        let id = waiters
            .next
            .checked_add(1)
            .ok_or_else(|| io::Error::other("cancellation wake identity exhausted"))?;
        waiters.next = id;
        waiters.live.insert(id, waker.clone());
        Ok(CancellationWake {
            token: Arc::downgrade(self),
            id: Some(id),
        })
    }
    pub fn requested(&self) -> bool {
        self.requested.load(Ordering::Acquire)
    }
    fn wait(&self) {
        let guard = self.lock.lock().unwrap_or_else(|error| error.into_inner());
        let _ = self
            .wake
            .wait_timeout_while(guard, Duration::from_millis(5), |_| !self.requested())
            .unwrap_or_else(|error| error.into_inner());
    }
    pub(crate) fn sleep(&self, requested: Duration) -> bool {
        let start = std::time::Instant::now();
        let mut guard = self.lock.lock().unwrap_or_else(|error| error.into_inner());
        loop {
            if self.requested() {
                return false;
            }
            let Some(remaining) = requested.checked_sub(start.elapsed()) else {
                return true;
            };
            if remaining.is_zero() {
                return true;
            }
            (guard, _) = self
                .wake
                .wait_timeout(guard, remaining)
                .unwrap_or_else(|error| error.into_inner());
        }
    }
}

#[cfg(test)]
mod cancellation_tree_tests {
    use super::*;
    struct WakeCount(AtomicUsize);
    impl std::task::Wake for WakeCount {
        fn wake(self: Arc<Self>) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
        fn wake_by_ref(self: &Arc<Self>) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }

    #[test]
    fn asynchronous_registration_tracks_the_latest_waiter_and_releases_old_edges() {
        let token = Arc::new(Cancellation::default());
        let first = Arc::new(WakeCount(AtomicUsize::new(0)));
        let second = Arc::new(WakeCount(AtomicUsize::new(0)));
        let mut registration = token
            .subscribe(&std::task::Waker::from(first.clone()))
            .unwrap();
        registration.refresh(&std::task::Waker::from(second.clone()));
        token.request();
        assert_eq!(first.0.load(Ordering::SeqCst), 0);
        assert_eq!(second.0.load(Ordering::SeqCst), 1);
        assert!(token.async_waiters.lock().unwrap().live.is_empty());
        let token = Arc::new(Cancellation::default());
        let counter = Arc::new(WakeCount(AtomicUsize::new(0)));
        let weak = Arc::downgrade(&counter);
        let registration = token.subscribe(&std::task::Waker::from(counter)).unwrap();
        assert!(weak.upgrade().is_some());
        drop(registration);
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn async_waiter_registration_cannot_miss_a_concurrent_cancellation() {
        let token = Arc::new(Cancellation::default());
        let mut workers = Vec::new();
        for _ in 0..4 {
            let token = token.clone();
            workers.push(thread::spawn(move || {
                (0..64)
                    .map(|_| {
                        let counter = Arc::new(WakeCount(AtomicUsize::new(0)));
                        let registration = token
                            .subscribe(&std::task::Waker::from(counter.clone()))
                            .unwrap();
                        (counter, registration)
                    })
                    .collect::<Vec<_>>()
            }));
        }
        token.request();
        for worker in workers {
            for (counter, _registration) in worker.join().unwrap() {
                assert_eq!(counter.0.load(Ordering::SeqCst), 1);
            }
        }
        assert!(token.async_waiters.lock().unwrap().live.is_empty());
    }
    #[test]
    fn local_scope_failure_does_not_cancel_the_parent_or_an_independent_sibling() {
        let parent = Arc::new(Cancellation::default());
        let left = parent.child().unwrap();
        let right = parent.child().unwrap();
        let nested = left.child().unwrap();
        left.request();
        assert!(left.requested() && nested.requested());
        assert!(!parent.requested() && !right.requested());
        parent.request();
        assert!(right.requested());
        assert!(parent.child().unwrap().requested());
    }
    #[test]
    fn concurrent_registration_and_cancellation_leave_no_live_uncancelled_children() {
        let parent = Arc::new(Cancellation::default());
        let handles: Vec<_> = (0..4)
            .map(|_| {
                let parent = parent.clone();
                thread::spawn(move || {
                    (0..128)
                        .map(|_| parent.child().unwrap())
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        parent.request();
        let children: Vec<_> = handles
            .into_iter()
            .flat_map(|thread| thread.join().unwrap())
            .collect();
        assert!(children.iter().all(|child| child.requested()));
        drop(children);
        assert!(parent.children.lock().unwrap().live.is_empty());
    }
    #[test]
    fn deeply_nested_scope_tokens_cancel_without_native_recursion() {
        let root = Arc::new(Cancellation::default());
        let mut nodes = vec![root.clone()];
        for _ in 0..20_000 {
            nodes.push(nodes.last().unwrap().child().unwrap());
        }
        root.request();
        assert!(nodes.iter().all(|node| node.requested()));
        drop(nodes);
        assert!(root.children.lock().unwrap().live.is_empty());
    }
}
#[derive(Debug)]
pub enum RunError {
    Start(io::Error),
    Wait(io::Error),
    Transfer(io::Error),
    CaptureLimit,
    Cancelled,
    WorkerPanic,
}
#[derive(Debug)]
pub struct Output {
    pub status: ExitStatus,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}
enum WorkerResult {
    Data(Vec<u8>),
    Written,
    Failed(io::Error),
    Limit,
    Cancelled,
}
struct Worker {
    stream: u8,
    thread: Option<JoinHandle<WorkerResult>>,
    result: Option<std::thread::Result<WorkerResult>>,
}
impl Worker {
    fn new(stream: u8, thread: JoinHandle<WorkerResult>) -> Self {
        Self {
            stream,
            thread: Some(thread),
            result: None,
        }
    }
    fn poll(&mut self) -> Option<RunError> {
        if self.thread.as_ref().is_some_and(JoinHandle::is_finished) {
            self.result = Some(self.thread.take().unwrap().join());
            match self.result.as_ref().unwrap() {
                Err(_) => return Some(RunError::WorkerPanic),
                Ok(WorkerResult::Failed(error)) => {
                    return Some(RunError::Transfer(
                        error
                            .raw_os_error()
                            .map(io::Error::from_raw_os_error)
                            .unwrap_or_else(|| io::Error::new(error.kind(), error.to_string())),
                    ));
                }
                Ok(WorkerResult::Limit) => return Some(RunError::CaptureLimit),
                _ => {}
            }
        }
        None
    }
}

fn reader<R: Read + Pipe>(
    mut pipe: R,
    limit: usize,
    total: Arc<AtomicUsize>,
    cancel: Arc<Cancellation>,
) -> WorkerResult {
    let outcome = (|| {
        pipe.prepare()?;
        let mut data = Vec::new();
        let mut buffer = [0; 8192];
        loop {
            if cancel.requested() {
                return Ok(WorkerResult::Cancelled);
            }
            match pipe.read(&mut buffer) {
                Ok(0) => return Ok(WorkerResult::Data(data)),
                Ok(count) => {
                    if total
                        .try_update(Ordering::AcqRel, Ordering::Acquire, |old| {
                            old.checked_add(count).filter(|&next| next <= limit)
                        })
                        .is_err()
                    {
                        return Ok(WorkerResult::Limit);
                    }
                    data.try_reserve(count)
                        .map_err(|_| io::Error::other("capture allocation failed"))?;
                    data.extend_from_slice(&buffer[..count]);
                }
                Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => cancel.wait(),
                Err(_) if cancel.requested() => return Ok(WorkerResult::Cancelled),
                Err(error) => return Err(error),
            }
        }
    })();
    match outcome {
        Ok(result) => result,
        Err(error) => WorkerResult::Failed(error),
    }
}
fn writer<W: Write + Pipe>(mut pipe: W, data: Vec<u8>, cancel: Arc<Cancellation>) -> WorkerResult {
    let outcome = (|| {
        pipe.prepare()?;
        let mut written = 0;
        while written < data.len() {
            if cancel.requested() {
                return Ok(WorkerResult::Cancelled);
            }
            #[cfg(target_os = "linux")]
            let result = crate::platform_signal::write(|| pipe.write(&data[written..]));
            #[cfg(not(target_os = "linux"))]
            let result = pipe.write(&data[written..]);
            match result {
                Ok(0) => {
                    return Err(io::Error::new(
                        io::ErrorKind::WriteZero,
                        "process input made no progress",
                    ));
                }
                Ok(count) => written += count,
                Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => cancel.wait(),
                Err(_) if cancel.requested() => return Ok(WorkerResult::Cancelled),
                Err(error) => return Err(error),
            }
        }
        // Closing this owned pipe signals EOF, including for empty Data input.
        Ok(WorkerResult::Written)
    })();
    match outcome {
        Ok(result) => result,
        Err(error) => WorkerResult::Failed(error),
    }
}
pub(crate) fn terminate_reap(child: &mut Child) -> io::Result<ExitStatus> {
    match child.try_wait() {
        Ok(Some(status)) => return Ok(status),
        Ok(None) => {}
        Err(error) => {
            let _ = child.kill();
            child.wait()?;
            return Err(error);
        }
    }
    if let Err(error) = child.kill() {
        if let Some(status) = child.try_wait()? {
            return Ok(status);
        }
        // The owning run cannot abandon a still-running child even when forced
        // termination fails. Waiting has no wall-clock bound under the contract.
        child.wait()?;
        return Err(error);
    }
    child.wait()
}
fn join_workers(
    mut workers: Vec<Worker>,
    cancel: &Cancellation,
) -> Vec<(u8, std::thread::Result<WorkerResult>)> {
    // Cancellation is a request, not completion. A worker may enter its host IO
    // just after the first request, so retry until every worker reports finished.
    while workers.iter().any(|worker| worker.thread.is_some()) {
        if cancel.requested() {
            for worker in &workers {
                if let Some(thread) = &worker.thread {
                    platform_io::cancel(thread);
                }
            }
        }
        for worker in &mut workers {
            worker.poll();
        }
        thread::sleep(Duration::from_millis(1));
    }
    workers
        .into_iter()
        .map(|worker| (worker.stream, worker.result.unwrap()))
        .collect()
}
pub fn run(
    mut command: Command,
    input: Option<Vec<u8>>,
    limit: usize,
    request: Arc<Cancellation>,
) -> Result<Output, RunError> {
    let mut child = command.spawn().map_err(RunError::Start)?;
    // A normal capture/transfer failure cancels only these workers. It must not
    // turn a caller's still-live structured task into a canceled task.
    let cancel = Arc::new(Cancellation::default());
    let total = Arc::new(AtomicUsize::new(0));
    let mut workers = Vec::new();
    let started = (|| -> io::Result<()> {
        if let Some(stdout) = child.stdout.take() {
            let (total, cancel) = (total.clone(), cancel.clone());
            workers.push(Worker::new(
                1,
                thread::Builder::new()
                    .name("ril-process-stdout".into())
                    .spawn(move || reader(stdout, limit, total, cancel))?,
            ));
        }
        if let Some(stderr) = child.stderr.take() {
            let (total, cancel) = (total.clone(), cancel.clone());
            workers.push(Worker::new(
                2,
                thread::Builder::new()
                    .name("ril-process-stderr".into())
                    .spawn(move || reader(stderr, limit, total, cancel))?,
            ));
        }
        if let Some(input) = input {
            let stdin = child
                .stdin
                .take()
                .ok_or_else(|| io::Error::other("missing process input pipe"))?;
            let cancel = cancel.clone();
            workers.push(Worker::new(
                0,
                thread::Builder::new()
                    .name("ril-process-stdin".into())
                    .spawn(move || writer(stdin, input, cancel))?,
            ));
        }
        Ok(())
    })();
    if let Err(error) = started {
        cancel.request();
        let cleaned = terminate_reap(&mut child);
        join_workers(workers, &cancel);
        cleaned.map_err(RunError::Wait)?;
        return Err(RunError::Transfer(error));
    }
    let mut failed = None;
    let status = loop {
        if request.requested() {
            failed = Some(RunError::Cancelled);
            break None;
        }
        for worker in &mut workers {
            if let Some(error) = worker.poll() {
                failed = Some(error);
                break;
            }
        }
        if failed.is_some() {
            break None;
        }
        match child.try_wait() {
            Ok(Some(status)) if workers.iter().all(|worker| worker.thread.is_none()) => {
                break Some(status);
            }
            Ok(_) => {}
            Err(error) => {
                failed = Some(RunError::Wait(error));
                break None;
            }
        }
        thread::sleep(Duration::from_millis(1));
    };
    if failed.is_some() {
        cancel.request();
        let cleaned = terminate_reap(&mut child);
        if let Err(error) = cleaned {
            failed = Some(RunError::Wait(error));
        }
    }
    let (mut stdout, mut stderr) = (vec![], vec![]);
    for (stream, result) in join_workers(workers, &cancel) {
        match result {
            Err(_) => failed = Some(RunError::WorkerPanic),
            Ok(WorkerResult::Failed(error))
                if !matches!(
                    failed,
                    Some(
                        RunError::Wait(_)
                            | RunError::CaptureLimit
                            | RunError::WorkerPanic
                            | RunError::Cancelled
                    )
                ) =>
            {
                failed = Some(RunError::Transfer(error))
            }
            Ok(WorkerResult::Limit)
                if !matches!(
                    failed,
                    Some(RunError::Wait(_) | RunError::WorkerPanic | RunError::Cancelled)
                ) =>
            {
                failed = Some(RunError::CaptureLimit)
            }
            Ok(WorkerResult::Data(data)) if stream == 1 => stdout = data,
            Ok(WorkerResult::Data(data)) if stream == 2 => stderr = data,
            _ => {}
        }
    }
    if let Some(error) = failed {
        Err(error)
    } else {
        let status = status
            .ok_or_else(|| RunError::Wait(io::Error::other("missing observed process status")))?;
        Ok(Output {
            status,
            stdout,
            stderr,
        })
    }
}
