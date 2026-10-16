//! Isolated provider transport. It owns native processes, pipes and bytes only;
//! managed callbacks and their continuations remain on the owning Ril task.
use crate::{
    platform_io::{self, Pipe},
    process_io::{self, Cancellation},
};
use ril_runtime_api::foreign::{ClientMessage, ProviderConfig, ProviderMessage};
use std::{
    collections::VecDeque,
    io::{self, Read, Write},
    panic::{AssertUnwindSafe, catch_unwind},
    process::{Child, Command, ExitStatus, Stdio},
    sync::{
        Arc, Mutex,
        mpsc::{self, Receiver, SyncSender, TrySendError},
    },
    thread::{self, JoinHandle},
    time::Duration,
};

const POLL: Duration = Duration::from_millis(5);
const STDERR_TAIL: usize = 64 * 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Failure {
    Binding(String),
    Cancelled,
    Internal(String),
}
type Result<T> = std::result::Result<T, Failure>;

/// Requests and replies contain host data only. Managed callback handles remain
/// in the owning Runtime, including while this request is pending.
pub(crate) enum Request {
    Start {
        provider: ProviderConfig,
        cancellation: Arc<Cancellation>,
        message: ClientMessage,
    },
    Exchange {
        session: Session,
        message: ClientMessage,
    },
    Finish {
        session: Session,
        values: ril_runtime_api::foreign::Graph,
    },
}
pub(crate) enum Reply {
    Event {
        session: Box<Session>,
        event: ProviderMessage,
    },
    Finished(ril_runtime_api::foreign::Graph),
}
impl Request {
    pub(crate) fn perform(self) -> Result<Reply> {
        match self {
            Self::Start {
                provider,
                cancellation,
                message,
            } => {
                let mut session = Session::start(&provider, cancellation)?;
                match session.next()? {
                    ProviderMessage::Ready {
                        version: ril_runtime_api::foreign::PROTOCOL_VERSION,
                    } => {}
                    _ => {
                        return Err(session.fail(Failure::Binding(
                            "missing or unsupported Ready handshake".into(),
                        )));
                    }
                }
                session.send(&message)?;
                let event = session.next()?;
                Ok(Reply::Event {
                    session: Box::new(session),
                    event,
                })
            }
            Self::Exchange {
                mut session,
                message,
            } => {
                session.send(&message)?;
                let event = session.next()?;
                Ok(Reply::Event {
                    session: Box::new(session),
                    event,
                })
            }
            Self::Finish {
                mut session,
                values,
            } => {
                session.finish()?;
                Ok(Reply::Finished(values))
            }
        }
    }
    /// Cancelling an unstarted request never spawns a provider. A live provider
    /// is terminated and reaped before the invocation may leave its activation.
    pub(crate) fn discard(self) -> Result<()> {
        match self {
            Self::Start { .. } => Ok(()),
            Self::Exchange { mut session, .. } | Self::Finish { mut session, .. } => {
                session.abort()
            }
        }
    }
}
impl Reply {
    pub(crate) fn discard(self) -> Result<()> {
        match self {
            Self::Event { mut session, .. } => session.abort(),
            Self::Finished(_) => Ok(()),
        }
    }
}
#[derive(Debug)]
enum Event {
    Frame(Vec<u8>),
    Eof,
    Wake,
}

#[derive(Debug)]
pub(crate) struct Session {
    child: Child,
    status: Option<ExitStatus>,
    requests: Option<SyncSender<Vec<u8>>>,
    events: Receiver<Event>,
    acknowledge: SyncSender<()>,
    workers: Vec<JoinHandle<()>>,
    stop: Arc<Cancellation>,
    cancellation: Arc<Cancellation>,
    failure: Arc<Mutex<Option<Failure>>>,
    stderr: Arc<Mutex<VecDeque<u8>>>,
    limit: u64,
    closed: bool,
}

impl Session {
    pub(crate) fn start(config: &ProviderConfig, cancellation: Arc<Cancellation>) -> Result<Self> {
        if cancellation.requested() {
            return Err(Failure::Cancelled);
        }
        if !config.program.is_absolute() || config.max_frame_bytes == 0 {
            return Err(Failure::Binding(
                "external provider needs an absolute program and positive frame limit".into(),
            ));
        }
        let mut command = Command::new(&config.program);
        command
            .args(&config.args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        #[cfg(windows)]
        {
            use std::os::windows::process::CommandExt;
            command.creation_flags(0x0800_0000); // CREATE_NO_WINDOW: provider is a protocol worker.
        }
        let mut child = command.spawn().map_err(|error| {
            Failure::Binding(format!(
                "cannot start external provider {}: {error}",
                config.id
            ))
        })?;
        let stdin = child.stdin.take().expect("piped provider input");
        let stdout = child.stdout.take().expect("piped provider output");
        let stderr = child.stderr.take().expect("piped provider diagnostics");
        let (requests, input) = mpsc::sync_channel(1);
        let (events, received) = mpsc::channel();
        let (acknowledge, acknowledgments) = mpsc::sync_channel(1);
        let mut session = Self {
            child,
            status: None,
            requests: Some(requests),
            events: received,
            acknowledge,
            workers: vec![],
            stop: Arc::default(),
            cancellation,
            failure: Arc::default(),
            stderr: Arc::default(),
            limit: config.max_frame_bytes,
            closed: false,
        };
        let started = (|| {
            let stop = session.stop.clone();
            session.worker("ril-provider-input", events.clone(), move || {
                write_frames(stdin, input, &stop)
            })?;
            let stop = session.stop.clone();
            let output = events.clone();
            let limit = session.limit;
            session.worker("ril-provider-output", events.clone(), move || {
                read_frames(stdout, output, acknowledgments, &stop, limit)
            })?;
            let stop = session.stop.clone();
            let tail = session.stderr.clone();
            session.worker("ril-provider-stderr", events, move || {
                drain_stderr(stderr, &stop, &tail)
            })
        })();
        if let Err(error) = started {
            return Err(session.fail(error));
        }
        Ok(session)
    }

    fn worker(
        &mut self,
        name: &str,
        events: mpsc::Sender<Event>,
        operation: impl FnOnce() -> Result<()> + Send + 'static,
    ) -> Result<()> {
        let failure = self.failure.clone();
        let stop = self.stop.clone();
        let worker = thread::Builder::new()
            .name(name.into())
            .spawn(move || {
                let result = catch_unwind(AssertUnwindSafe(operation)).unwrap_or_else(|_| {
                    Err(Failure::Internal(
                        "unexpected Rust panic in external provider transport".into(),
                    ))
                });
                if let Err(error) = result
                    && (!stop.requested() || matches!(error, Failure::Internal(_)))
                {
                    let mut saved = failure.lock().unwrap_or_else(|error| error.into_inner());
                    if saved.is_none() || matches!(error, Failure::Internal(_)) {
                        *saved = Some(error);
                    }
                    let _ = events.send(Event::Wake);
                }
            })
            .map_err(|error| {
                Failure::Internal(format!("cannot start external transport worker: {error}"))
            })?;
        self.workers.push(worker);
        Ok(())
    }

    pub(crate) fn send(&mut self, message: &ClientMessage) -> Result<()> {
        if let Err(error) = self.check() {
            return Err(self.fail(error));
        }
        let mut bytes = match encode(message, self.limit) {
            Ok(bytes) => bytes,
            Err(error) => return Err(self.fail(error)),
        };
        loop {
            if let Err(error) = self.check() {
                return Err(self.fail(error));
            }
            let Some(sender) = &self.requests else {
                return Err(self.fail(Failure::Binding("external input already closed".into())));
            };
            match sender.try_send(bytes) {
                Ok(()) => return Ok(()),
                Err(TrySendError::Full(returned)) => bytes = returned,
                Err(TrySendError::Disconnected(_)) => {
                    return Err(self.fail(Failure::Binding("external input pipe closed".into())));
                }
            }
            thread::sleep(POLL);
        }
    }

    pub(crate) fn next(&mut self) -> Result<ProviderMessage> {
        loop {
            if let Err(error) = self.check() {
                return Err(self.fail(error));
            }
            match self.events.recv_timeout(POLL) {
                Ok(Event::Frame(bytes)) => {
                    let _ = self.acknowledge.try_send(());
                    return serde_json::from_slice(&bytes).map_err(|error| {
                        self.fail(Failure::Binding(format!(
                            "invalid external protocol frame: {error}"
                        )))
                    });
                }
                Ok(Event::Eof) => {
                    return Err(self.fail(Failure::Binding(
                        "external provider closed output before a required reply".into(),
                    )));
                }
                Ok(Event::Wake) | Err(mpsc::RecvTimeoutError::Timeout) => {}
                Err(mpsc::RecvTimeoutError::Disconnected) => {
                    return Err(self.fail(Failure::Binding(
                        "external provider transport ended before a required reply".into(),
                    )));
                }
            }
        }
    }

    /// The final reply is provisional until the provider exits successfully.
    /// Closing input permits an adapter to finish after observing owner EOF.
    pub(crate) fn finish(&mut self) -> Result<()> {
        self.requests.take();
        let mut eof = false;
        loop {
            if let Err(error) = self.check() {
                return Err(self.fail(error));
            }
            match self.events.recv_timeout(POLL) {
                Ok(Event::Frame(_)) => {
                    return Err(self.fail(Failure::Binding(
                        "external provider sent a message after its final reply".into(),
                    )));
                }
                Ok(Event::Eof) => eof = true,
                Ok(Event::Wake)
                | Err(mpsc::RecvTimeoutError::Timeout | mpsc::RecvTimeoutError::Disconnected) => {}
            }
            match self.child.try_wait() {
                Ok(Some(status)) => {
                    self.status = Some(status);
                    if !status.success() {
                        return Err(self.fail(Failure::Binding(format!(
                            "external provider exited with {status}"
                        ))));
                    }
                    if eof {
                        return self.shutdown();
                    }
                }
                Ok(None) => {}
                Err(error) => {
                    return Err(self.fail(Failure::Internal(format!(
                        "cannot observe external provider completion: {error}"
                    ))));
                }
            }
        }
    }

    pub(crate) fn abort(&mut self) -> Result<()> {
        self.shutdown()
    }

    fn check(&self) -> Result<()> {
        let failed = self
            .failure
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .clone();
        if let Some(Failure::Internal(_)) = &failed {
            return Err(failed.unwrap());
        }
        if self.cancellation.requested() {
            return Err(Failure::Cancelled);
        }
        if self.closed {
            return Err(Failure::Binding(
                "external provider invocation is closed".into(),
            ));
        }
        match failed {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }

    fn fail(&mut self, mut failure: Failure) -> Failure {
        if let Err(error) = self.shutdown() {
            return error;
        }
        if let Failure::Binding(message) = &mut failure {
            let tail: Vec<_> = self
                .stderr
                .lock()
                .unwrap_or_else(|error| error.into_inner())
                .iter()
                .copied()
                .collect();
            if !tail.is_empty() {
                message.push_str(&format!(
                    "; provider stderr: {}",
                    String::from_utf8_lossy(&tail)
                ));
            }
        }
        failure
    }

    fn shutdown(&mut self) -> Result<()> {
        if self.closed {
            return Ok(());
        }
        self.stop.request();
        self.requests.take();
        let mut error = if self.status.is_none() {
            match process_io::terminate_reap(&mut self.child) {
                Ok(status) => {
                    self.status = Some(status);
                    None
                }
                Err(error) => Some(Failure::Internal(format!(
                    "cannot terminate and reap external provider: {error}"
                ))),
            }
        } else {
            None
        };
        while self.workers.iter().any(|worker| !worker.is_finished()) {
            for worker in &self.workers {
                platform_io::cancel(worker);
            }
            thread::sleep(Duration::from_millis(1));
        }
        for worker in self.workers.drain(..) {
            if worker.join().is_err() {
                error = Some(Failure::Internal(
                    "unexpected Rust panic in external provider transport".into(),
                ));
            }
        }
        if let Some(Failure::Internal(message)) = self
            .failure
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .as_ref()
        {
            error = Some(Failure::Internal(message.clone()));
        }
        self.closed = true;
        match error {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }
}
impl Drop for Session {
    fn drop(&mut self) {
        let _ = self.shutdown();
    }
}

fn encode(message: &ClientMessage, limit: u64) -> Result<Vec<u8>> {
    struct Bounded {
        bytes: Vec<u8>,
        limit: u64,
    }
    impl Write for Bounded {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            if bytes.len() as u64 > self.limit.saturating_sub(self.bytes.len() as u64) {
                return Err(io::Error::other(
                    "external protocol frame exceeds configured limit",
                ));
            }
            self.bytes
                .try_reserve(bytes.len())
                .map_err(|_| io::Error::other("external protocol frame allocation failed"))?;
            self.bytes.extend_from_slice(bytes);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }
    let mut output = Bounded {
        bytes: vec![],
        limit,
    };
    serde_json::to_writer(&mut output, message).map_err(|error| {
        Failure::Binding(format!("cannot encode external protocol frame: {error}"))
    })?;
    Ok(output.bytes)
}

fn write_frames<W: Write + Pipe>(
    mut pipe: W,
    input: Receiver<Vec<u8>>,
    stop: &Cancellation,
) -> Result<()> {
    pipe.prepare().map_err(binding_io)?;
    while !stop.requested() {
        let data = match input.recv_timeout(POLL) {
            Ok(data) => data,
            Err(mpsc::RecvTimeoutError::Timeout) => continue,
            Err(mpsc::RecvTimeoutError::Disconnected) => return Ok(()),
        };
        for data in [&(data.len() as u64).to_le_bytes()[..], &data[..]] {
            let mut offset = 0;
            while offset < data.len() {
                if stop.requested() {
                    return Ok(());
                }
                #[cfg(target_os = "linux")]
                let result = crate::platform_signal::write(|| pipe.write(&data[offset..]));
                #[cfg(not(target_os = "linux"))]
                let result = pipe.write(&data[offset..]);
                match result {
                    Ok(0) => {
                        return Err(Failure::Binding(
                            "external provider input made no progress".into(),
                        ));
                    }
                    Ok(count) => offset += count,
                    Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                        stop.sleep(POLL);
                    }
                    Err(error) => return Err(binding_io(error)),
                }
            }
        }
    }
    Ok(())
}

fn read_exact<R: Read>(pipe: &mut R, bytes: &mut [u8], stop: &Cancellation) -> Result<bool> {
    let mut offset = 0;
    while offset < bytes.len() {
        if stop.requested() {
            return Ok(false);
        }
        match pipe.read(&mut bytes[offset..]) {
            Ok(0) if offset == 0 => return Ok(false),
            Ok(0) => {
                return Err(Failure::Binding(
                    "external provider truncated a protocol frame".into(),
                ));
            }
            Ok(count) => offset += count,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                stop.sleep(POLL);
            }
            Err(error) => return Err(binding_io(error)),
        }
    }
    Ok(true)
}
fn read_frames<R: Read + Pipe>(
    mut pipe: R,
    events: mpsc::Sender<Event>,
    acknowledge: Receiver<()>,
    stop: &Cancellation,
    limit: u64,
) -> Result<()> {
    pipe.prepare().map_err(binding_io)?;
    loop {
        let mut header = [0; 8];
        if !read_exact(&mut pipe, &mut header, stop)? {
            let _ = events.send(Event::Eof);
            return Ok(());
        }
        let length = u64::from_le_bytes(header);
        if length > limit {
            return Err(Failure::Binding(
                "external protocol frame exceeds configured limit".into(),
            ));
        }
        let length = usize::try_from(length).map_err(|_| {
            Failure::Binding("external frame length cannot be represented on this target".into())
        })?;
        let mut data = vec![];
        data.try_reserve_exact(length)
            .map_err(|_| Failure::Binding("external protocol frame allocation failed".into()))?;
        data.resize(length, 0);
        if !read_exact(&mut pipe, &mut data, stop)? {
            if stop.requested() {
                return Ok(());
            }
            return Err(Failure::Binding(
                "external provider omitted its frame body".into(),
            ));
        }
        if events.send(Event::Frame(data)).is_err() {
            return Ok(());
        }
        loop {
            if stop.requested() {
                return Ok(());
            }
            match acknowledge.recv_timeout(POLL) {
                Ok(()) => break,
                Err(mpsc::RecvTimeoutError::Timeout) => {}
                Err(mpsc::RecvTimeoutError::Disconnected) => return Ok(()),
            }
        }
    }
}
fn drain_stderr<R: Read + Pipe>(
    mut pipe: R,
    stop: &Cancellation,
    tail: &Mutex<VecDeque<u8>>,
) -> Result<()> {
    pipe.prepare().map_err(binding_io)?;
    let mut data = [0; 8192];
    while !stop.requested() {
        match pipe.read(&mut data) {
            Ok(0) => return Ok(()),
            Ok(count) => {
                let mut tail = tail.lock().unwrap_or_else(|error| error.into_inner());
                tail.extend(&data[..count]);
                while tail.len() > STDERR_TAIL {
                    tail.pop_front();
                }
            }
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                stop.sleep(POLL);
            }
            Err(error) => return Err(binding_io(error)),
        }
    }
    Ok(())
}
fn binding_io(error: io::Error) -> Failure {
    Failure::Binding(format!("external provider IO failed: {error}"))
}

#[cfg(test)]
#[path = "foreign_process_tests.rs"]
mod tests;
