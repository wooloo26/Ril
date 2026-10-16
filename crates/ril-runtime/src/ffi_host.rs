//! Native host waits carry owned requests and replies, never Runtime borrows.
use super::*;
use crate::{
    file::{filesystem, host as file},
    host_job::Job,
    host_stdio as stdio,
    process::host as process,
    process_io::Cancellation,
};
use std::{
    future::Future,
    pin::Pin,
    sync::Arc,
    task::{Context, Poll},
};

enum Request {
    Entropy(crate::host_service::Request),
    Stdio(stdio::Request),
    File(file::Request),
    FileSystem(filesystem::Request),
    Process(Box<process::Request>),
}
enum Reply {
    Entropy(crate::host_service::Reply),
    Stdio(stdio::Reply),
    File(file::Reply),
    FileSystem(filesystem::Reply),
    Process(process::Reply),
}
impl Request {
    fn perform(self) -> Result<Reply> {
        match self {
            Self::Entropy(request) => request.perform().map(Reply::Entropy),
            Self::Stdio(request) => request.perform().map(Reply::Stdio),
            Self::File(request) => request.perform().map(Reply::File),
            Self::FileSystem(request) => request.perform().map(Reply::FileSystem),
            Self::Process(request) => request.perform().map(Reply::Process),
        }
    }
}
impl Reply {
    fn finish(self, runtime: &mut Runtime) -> Result<Handle> {
        match self {
            Self::Entropy(reply) => crate::host_service::finish(runtime, reply),
            Self::Stdio(reply) => stdio::finish(runtime, reply),
            Self::File(reply) => file::finish(runtime, reply),
            Self::FileSystem(reply) => filesystem::finish(runtime, reply),
            Self::Process(reply) => process::finish(runtime, reply),
        }
    }
    fn discard(self) -> Result<()> {
        if let Self::Process(reply) = self {
            process::discard(reply)?;
        }
        Ok(())
    }
}
enum State {
    Running(Job<Reply>),
    Discarding(Job<()>),
    Complete,
}
pub(super) struct PendingHost {
    state: State,
    continuation: Handle,
}

pub(super) fn prepare(
    callable: Handle,
    arguments: Handle,
    continuation: Handle,
) -> Option<PendingHost> {
    let name = with_runtime(|runtime| match runtime.heap.get(callable) {
        Ok(Object::Builtin(name)) => {
            let name = name.strip_prefix("Prelude::").unwrap_or(name);
            Some(
                ril_runtime_api::builtins::canonical_builtin(name)
                    .unwrap_or(name)
                    .to_owned(),
            )
        }
        _ => None,
    })?;
    if name != "Random::entropy"
        && !stdio::is_operation(&name)
        && !file::is_operation(&name)
        && !filesystem::is_operation(&name)
        && !process::is_operation(&name)
    {
        return None;
    }
    let prepared: Option<(Request, Arc<Cancellation>)> = guarded(|runtime| {
        let arguments = runtime.sequence(arguments)?;
        let cancellation = runtime
            .host_cancellation()
            .child()
            .map_err(|error| RuntimeError::internal(error.to_string()))?;
        let request = if name == "Random::entropy" {
            Request::Entropy(
                crate::host_service::prepare(runtime, &name, &arguments)?
                    .with_cancellation(cancellation.clone()),
            )
        } else if stdio::is_operation(&name) {
            Request::Stdio(
                stdio::prepare(runtime, &name, &arguments)?.with_cancellation(cancellation.clone()),
            )
        } else if file::is_operation(&name) {
            Request::File(
                file::prepare(runtime, &name, &arguments)?.with_cancellation(cancellation.clone()),
            )
        } else if filesystem::is_operation(&name) {
            Request::FileSystem(
                filesystem::prepare(runtime, &name, &arguments)?
                    .with_cancellation(cancellation.clone()),
            )
        } else {
            Request::Process(Box::new(
                process::prepare(runtime, &name, &arguments)?
                    .with_cancellation(cancellation.clone()),
            ))
        };
        Ok(Some((request, cancellation)))
    });
    let (request, cancellation) = prepared?;
    match Job::start(move || request.perform(), cancellation, Reply::discard) {
        Ok(job) => Some(PendingHost {
            state: State::Running(job),
            continuation,
        }),
        Err(error) => {
            with_runtime(|runtime| runtime.fault = Some(error));
            None
        }
    }
}

pub(super) fn poll(pending: &mut PendingHost, context: &mut Context<'_>) -> Poll<u64> {
    match &mut pending.state {
        State::Running(job) => {
            let Poll::Ready(result) = Pin::new(job).poll(context) else {
                return Poll::Pending;
            };
            pending.state = State::Complete;
            let mut unpublished = None;
            let value = match result {
                Err(error) => finish_host::<()>(Err(error), |runtime, ()| runtime.unit()),
                Ok(reply) => {
                    unpublished = Some(reply);
                    handle(|runtime| {
                        unpublished
                            .take()
                            .expect("unpublished host reply")
                            .finish(runtime)
                    })
                }
            };
            if let Some(reply) = unpublished {
                // Spawn cancellation may require process terminate/reap. That
                // discard is itself mandatory host work; keep the fault pending.
                match Job::start(move || reply.discard(), Arc::default(), |()| Ok(())) {
                    Ok(job) => {
                        pending.state = State::Discarding(job);
                        return poll(pending, context);
                    }
                    Err(mut error) => {
                        with_runtime(|runtime| {
                            error.primary = runtime.fault.take().map(Box::new);
                            runtime.fault = Some(error);
                        });
                        return Poll::Ready(0);
                    }
                }
            }
            Poll::Ready(if value == 0 {
                0
            } else {
                return_step(pending.continuation, value)
            })
        }
        State::Discarding(job) => {
            let Poll::Ready(result) = Pin::new(job).poll(context) else {
                return Poll::Pending;
            };
            pending.state = State::Complete;
            if let Err(mut error) = result {
                with_runtime(|runtime| {
                    error.primary = runtime.fault.take().map(Box::new);
                    runtime.fault = Some(error);
                });
            }
            Poll::Ready(0)
        }
        State::Complete => {
            with_runtime(|runtime| {
                runtime.fault = Some(RuntimeError::internal(
                    "host operation polled after completion",
                ))
            });
            Poll::Ready(0)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn cancelled_unpublished_spawn_is_drained_before_the_pending_native_reply_finishes() {
        ril_rt_init();
        let child = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "process_io::tests::child_fixture",
                "--ignored",
                "--nocapture",
            ])
            .env("RIL_PROCESS_IO_FIXTURE", "sleep")
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .unwrap();
        let job = Job::start(
            move || Ok(Reply::Process(process::Reply::Spawn(Ok(child)))),
            Arc::default(),
            Reply::discard,
        )
        .unwrap();
        let mut pending = PendingHost {
            state: State::Running(job),
            continuation: Handle::INVALID,
        };
        with_runtime(|runtime| runtime.cancellation.request());
        let started = std::time::Instant::now();
        let mut context = Context::from_waker(std::task::Waker::noop());
        loop {
            if let Poll::Ready(value) = poll(&mut pending, &mut context) {
                assert_eq!(value, 0);
                break;
            }
            assert!(
                started.elapsed() < std::time::Duration::from_secs(3),
                "unpublished child cleanup did not finish"
            );
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
        assert!(matches!(pending.state, State::Complete));
        with_runtime(|runtime| {
            assert!(runtime.children.is_empty());
            assert_eq!(runtime.fault.as_ref().unwrap().tag, OutcomeTag::Cancelled);
        });
    }
}
