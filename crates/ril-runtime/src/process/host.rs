//! Process launch/transfer owns only host command state while it is outside the
//! managed-heap gate. Cancellation completes terminate/reap before propagating.
use super::*;
use crate::process_io::Cancellation;
use std::sync::{Arc, Mutex};

pub(crate) struct Request {
    operation: Operation,
    cancellation: Arc<Cancellation>,
}
enum Operation {
    Launch {
        prepared: Box<std::result::Result<Prepared, PrepareError>>,
        limit: Option<usize>,
    },
    Await {
        child: Arc<Mutex<ChildState>>,
        terminate: bool,
    },
}
pub(crate) enum Reply {
    Invalid(String),
    Host(std::io::Error),
    Run(std::result::Result<process_io::Output, RunError>),
    Spawn(std::io::Result<Child>),
    Observed {
        status: std::io::Result<ExitStatus>,
        terminate: bool,
    },
}
pub(crate) fn is_operation(name: &str) -> bool {
    matches!(
        name,
        "Process::run" | "Process::spawn" | "Process::wait" | "Process::terminate"
    )
}
pub(crate) fn prepare(runtime: &mut Runtime, name: &str, args: &[Handle]) -> Result<Request> {
    if matches!(name, "Process::wait" | "Process::terminate") {
        let first = *args
            .first()
            .ok_or_else(|| RuntimeError::internal("missing child authority"))?;
        let Object::Child(id) = runtime.heap.get(first)? else {
            return Err(RuntimeError::internal("expected child authority"));
        };
        let child = runtime
            .children
            .get(*id as usize)
            .ok_or_else(|| RuntimeError::internal("invalid child authority"))?
            .clone();
        return Ok(Request {
            operation: Operation::Await {
                child,
                terminate: name == "Process::terminate",
            },
            cancellation: runtime.host_cancellation(),
        });
    }
    let limit = match name {
        "Process::run" => Some(
            usize::try_from(match args.get(1) {
                Some(&limit) => runtime.as_integer(limit)?,
                None => 16_777_216,
            })
            .map_err(|_| RuntimeError::panic("negative process capture limit"))?,
        ),
        "Process::spawn" => None,
        _ => return Err(RuntimeError::internal("invalid host process operation")),
    };
    let command = *args
        .first()
        .ok_or_else(|| RuntimeError::internal("missing process command"))?;
    Ok(Request {
        operation: Operation::Launch {
            prepared: Box::new(runtime.process_prepare(command, limit.is_none())?),
            limit,
        },
        cancellation: runtime.host_cancellation(),
    })
}
impl Request {
    pub(crate) fn with_cancellation(mut self, cancellation: Arc<Cancellation>) -> Self {
        self.cancellation = cancellation;
        self
    }
    pub(crate) fn perform(self) -> Result<Reply> {
        if self.cancellation.requested() {
            return Err(RuntimeError::cancelled());
        }
        let Operation::Launch { prepared, limit } = self.operation else {
            let Operation::Await { child, terminate } = self.operation else {
                unreachable!()
            };
            let mut child = child.lock().unwrap_or_else(|error| error.into_inner());
            let status = if let Some(status) = child.observed {
                Ok(status)
            } else if terminate {
                process_io::terminate_reap(&mut child.child)
            } else {
                loop {
                    if self.cancellation.requested() {
                        return Err(RuntimeError::cancelled());
                    }
                    match child.child.try_wait() {
                        Ok(Some(status)) => break Ok(status),
                        Ok(None) => {
                            if !self.cancellation.sleep(std::time::Duration::from_millis(5)) {
                                return Err(RuntimeError::cancelled());
                            }
                        }
                        Err(error) => break Err(error),
                    }
                }
            };
            if let Ok(status) = status {
                child.observed = Some(status);
            }
            drop(child);
            return Ok(Reply::Observed { status, terminate });
        };
        let Prepared { mut command, input } = match *prepared {
            Ok(prepared) => prepared,
            Err(PrepareError::Invalid(message)) => return Ok(Reply::Invalid(message)),
            Err(PrepareError::Host(error)) => return Ok(Reply::Host(error)),
        };
        if let Some(limit) = limit {
            return Ok(Reply::Run(process_io::run(
                command,
                input,
                limit,
                self.cancellation,
            )));
        }
        let child = command.spawn();
        if self.cancellation.requested() {
            if let Ok(mut child) = child {
                process_io::terminate_reap(&mut child).map_err(|error| {
                    RuntimeError::internal(format!(
                        "cancelled spawn could not reap its child: {error}"
                    ))
                })?;
            }
            return Err(RuntimeError::cancelled());
        }
        Ok(Reply::Spawn(child))
    }
}
pub(crate) fn finish(runtime: &mut Runtime, reply: Reply) -> Result<Handle> {
    match reply {
        Reply::Invalid(message) => runtime.invalid_command(message),
        Reply::Host(error) | Reply::Spawn(Err(error)) => {
            runtime.process_host_error("StartFailed", error)
        }
        Reply::Spawn(Ok(child)) => {
            let id = runtime.children.len() as u64;
            runtime.children.push(Arc::new(Mutex::new(ChildState {
                child,
                observed: None,
            })));
            let child = runtime.allocate(Object::Child(id))?;
            runtime.variant("Ok", vec![child])
        }
        Reply::Observed {
            status: Ok(status),
            terminate,
        } => {
            let value = if terminate {
                runtime.unit()?
            } else {
                runtime.process_status(status)?
            };
            runtime.variant("Ok", vec![value])
        }
        Reply::Observed {
            status: Err(error), ..
        } => runtime.process_host_error("WaitFailed", error),
        Reply::Run(Ok(output)) => {
            let status = runtime.process_status(output.status)?;
            let stdout = runtime.allocate(Object::Bytes(output.stdout.into()))?;
            let stderr = runtime.allocate(Object::Bytes(output.stderr.into()))?;
            let output = runtime.allocate(Object::Record(
                [
                    ("status".into(), status),
                    ("stdout".into(), stdout),
                    ("stderr".into(), stderr),
                ]
                .into(),
            ))?;
            runtime.variant("Ok", vec![output])
        }
        Reply::Run(Err(error)) => match error {
            RunError::Start(error) => runtime.process_host_error("StartFailed", error),
            RunError::Wait(error) => runtime.process_host_error("WaitFailed", error),
            RunError::Transfer(error) => runtime.process_host_error("TransferFailed", error),
            RunError::CaptureLimit => runtime.process_error("CaptureLimit", None),
            RunError::WorkerPanic => Err(RuntimeError::internal(
                "unexpected Rust panic in process transfer worker",
            )),
            RunError::Cancelled => Err(RuntimeError::cancelled()),
        },
    }
}

/// Cancellation can arrive after spawn's last host check and before managed
/// publication. Dropping std::process::Child alone would leave it running.
pub(crate) fn discard(reply: Reply) -> Result<()> {
    if let Reply::Spawn(Ok(mut child)) = reply {
        process_io::terminate_reap(&mut child).map_err(|error| {
            RuntimeError::internal(format!(
                "unpublished spawn could not reap its child: {error}"
            ))
        })?;
    }
    Ok(())
}
