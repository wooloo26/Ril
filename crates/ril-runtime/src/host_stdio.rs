//! Managed arguments and replies cross short heap access sections. The host
//! transfer itself owns only byte storage/counts and holds no managed borrow.
use crate::process_io::Cancellation;
use crate::{
    byte_string::Bytes,
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};
use std::{io, sync::Arc, time::Duration};
#[cfg(all(test, target_os = "linux"))]
#[path = "host_stdio_tests.rs"]
mod tests;
pub(crate) struct Request {
    operation: Operation,
    cancellation: Arc<Cancellation>,
    print: bool,
}
enum Operation {
    Read(usize),
    Write {
        data: Bytes,
        stderr: bool,
        all: bool,
    },
}
pub(crate) enum Reply {
    Read(io::Result<(Vec<u8>, bool)>),
    Progress {
        written: usize,
        error: Option<io::Error>,
    },
    Unit(io::Result<()>),
    Printed(io::Result<()>),
}
pub(crate) fn is_operation(name: &str) -> bool {
    matches!(
        name,
        "Io::stdin_read"
            | "Io::stdout_write"
            | "Io::stderr_write"
            | "Io::write_stdout"
            | "Io::write_stderr"
            | "print"
            | "println"
    )
}
pub(crate) fn prepare(runtime: &Runtime, name: &str, args: &[Handle]) -> Result<Request> {
    let first = *args
        .first()
        .ok_or_else(|| RuntimeError::internal("missing host stream argument"))?;
    let operation = match name {
        "Io::stdin_read" => Operation::Read(
            usize::try_from(runtime.as_integer(first)?)
                .map_err(|_| RuntimeError::panic("negative read count"))?,
        ),
        "Io::stdout_write" | "Io::stderr_write" => {
            let Object::Bytes(data) = runtime.heap.get(first)? else {
                return Err(RuntimeError::internal("invalid byte stream input"));
            };
            Operation::Write {
                data: data.clone(),
                stderr: name == "Io::stderr_write",
                all: false,
            }
        }
        "Io::write_stdout" | "Io::write_stderr" => Operation::Write {
            data: runtime.as_string(first)?.as_bytes().to_vec().into(),
            stderr: name == "Io::write_stderr",
            all: true,
        },
        "print" | "println" => {
            let mut text = runtime.format(first)?;
            if name == "println" {
                text.push('\n');
            }
            Operation::Write {
                data: text.into_bytes().into(),
                stderr: false,
                all: true,
            }
        }
        _ => return Err(RuntimeError::internal("invalid host stream operation")),
    };
    Ok(Request {
        operation,
        cancellation: runtime.host_cancellation(),
        print: matches!(name, "print" | "println"),
    })
}
impl Request {
    pub(crate) fn with_cancellation(mut self, cancellation: Arc<Cancellation>) -> Self {
        self.cancellation = cancellation;
        self
    }
    pub(crate) fn perform(self) -> Result<Reply> {
        let print = self.print;
        let reply = crate::host_transfer::run(self.cancellation.clone(), move || self.transfer())?;
        Ok(match reply {
            Reply::Unit(result) if print => Reply::Printed(result),
            reply => reply,
        })
    }
    fn transfer(self) -> Result<Reply> {
        let stream = match self.operation {
            Operation::Read(_) => 0,
            Operation::Write { stderr: false, .. } => 1,
            Operation::Write { stderr: true, .. } => 2,
        };
        let mode = crate::platform_stdio::Mode::nonblocking(stream);
        // Failure to acquire a host descriptor is an IO result, not a runtime
        // fault. Preserve the primitive's own structured error shape.
        let _mode = match mode {
            Ok(mode) => mode,
            Err(error) => {
                return Ok(match self.operation {
                    Operation::Read(_) => Reply::Read(Err(error)),
                    Operation::Write { all: true, .. } => Reply::Unit(Err(error)),
                    Operation::Write { all: false, .. } => Reply::Progress {
                        written: 0,
                        error: Some(error),
                    },
                });
            }
        };
        Ok(match self.operation {
            Operation::Read(maximum) => {
                let mut data = Vec::new();
                data.try_reserve_exact(maximum)
                    .map_err(|_| RuntimeError::panic("read allocation failed"))?;
                data.resize(maximum, 0);
                let result = retry(&self.cancellation, || {
                    crate::platform_stdio::read(&mut data)
                })?;
                Reply::Read(result.map(|transferred| {
                    data.truncate(transferred);
                    (data, maximum > 0 && transferred == 0)
                }))
            }
            Operation::Write {
                data,
                stderr,
                all: true,
            } => {
                let mut offset = 0;
                let result = loop {
                    match retry(&self.cancellation, || {
                        crate::platform_stdio::write(&data[offset..], stderr)
                    })? {
                        Ok(count) if offset + count == data.len() => break Ok(()),
                        Ok(0) => break Err(io::Error::from(io::ErrorKind::WriteZero)),
                        Ok(count) => offset += count,
                        Err(error) => break Err(error),
                    }
                };
                Reply::Unit(result)
            }
            Operation::Write {
                data,
                stderr,
                all: false,
            } => {
                let result = retry(&self.cancellation, || {
                    crate::platform_stdio::write(&data, stderr)
                })?;
                match result {
                    Ok(0) if !data.is_empty() => Reply::Progress {
                        written: 0,
                        error: Some(io::Error::new(
                            io::ErrorKind::WriteZero,
                            "stream write made no progress",
                        )),
                    },
                    Ok(written) => Reply::Progress {
                        written,
                        error: None,
                    },
                    Err(error) => Reply::Progress {
                        written: 0,
                        error: Some(error),
                    },
                }
            }
        })
    }
}
fn retry<T>(
    cancellation: &Cancellation,
    mut transfer: impl FnMut() -> io::Result<T>,
) -> Result<io::Result<T>> {
    loop {
        if cancellation.requested() {
            return Err(RuntimeError::cancelled());
        }
        match transfer() {
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                if !cancellation.sleep(Duration::from_millis(5)) {
                    return Err(RuntimeError::cancelled());
                }
            }
            result => return Ok(result),
        }
    }
}
pub(crate) fn finish(runtime: &mut Runtime, reply: Reply) -> Result<Handle> {
    match reply {
        Reply::Read(Ok((data, end))) => {
            let chunk = runtime.read_chunk_value(data, end)?;
            runtime.variant("Ok", vec![chunk])
        }
        Reply::Read(Err(error)) => runtime.io_result(Err(error)),
        Reply::Progress { written, error } => {
            let error = error
                .map(|error| runtime.io_host_error(error))
                .transpose()?;
            runtime.write_progress(written, error)
        }
        Reply::Unit(result) => runtime.io_unit_result(result),
        Reply::Printed(result) => {
            result.map_err(|error| RuntimeError::panic(error.to_string()))?;
            runtime.unit()
        }
    }
}
