//! Stream requests carry task-local host authority and immutable bytes only.
//! Native dispatch performs IO without retaining the shared managed-heap gate.
use super::*;
use crate::byte_string::Bytes;

#[cfg(test)]
#[path = "host_tests.rs"]
mod tests;

pub(crate) struct Request {
    file: Arc<Mutex<FileState>>,
    operation: Operation,
    cancellation: Arc<crate::process_io::Cancellation>,
}
enum Operation {
    Read(usize),
    Write(Bytes),
    Seek(std::io::Result<SeekFrom>),
    Sync,
    Close,
}
pub(crate) enum Reply {
    Invalid {
        kind: &'static str,
        message: &'static str,
        write: bool,
    },
    Read(std::io::Result<(Vec<u8>, bool)>),
    Write(std::io::Result<usize>),
    Seek(std::io::Result<u64>),
    Unit(std::io::Result<()>),
}
pub(crate) fn is_operation(name: &str) -> bool {
    matches!(
        name,
        "File::read_chunk" | "File::write" | "File::seek" | "File::sync" | "File::close"
    )
}
pub(crate) fn prepare(runtime: &Runtime, name: &str, args: &[Handle]) -> Result<Request> {
    let arg = |index: usize| {
        args.get(index)
            .copied()
            .ok_or_else(|| RuntimeError::internal("missing file stream argument"))
    };
    let operation = match name {
        "File::read_chunk" => Operation::Read(
            usize::try_from(runtime.as_integer(arg(1)?)?)
                .map_err(|_| RuntimeError::panic("negative read count"))?,
        ),
        "File::write" => {
            let Object::Bytes(data) = runtime.heap.get(arg(1)?)? else {
                return Err(RuntimeError::internal("expected file write bytes"));
            };
            Operation::Write(data.clone())
        }
        "File::seek" => {
            let Object::Variant { tag, fields } = runtime.heap.get(arg(1)?)? else {
                return Err(RuntimeError::internal("expected seek position"));
            };
            if fields.len() != 1 {
                return Err(RuntimeError::internal("invalid seek position payload"));
            }
            let offset = i64::try_from(runtime.as_integer(fields[0])?)
                .map_err(|_| RuntimeError::internal("invalid seek offset"))?;
            Operation::Seek(match tag.rsplit("::").next() {
                Some("Start") => u64::try_from(offset).map(SeekFrom::Start).map_err(|_| {
                    std::io::Error::new(std::io::ErrorKind::InvalidInput, "negative seek position")
                }),
                Some("Current") => Ok(SeekFrom::Current(offset)),
                Some("End") => Ok(SeekFrom::End(offset)),
                _ => return Err(RuntimeError::internal("invalid seek position tag")),
            })
        }
        "File::sync" => Operation::Sync,
        "File::close" => Operation::Close,
        _ => return Err(RuntimeError::internal("invalid file stream operation")),
    };
    Ok(Request {
        file: runtime.file_state(arg(0)?)?,
        operation,
        cancellation: runtime.host_cancellation(),
    })
}
impl Request {
    pub(crate) fn with_cancellation(
        mut self,
        cancellation: Arc<crate::process_io::Cancellation>,
    ) -> Self {
        self.cancellation = cancellation;
        self
    }
    pub(crate) fn perform(self) -> Result<Reply> {
        crate::host_transfer::run(self.cancellation.clone(), move || self.perform_in_worker())
    }
    fn perform_in_worker(self) -> Result<Reply> {
        let mut state = self.file.lock().unwrap_or_else(|error| error.into_inner());
        if self.cancellation.requested() {
            return Err(RuntimeError::cancelled());
        }
        if matches!(self.operation, Operation::Close) {
            // All aliases observe closure before the host can report an error.
            let file = state.file.take();
            drop(state);
            return Ok(Reply::Unit(
                file.map_or(Ok(()), crate::platform_file::close),
            ));
        }
        let invalid = if state.file.is_none() {
            Some(("Closed", "file is closed"))
        } else if matches!(self.operation, Operation::Read(_)) && !state.readable
            || matches!(self.operation, Operation::Write(_)) && !state.writable
        {
            Some(("InvalidInput", "operation is not supported by open mode"))
        } else {
            None
        };
        if let Some((kind, message)) = invalid {
            return Ok(Reply::Invalid {
                kind,
                message,
                write: matches!(self.operation, Operation::Write(_)),
            });
        }
        let file = state
            .file
            .as_mut()
            .ok_or_else(|| RuntimeError::internal("lost file authority"))?;
        Ok(match self.operation {
            Operation::Read(count) => {
                let mut data = Vec::new();
                data.try_reserve_exact(count)
                    .map_err(|_| RuntimeError::panic("read allocation failed"))?;
                data.resize(count, 0);
                let result = if count == 0 {
                    Ok(0)
                } else {
                    let _mode = match crate::platform_io::FileMode::nonblocking(file) {
                        Ok(mode) => mode,
                        Err(error) => return Ok(Reply::Read(Err(error))),
                    };
                    let mut file = &*file;
                    loop {
                        if self.cancellation.requested() {
                            return Err(RuntimeError::cancelled());
                        }
                        match file.read(&mut data) {
                            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {
                                continue;
                            }
                            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                                if !self.cancellation.sleep(std::time::Duration::from_millis(5)) {
                                    return Err(RuntimeError::cancelled());
                                }
                            }
                            result => break result,
                        }
                    }
                };
                Reply::Read(result.map(|read| {
                    data.truncate(read);
                    (data, count != 0 && read == 0)
                }))
            }
            Operation::Write(data) => {
                let result = if data.is_empty() {
                    Ok(0)
                } else {
                    let _mode = match crate::platform_io::FileMode::nonblocking(file) {
                        Ok(mode) => mode,
                        Err(error) => return Ok(Reply::Write(Err(error))),
                    };
                    let mut file = &*file;
                    loop {
                        if self.cancellation.requested() {
                            return Err(RuntimeError::cancelled());
                        }
                        #[cfg(target_os = "linux")]
                        let result = crate::platform_signal::write(|| file.write(&data));
                        #[cfg(not(target_os = "linux"))]
                        let result = file.write(&data);
                        match result {
                            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {
                                continue;
                            }
                            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                                if !self.cancellation.sleep(std::time::Duration::from_millis(5)) {
                                    return Err(RuntimeError::cancelled());
                                }
                            }
                            Ok(0) => {
                                break Err(std::io::Error::new(
                                    std::io::ErrorKind::WriteZero,
                                    "nonempty file write made no progress",
                                ));
                            }
                            result => break result,
                        }
                    }
                };
                Reply::Write(result)
            }
            Operation::Seek(position) => {
                Reply::Seek(position.and_then(|position| file.seek(position)))
            }
            Operation::Sync => Reply::Unit(file.sync_all()),
            Operation::Close => unreachable!(),
        })
    }
}
pub(crate) fn finish(runtime: &mut Runtime, reply: Reply) -> Result<Handle> {
    match reply {
        Reply::Invalid {
            kind,
            message,
            write,
        } => {
            if write {
                let error = runtime.io_error(kind, message, None)?;
                runtime.write_progress(0, Some(error))
            } else {
                runtime.io_failure(kind, message)
            }
        }
        Reply::Read(Ok((data, end))) => {
            let chunk = runtime.read_chunk_value(data, end)?;
            runtime.variant("Ok", vec![chunk])
        }
        Reply::Read(Err(error)) | Reply::Seek(Err(error)) => runtime.io_result(Err(error)),
        Reply::Write(Ok(count)) => runtime.write_progress(count, None),
        Reply::Write(Err(error)) => {
            let error = runtime.io_host_error(error)?;
            runtime.write_progress(0, Some(error))
        }
        Reply::Seek(Ok(position)) => {
            let position = runtime.integer(i128::from(position), 64, false)?;
            runtime.variant("Ok", vec![position])
        }
        Reply::Unit(result) => runtime.io_unit_result(result),
    }
}
