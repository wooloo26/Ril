//! Portable IO records. A host error remains a language Result, never EOF.
#[cfg(test)]
#[path = "io_tests.rs"]
mod tests;
use crate::{
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};

pub(crate) fn error_kind(error: &std::io::Error) -> &'static str {
    use std::io::ErrorKind;
    match error.kind() {
        ErrorKind::NotFound => "NotFound",
        ErrorKind::PermissionDenied => "PermissionDenied",
        ErrorKind::AlreadyExists => "AlreadyExists",
        ErrorKind::InvalidInput => "InvalidInput",
        ErrorKind::InvalidData => "InvalidData",
        ErrorKind::UnexpectedEof => "UnexpectedEnd",
        ErrorKind::BrokenPipe => "BrokenPipe",
        ErrorKind::Unsupported | ErrorKind::CrossesDevices => "Unsupported",
        _ if (cfg!(windows) && error.raw_os_error() == Some(6))
            || (cfg!(target_os = "linux") && error.raw_os_error() == Some(9)) =>
        {
            "Closed"
        }
        _ if cfg!(windows) && matches!(error.raw_os_error(), Some(87 | 123 | 206)) => {
            "InvalidInput"
        }
        _ => "Other",
    }
}
impl Runtime {
    pub(crate) fn validate_read(&self, result: Handle, maximum: Handle) -> Result<()> {
        let maximum = self.as_integer(maximum)?;
        if maximum < 0 {
            return Err(RuntimeError::panic("negative read count"));
        }
        let Object::Variant { tag, fields } = self.heap.get(result)? else {
            return Err(RuntimeError::internal(
                "stream read did not return a certified Result",
            ));
        };
        if fields.len() != 1 {
            return Err(RuntimeError::internal("invalid stream Result payload"));
        }
        if tag == "Err" {
            return Ok(());
        }
        if tag != "Ok" {
            return Err(RuntimeError::internal("invalid stream Result tag"));
        }
        let Object::Record(chunk) = self.heap.get(fields[0])? else {
            return Err(RuntimeError::internal("invalid ReadChunk"));
        };
        let data = *chunk
            .get("data")
            .ok_or_else(|| RuntimeError::internal("missing ReadChunk data"))?;
        let end = *chunk
            .get("end")
            .ok_or_else(|| RuntimeError::internal("missing ReadChunk end"))?;
        let count = self.as_bytes(data)?.len() as i128;
        let Object::Bool(end) = self.heap.get(end)? else {
            return Err(RuntimeError::internal("invalid ReadChunk end flag"));
        };
        let end = *end;
        if count > maximum {
            return Err(RuntimeError::panic("read exceeds requested count"));
        }
        if maximum == 0 && (count != 0 || end) {
            return Err(RuntimeError::panic("invalid zero-request read"));
        }
        if maximum > 0 && count == 0 && !end {
            return Err(RuntimeError::panic("empty read without eof"));
        }
        Ok(())
    }
    pub(crate) fn validate_write(&self, progress: Handle, data: Handle) -> Result<()> {
        let Object::Record(progress) = self.heap.get(progress)? else {
            return Err(RuntimeError::internal("invalid WriteProgress"));
        };
        let count = *progress
            .get("written")
            .ok_or_else(|| RuntimeError::internal("missing WriteProgress count"))?;
        let error = *progress
            .get("error")
            .ok_or_else(|| RuntimeError::internal("missing WriteProgress error"))?;
        let count = self.as_integer(count)?;
        let maximum = self.as_bytes(data)?.len() as i128;
        let no_error = match self.heap.get(error)? {
            Object::Variant { tag, fields } if tag == "None" && fields.is_empty() => true,
            Object::Variant { tag, fields } if tag == "Some" && fields.len() == 1 => false,
            _ => return Err(RuntimeError::internal("invalid WriteProgress error option")),
        };
        if count < 0 {
            return Err(RuntimeError::panic("negative progress"));
        }
        if count > maximum {
            return Err(RuntimeError::panic("excess progress"));
        }
        if maximum > 0 && count == 0 && no_error {
            return Err(RuntimeError::panic("no progress"));
        }
        Ok(())
    }
    pub(crate) fn io_error(
        &mut self,
        kind: &str,
        message: impl Into<String>,
        code: Option<i32>,
    ) -> Result<Handle> {
        let kind = self.variant(&format!("Io::ErrorKind::{kind}"), vec![])?;
        let message = self.string(message.into())?;
        let native_code = if let Some(code) = code {
            let code = self.integer(i128::from(code), 64, true)?;
            self.variant("Some", vec![code])?
        } else {
            self.variant("None", vec![])?
        };
        self.allocate(Object::Record(
            [
                ("kind".into(), kind),
                ("message".into(), message),
                ("native_code".into(), native_code),
            ]
            .into(),
        ))
    }
    pub(crate) fn io_host_error(&mut self, error: std::io::Error) -> Result<Handle> {
        self.io_error(error_kind(&error), error.to_string(), error.raw_os_error())
    }
    pub(crate) fn io_failure(&mut self, kind: &str, message: &str) -> Result<Handle> {
        let error = self.io_error(kind, message, None)?;
        self.variant("Err", vec![error])
    }
    pub(crate) fn io_result(&mut self, result: std::io::Result<Handle>) -> Result<Handle> {
        match result {
            Ok(value) => self.variant("Ok", vec![value]),
            Err(error) => {
                let error = self.io_host_error(error)?;
                self.variant("Err", vec![error])
            }
        }
    }
    pub(crate) fn io_unit_result(&mut self, result: std::io::Result<()>) -> Result<Handle> {
        let result = result.map(|()| Handle::INVALID);
        match result {
            Ok(_) => {
                let unit = self.unit()?;
                self.variant("Ok", vec![unit])
            }
            Err(error) => self.io_result(Err(error)),
        }
    }
    pub(crate) fn read_chunk_value(&mut self, data: Vec<u8>, end: bool) -> Result<Handle> {
        let data = self.allocate(Object::Bytes(data.into()))?;
        let end = self.boolean(end)?;
        self.allocate(Object::Record(
            [("data".into(), data), ("end".into(), end)].into(),
        ))
    }
    pub(crate) fn write_progress(
        &mut self,
        written: usize,
        error: Option<Handle>,
    ) -> Result<Handle> {
        let written = self.int(written as i128)?;
        let error = if let Some(error) = error {
            self.variant("Some", vec![error])?
        } else {
            self.variant("None", vec![])?
        };
        self.allocate(Object::Record(
            [("written".into(), written), ("error".into(), error)].into(),
        ))
    }
    pub(crate) fn io_builtin(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        if crate::host_stdio::is_operation(name) {
            let request = crate::host_stdio::prepare(self, name, args)?;
            let reply = request.perform()?;
            return crate::host_stdio::finish(self, reply);
        }
        let arg = |index| {
            args.get(index)
                .copied()
                .ok_or_else(|| RuntimeError::internal("missing IO argument"))
        };
        match name {
            "Io::read_position" => {
                let handle = self.allocate(Object::ReadPosition(Handle::INVALID))?;
                *self.heap.get_mut(handle)? = Object::ReadPosition(handle);
                Ok(handle)
            }
            "Io::guard_read" | "Io::guard_seek" => {
                let identity = self.read_position_identity(arg(0)?)?;
                self.guard_read_position(identity, name == "Io::guard_seek")?;
                self.unit()
            }
            "Io::read_buffer" | "Io::write_buffer" => {
                let capacity = usize::try_from(self.as_integer(arg(0)?)?)
                    .ok()
                    .filter(|&capacity| capacity > 0)
                    .ok_or_else(|| {
                        RuntimeError::panic(if name == "Io::read_buffer" {
                            "read buffer capacity"
                        } else {
                            "write buffer capacity"
                        })
                    })?;
                self.allocate(if name == "Io::read_buffer" {
                    Object::ReadBuffer(crate::io_buffered::ReadBuffer::new(capacity))
                } else {
                    Object::WriteBuffer(crate::io_buffered::WriteBuffer::new(capacity))
                })
            }
            "__io_read_validate" => {
                self.validate_read(arg(0)?, arg(1)?)?;
                Ok(arg(0)?)
            }
            "__io_write_validate" => {
                self.validate_write(arg(0)?, arg(1)?)?;
                Ok(arg(0)?)
            }
            "__io_acc_new" => self.allocate(Object::IoAccumulator(vec![])),
            "__io_acc_push" => {
                let Object::Bytes(data) = self.heap.get(arg(1)?)? else {
                    return Err(RuntimeError::internal("invalid stream accumulator input"));
                };
                let data = data.clone();
                let Object::IoAccumulator(output) = self.heap.get_mut(arg(0)?)? else {
                    return Err(RuntimeError::internal("invalid stream accumulator"));
                };
                output
                    .try_reserve(data.len())
                    .map_err(|_| RuntimeError::panic("stream allocation failed"))?;
                output.extend_from_slice(&data);
                self.unit()
            }
            "__io_acc_finish" => {
                let Object::IoAccumulator(output) = self.heap.get_mut(arg(0)?)? else {
                    return Err(RuntimeError::internal("invalid stream accumulator"));
                };
                let data = std::mem::take(output);
                self.allocate(Object::Bytes(data.into()))
            }
            "__io_bytes_suffix" => {
                let count = usize::try_from(self.as_integer(arg(1)?)?)
                    .map_err(|_| RuntimeError::internal("invalid certified stream suffix"))?;
                let Object::Bytes(data) = self.heap.get(arg(0)?)? else {
                    return Err(RuntimeError::internal("invalid stream suffix input"));
                };
                let data = data.slice(count..data.len()).ok_or_else(|| {
                    RuntimeError::internal("certified stream suffix exceeds input")
                })?;
                self.allocate(Object::Bytes(data))
            }
            "Io::error_text" => self.field(arg(0)?, "message"),
            _ => Err(RuntimeError::internal(
                "IO callback operation needs native invocation bridge",
            )),
        }
    }
}
