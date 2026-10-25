//! Portable IO records. A host error remains a language Result, never EOF.
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
        Err(RuntimeError::internal("unknown host stdio operation"))
    }
}
