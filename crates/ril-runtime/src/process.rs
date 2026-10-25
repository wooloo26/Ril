//! Explicit-path process invocation and task-local child authority. Child IO uses
//! separate cancellable workers; no shell or PATH resolution is implicit.
use crate::{
    environment::valid_environment_name,
    heap::{Handle, Object},
    native_string::NativeString,
    process_io::{self, RunError},
    value::{Result, Runtime, RuntimeError},
};
pub(crate) mod host;
#[cfg(test)]
pub(crate) mod tests;
use std::{
    ffi::OsString,
    path::PathBuf,
    process::{Child, Command, ExitStatus, Stdio},
};

#[derive(Debug)]
pub(crate) struct ChildState {
    child: Child,
    observed: Option<ExitStatus>,
}
pub(crate) fn release_host(state: &std::sync::Arc<std::sync::Mutex<ChildState>>) -> Result<()> {
    let mut state = state.lock().unwrap_or_else(|error| error.into_inner());
    if state.observed.is_some() {
        return Ok(());
    }
    match process_io::terminate_reap(&mut state.child) {
        Ok(status) => state.observed = Some(status),
        Err(error) => {
            if let Ok(Some(status)) = state.child.try_wait() {
                state.observed = Some(status);
            } else {
                return Err(RuntimeError::internal(format!(
                    "owning child cleanup could not reap the child: {error}"
                )));
            }
        }
    }
    Ok(())
}
struct Prepared {
    command: Command,
    input: Option<Vec<u8>>,
}
enum PrepareError {
    Invalid(String),
    Host(std::io::Error),
}
impl From<String> for PrepareError {
    fn from(message: String) -> Self {
        Self::Invalid(message)
    }
}
impl From<&str> for PrepareError {
    fn from(message: &str) -> Self {
        Self::Invalid(message.into())
    }
}
fn native_argument(value: NativeString) -> std::result::Result<OsString, &'static str> {
    if value.contains_nul() {
        return Err("native argument contains NUL");
    }
    value.to_os()
}
impl Runtime {
    /// Internal owning wrapper cleanup. Source Child has no scoped/on_close
    /// contract; only verified with_child lowering can register this authority.
    #[cfg(test)]
    pub(crate) fn release_child(&mut self, handle: Handle) -> Result<bool> {
        let Object::Child(id) = self.heap.get(handle)? else {
            return Ok(false);
        };
        let state = self
            .children
            .get(*id as usize)
            .ok_or_else(|| RuntimeError::internal("invalid child authority"))?;
        release_host(state)?;
        Ok(true)
    }
    fn process_error(&mut self, kind: &str, payload: Option<Handle>) -> Result<Handle> {
        let error = self.variant(
            &format!("Process::ProcessError::{kind}"),
            payload.into_iter().collect(),
        )?;
        self.variant("Err", vec![error])
    }
    fn invalid_command(&mut self, message: impl Into<String>) -> Result<Handle> {
        let message = self.string(message.into())?;
        self.process_error("InvalidCommand", Some(message))
    }
    fn process_host_error(&mut self, kind: &str, error: std::io::Error) -> Result<Handle> {
        let error = self.io_host_error(error)?;
        self.process_error(kind, Some(error))
    }
    fn optional_value(&self, value: Handle) -> Result<Option<Handle>> {
        match self.heap.get(value)? {
            Object::Variant { tag, fields } if tag == "None" && fields.is_empty() => Ok(None),
            Object::Variant { tag, fields } if tag == "Some" && fields.len() == 1 => {
                Ok(Some(fields[0]))
            }
            _ => Err(RuntimeError::internal("invalid optional process field")),
        }
    }
    fn process_prepare(
        &mut self,
        value: Handle,
        spawn: bool,
    ) -> Result<std::result::Result<Prepared, PrepareError>> {
        let program = self.field(value, "program")?;
        let program = self.as_path(program)?;
        let program = match native_argument(program) {
            Ok(value) if !value.is_empty() => PathBuf::from(value),
            _ => return Ok(Err("invalid program path".into())),
        };
        let arguments = self.field(value, "args")?;
        let arguments = self
            .sequence(arguments)?
            .into_iter()
            .map(|argument| native_argument(self.as_native(argument)?).map_err(RuntimeError::panic))
            .collect::<Result<Vec<_>>>();
        let arguments = match arguments {
            Ok(value) => value,
            Err(error) if error.tag == ril_runtime_api::abi::OutcomeTag::LanguagePanic => {
                return Ok(Err(error.message.into()));
            }
            Err(error) => return Err(error),
        };
        let cwd = self.field(value, "cwd")?;
        let cwd = self
            .optional_value(cwd)?
            .map(|cwd| self.as_path(cwd))
            .transpose()?;
        let cwd = match cwd.map(native_argument).transpose() {
            Ok(value) => value.map(PathBuf::from),
            Err(error) => return Ok(Err(error.into())),
        };
        let environment = self.field(value, "env")?;
        let environment = self
            .optional_value(environment)?
            .map(|env| self.sequence(env))
            .transpose()?;
        let environment = if let Some(environment) = environment {
            let mut entries: Vec<(NativeString, OsString, OsString)> =
                Vec::with_capacity(environment.len());
            for pair in environment {
                let pair = self.sequence(pair)?;
                if pair.len() != 2 {
                    return Err(RuntimeError::internal("invalid process environment pair"));
                }
                let name = self.as_native(pair[0])?;
                if !valid_environment_name(&name) {
                    return Ok(Err("invalid environment name".into()));
                }
                let native_name = match native_argument(name.clone()) {
                    Ok(value) => value,
                    Err(error) => return Ok(Err(error.into())),
                };
                let native_value = match native_argument(self.as_native(pair[1])?) {
                    Ok(value) => value,
                    Err(error) => return Ok(Err(error.into())),
                };
                let duplicate = entries.iter().any(|(previous, _, _)| {
                    #[cfg(windows)]
                    {
                        crate::platform_environment::compare_environment_names(
                            &previous.units(),
                            &name.units(),
                        )
                        .is_eq()
                    }
                    #[cfg(unix)]
                    {
                        previous == &name
                    }
                });
                if duplicate {
                    return Ok(Err("duplicate effective environment name".into()));
                }
                entries.push((name, native_name, native_value));
            }
            Some(entries)
        } else {
            None
        };
        let input = self.field(value, "input")?;
        let (stdin, input) = match self.heap.get(input)?.clone() {
            Object::Variant { tag, fields }
                if tag == "Process::Input::Inherit" && fields.is_empty() =>
            {
                (Stdio::inherit(), None)
            }
            Object::Variant { tag, fields }
                if tag == "Process::Input::Null" && fields.is_empty() =>
            {
                (Stdio::null(), None)
            }
            Object::Variant { tag, fields }
                if tag == "Process::Input::Data" && fields.len() == 1 && !spawn =>
            {
                (Stdio::piped(), Some(self.as_bytes(fields[0])?.to_vec()))
            }
            Object::Variant { tag, .. } if spawn && tag == "Process::Input::Data" => {
                return Ok(Err("spawn does not admit Data input".into()));
            }
            _ => return Err(RuntimeError::internal("invalid process input mode")),
        };
        let mut streams = Vec::new();
        for field in ["stdout", "stderr"] {
            let value = self.field(value, field)?;
            let stream = match self.heap.get(value)? {
                Object::Variant { tag, fields }
                    if tag == "Process::OutputMode::Inherit" && fields.is_empty() =>
                {
                    Stdio::inherit()
                }
                Object::Variant { tag, fields }
                    if tag == "Process::OutputMode::Null" && fields.is_empty() =>
                {
                    Stdio::null()
                }
                Object::Variant { tag, fields }
                    if tag == "Process::OutputMode::Capture" && fields.is_empty() && !spawn =>
                {
                    Stdio::piped()
                }
                Object::Variant { tag, .. } if spawn && tag == "Process::OutputMode::Capture" => {
                    return Ok(Err("spawn does not admit captured output".into()));
                }
                _ => return Err(RuntimeError::internal("invalid process output mode")),
            };
            streams.push(stream);
        }
        // Both paths resolve against one caller-directory observation before any
        // child cwd override. An absolute program prevents implicit PATH search.
        let caller =
            if !program.is_absolute() || cwd.as_ref().is_some_and(|path| !path.is_absolute()) {
                match std::env::current_dir() {
                    Ok(path) => path,
                    Err(error) => return Ok(Err(PrepareError::Host(error))),
                }
            } else {
                PathBuf::new()
            };
        let mut command = Command::new(if program.is_absolute() {
            program
        } else {
            caller.join(program)
        });
        #[cfg(windows)]
        {
            use std::os::windows::process::CommandExt;
            // raw_arg adds precisely STD's encoder to the platform-generated
            // executable element; the latter is always a resolved path.
            for argument in arguments {
                use std::os::windows::ffi::{OsStrExt, OsStringExt};
                let quoted = crate::environment::quote_windows_argument(
                    &argument.encode_wide().collect::<Vec<_>>(),
                );
                command.raw_arg(OsString::from_wide(&quoted));
            }
            // No visible console is requested for native runtime subprocesses.
            command.creation_flags(0x0800_0000);
        }
        #[cfg(unix)]
        command.args(arguments);
        if let Some(cwd) = cwd {
            command.current_dir(if cwd.is_absolute() {
                cwd
            } else {
                caller.join(cwd)
            });
        }
        if let Some(environment) = environment {
            command.env_clear();
            command.envs(
                environment
                    .into_iter()
                    .map(|(_, name, value)| (name, value)),
            );
        }
        command
            .stdin(stdin)
            .stdout(streams.remove(0))
            .stderr(streams.remove(0));
        Ok(Ok(Prepared { command, input }))
    }
    fn process_status(&mut self, status: ExitStatus) -> Result<Handle> {
        if let Some(code) = status.code() {
            let code = self.integer(i128::from(code as u32), 32, false)?;
            self.variant("Process::ExitStatus::Exited", vec![code])
        } else {
            #[cfg(unix)]
            {
                use std::os::unix::process::ExitStatusExt;
                if let Some(signal) = status.signal() {
                    let signal = self.int(i128::from(signal))?;
                    return self.variant("Process::ExitStatus::Signaled", vec![signal]);
                }
            }
            Err(RuntimeError::internal(
                "unrepresentable observed child status",
            ))
        }
    }
    pub(crate) fn process_builtin(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let arg = |index| {
            args.get(index)
                .copied()
                .ok_or_else(|| RuntimeError::internal("missing process argument"))
        };
        if matches!(
            name,
            "Process::Input::Data"
                | "Process::ExitStatus::Exited"
                | "Process::ExitStatus::Signaled"
        ) {
            return self.variant(name, vec![arg(0)?]);
        }
        match name {
            "Process::run" | "Process::spawn" => {
                let request = host::prepare(self, name, args)?;
                host::finish(self, request.perform()?)
            }
            "Process::wait" | "Process::terminate" => {
                let request = host::prepare(self, name, args)?;
                host::finish(self, request.perform()?)
            }
            _ => Err(RuntimeError::internal(
                "process callback operation needs a verified native bridge",
            )),
        }
    }
}
