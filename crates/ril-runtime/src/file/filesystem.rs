//! Filesystem requests own host paths and bytes; no managed reference survives
//! preparation. Native dispatch releases the heap gate before `perform`.
use super::*;
#[cfg(test)]
#[path = "filesystem_tests.rs"]
mod tests;

pub(crate) struct Request {
    path: std::io::Result<PathBuf>,
    operation: Operation,
    cancellation: Arc<crate::process_io::Cancellation>,
}

enum Operation {
    Open(String),
    Metadata(bool),
    ReadDir,
    Unit(UnitOperation),
    Rename(std::io::Result<PathBuf>),
    Canonicalize,
    TempFile,
}

enum UnitOperation {
    CreateDir,
    CreateDirAll,
    RemoveFile,
    RemoveDir,
}

pub(crate) enum Reply {
    Open(std::io::Result<FileState>),
    Unit(std::io::Result<()>),
    Metadata(std::io::Result<fs::Metadata>),
    Entries(std::io::Result<Vec<(NativeString, &'static str)>>),
    Path(std::io::Result<PathBuf>),
    TempFile(std::io::Result<(File, PathBuf)>),
}

pub(crate) fn is_operation(name: &str) -> bool {
    matches!(
        name,
        "File::open_path"
            | "File::metadata"
            | "\0ril.host.file_read_dir"
            | "File::create_dir"
            | "File::create_dir_all"
            | "File::remove_file"
            | "File::remove_dir"
            | "File::rename"
            | "File::canonicalize"
            | "File::temp_file"
    )
}

pub(crate) fn prepare(runtime: &Runtime, name: &str, args: &[Handle]) -> Result<Request> {
    let arg = |index| {
        args.get(index)
            .copied()
            .ok_or_else(|| RuntimeError::internal("missing filesystem argument"))
    };
    let native = runtime.as_path(arg(0)?)?;
    let operation = match name {
        "File::open_path" => {
            let Object::Variant { tag, fields } = runtime.heap.get(arg(1)?)? else {
                return Err(RuntimeError::internal("expected file open mode"));
            };
            if !fields.is_empty() {
                return Err(RuntimeError::internal("invalid open mode payload"));
            }
            Operation::Open(tag.clone())
        }
        "File::metadata" => Operation::Metadata(
            args.get(1)
                .map(|&value| runtime.truth(value))
                .transpose()?
                .unwrap_or(true),
        ),
        "\0ril.host.file_read_dir" => Operation::ReadDir,
        "File::create_dir" => Operation::Unit(UnitOperation::CreateDir),
        "File::create_dir_all" => Operation::Unit(UnitOperation::CreateDirAll),
        "File::remove_file" => Operation::Unit(UnitOperation::RemoveFile),
        "File::remove_dir" => Operation::Unit(UnitOperation::RemoveDir),
        "File::rename" => Operation::Rename(native_path(runtime.as_path(arg(1)?)?)),
        "File::canonicalize" => Operation::Canonicalize,
        "File::temp_file" => Operation::TempFile,
        _ => return Err(RuntimeError::internal("invalid filesystem operation")),
    };
    Ok(Request {
        path: native_path(native),
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
        if self.cancellation.requested() {
            return Err(RuntimeError::cancelled());
        }
        let wait = match crate::platform_file::Wait::new() {
            Ok(wait) => wait,
            Err(error) => return Ok(self.failed(error)),
        };
        wait.run(self.cancellation.clone(), move || self.perform_in_worker())
    }
    fn failed(self, error: std::io::Error) -> Reply {
        match self.operation {
            Operation::Open(_) => Reply::Open(Err(error)),
            Operation::Metadata(_) => Reply::Metadata(Err(error)),
            Operation::ReadDir => Reply::Entries(Err(error)),
            Operation::Canonicalize => Reply::Path(Err(error)),
            Operation::TempFile => Reply::TempFile(Err(error)),
            _ => Reply::Unit(Err(error)),
        }
    }
    fn perform_in_worker(self) -> Result<Reply> {
        if self.cancellation.requested() {
            return Err(RuntimeError::cancelled());
        }
        let path = self.path;
        Ok(match self.operation {
            Operation::Open(mode) => {
                Reply::Open(path.and_then(|path| retry(&self.cancellation, || open(&path, &mode))))
            }
            Operation::Metadata(follow) => Reply::Metadata(path.and_then(|path| {
                if follow {
                    fs::metadata(path)
                } else {
                    fs::symlink_metadata(path)
                }
            })),
            Operation::ReadDir => Reply::Entries(path.and_then(|path| {
                let mut entries = Vec::new();
                for entry in fs::read_dir(path)? {
                    check(&self.cancellation)?;
                    let entry = entry?;
                    let ty = entry.file_type()?;
                    let kind = if ty.is_symlink() {
                        "Symlink"
                    } else if ty.is_file() {
                        "Regular"
                    } else if ty.is_dir() {
                        "Directory"
                    } else {
                        "Other"
                    };
                    entries.push((NativeString::from_os(&entry.file_name()), kind));
                }
                Ok(entries)
            })),
            Operation::Unit(operation) => Reply::Unit(path.and_then(|path| match operation {
                UnitOperation::CreateDir => fs::create_dir(path),
                UnitOperation::CreateDirAll => fs::create_dir_all(path),
                UnitOperation::RemoveFile => fs::remove_file(path),
                UnitOperation::RemoveDir => fs::remove_dir(path),
            })),
            Operation::Rename(destination) => Reply::Unit(path.and_then(|path| {
                destination
                    .and_then(|destination| crate::platform_file::rename(&path, &destination))
            })),
            Operation::Canonicalize => Reply::Path(path.and_then(fs::canonicalize)),
            Operation::TempFile => Reply::TempFile(path.and_then(|path| {
                tempfile::Builder::new()
                    .prefix("ril-")
                    .tempfile_in(path)
                    .and_then(|file| file.keep().map_err(|error| error.error))
            })),
        })
    }
}

fn check(cancellation: &crate::process_io::Cancellation) -> std::io::Result<()> {
    if cancellation.requested() {
        Err(std::io::Error::new(
            std::io::ErrorKind::Interrupted,
            "filesystem operation canceled",
        ))
    } else {
        Ok(())
    }
}
fn retry<T>(
    cancellation: &crate::process_io::Cancellation,
    mut operation: impl FnMut() -> std::io::Result<T>,
) -> std::io::Result<T> {
    loop {
        check(cancellation)?;
        match operation() {
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => check(cancellation)?,
            result => return result,
        }
    }
}
pub(crate) fn finish(runtime: &mut Runtime, reply: Reply) -> Result<Handle> {
    let value = match reply {
        Reply::Open(Ok(state)) => runtime.file_handle(state)?,
        Reply::Open(Err(error))
        | Reply::Metadata(Err(error))
        | Reply::Entries(Err(error))
        | Reply::Path(Err(error))
        | Reply::TempFile(Err(error)) => return runtime.io_result(Err(error)),
        Reply::Unit(result) => return runtime.io_unit_result(result),
        Reply::Metadata(Ok(metadata)) => runtime.file_metadata(metadata)?,
        Reply::Entries(Ok(entries)) => {
            let mut output = Vec::with_capacity(entries.len());
            for (entry_name, kind) in entries {
                let name = runtime.allocate(Object::NativeString(entry_name))?;
                let kind = runtime.variant(&format!("File::FileKind::{kind}"), vec![])?;
                output.push(runtime.allocate(Object::Tuple(vec![name, kind]))?);
            }
            runtime.allocate(Object::Array(output))?
        }
        Reply::Path(Ok(path)) => {
            runtime.allocate(Object::Path(NativeString::from_os(path.as_os_str())))?
        }
        Reply::TempFile(Ok((file, path))) => {
            let file = runtime.file_handle(FileState {
                file: Some(file),
                readable: true,
                writable: true,
            })?;
            let path = runtime.allocate(Object::Path(NativeString::from_os(path.as_os_str())))?;
            runtime.allocate(Object::Tuple(vec![path, file]))?
        }
    };
    runtime.variant("Ok", vec![value])
}
