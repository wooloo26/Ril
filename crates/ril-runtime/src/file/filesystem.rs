//! Filesystem requests own host paths and bytes; no managed reference survives
//! preparation. Native dispatch releases the heap gate before `perform`.
use super::*;
use crate::byte_string::Bytes;
#[cfg(test)]
#[path = "filesystem_tests.rs"]
mod tests;

pub(crate) struct Request {
    native: NativeString,
    path: std::io::Result<PathBuf>,
    operation: Operation,
    cancellation: Arc<crate::process_io::Cancellation>,
}

enum Operation {
    Open(String),
    Read(ReadKind),
    Write(Bytes),
    Metadata(bool),
    ReadDir,
    Unit(UnitOperation),
    Rename(std::io::Result<PathBuf>),
    Canonicalize,
    TempFile,
}

#[derive(Clone, Copy)]
pub(crate) enum ReadKind {
    LegacyText,
    Text,
    Bytes,
}

enum UnitOperation {
    CreateDir,
    CreateDirAll,
    RemoveFile,
    RemoveDir,
}

pub(crate) enum Reply {
    Open(std::io::Result<FileState>),
    Read(ReadKind, std::io::Result<Vec<u8>>),
    Unit(std::io::Result<()>),
    Metadata(std::io::Result<fs::Metadata>),
    Entries(
        NativeString,
        std::io::Result<Vec<(NativeString, &'static str)>>,
    ),
    Path(std::io::Result<PathBuf>),
    TempFile(std::io::Result<(File, PathBuf)>),
}

pub(crate) fn is_operation(name: &str) -> bool {
    matches!(
        name,
        "File::open"
            | "File::open_path"
            | "File::read"
            | "File::read_bytes"
            | "File::read_text"
            | "File::write_bytes"
            | "File::write_text"
            | "File::metadata"
            | "File::read_dir"
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
    let native = if matches!(name, "File::open" | "File::read") {
        NativeString::from_text(runtime.as_string(arg(0)?)?)
    } else {
        runtime.as_path(arg(0)?)?
    };
    let operation = match name {
        "File::open" => Operation::Open("Read".into()),
        "File::open_path" => {
            let Object::Variant { tag, fields } = runtime.heap.get(arg(1)?)? else {
                return Err(RuntimeError::internal("expected file open mode"));
            };
            if !fields.is_empty() {
                return Err(RuntimeError::internal("invalid open mode payload"));
            }
            Operation::Open(tag.clone())
        }
        "File::read" => Operation::Read(ReadKind::LegacyText),
        "File::read_bytes" => Operation::Read(ReadKind::Bytes),
        "File::read_text" => Operation::Read(ReadKind::Text),
        "File::write_bytes" => {
            let Object::Bytes(bytes) = runtime.heap.get(arg(1)?)? else {
                return Err(RuntimeError::internal("expected filesystem write bytes"));
            };
            Operation::Write(bytes.clone())
        }
        "File::write_text" => {
            Operation::Write(runtime.as_string(arg(1)?)?.as_bytes().to_vec().into())
        }
        "File::metadata" => Operation::Metadata(
            args.get(1)
                .map(|&value| runtime.truth(value))
                .transpose()?
                .unwrap_or(true),
        ),
        "File::read_dir" => Operation::ReadDir,
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
        path: native_path(native.clone()),
        native,
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
            Operation::Read(kind) => Reply::Read(kind, Err(error)),
            Operation::Metadata(_) => Reply::Metadata(Err(error)),
            Operation::ReadDir => Reply::Entries(self.native, Err(error)),
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
            Operation::Read(kind) => Reply::Read(
                kind,
                path.and_then(|path| read_all(&path, &self.cancellation)),
            ),
            Operation::Write(bytes) => {
                Reply::Unit(path.and_then(|path| write_all(&path, &bytes, &self.cancellation)))
            }
            Operation::Metadata(follow) => Reply::Metadata(path.and_then(|path| {
                if follow {
                    fs::metadata(path)
                } else {
                    fs::symlink_metadata(path)
                }
            })),
            Operation::ReadDir => Reply::Entries(
                self.native,
                path.and_then(|path| {
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
                    entries.sort_by(|a, b| a.0.cmp(&b.0));
                    Ok(entries)
                }),
            ),
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
fn read_all(
    path: &Path,
    cancellation: &crate::process_io::Cancellation,
) -> std::io::Result<Vec<u8>> {
    let state = retry(cancellation, || open(path, "Read"))?;
    let file = state.file.as_ref().expect("new file authority");
    let mut result = Vec::new();
    let mut chunk = [0; 64 * 1024];
    loop {
        let count = retry(cancellation, || {
            crate::platform_file::read(file, &mut chunk)
        })?;
        if count == 0 {
            return Ok(result);
        }
        result
            .try_reserve(count)
            .map_err(|_| std::io::Error::other("filesystem read allocation failed"))?;
        result.extend_from_slice(&chunk[..count]);
    }
}
fn write_all(
    path: &Path,
    bytes: &[u8],
    cancellation: &crate::process_io::Cancellation,
) -> std::io::Result<()> {
    let state = retry(cancellation, || open(path, "WriteTruncate"))?;
    let file = state.file.as_ref().expect("new file authority");
    let mut remaining = bytes;
    while !remaining.is_empty() {
        let count = retry(cancellation, || {
            crate::platform_file::write(file, &remaining[..remaining.len().min(64 * 1024)])
        })?;
        if count == 0 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::WriteZero,
                "nonempty filesystem write made no progress",
            ));
        }
        remaining = &remaining[count..];
    }
    Ok(())
}

pub(crate) fn finish(runtime: &mut Runtime, reply: Reply) -> Result<Handle> {
    let value = match reply {
        Reply::Open(Ok(state)) => runtime.file_handle(state)?,
        Reply::Open(Err(error))
        | Reply::Metadata(Err(error))
        | Reply::Entries(_, Err(error))
        | Reply::Path(Err(error))
        | Reply::TempFile(Err(error)) => return runtime.io_result(Err(error)),
        Reply::Read(kind, data) => {
            let data = match data {
                Ok(data) => data,
                Err(error) => return read_error(runtime, kind, error.to_string(), Some(error)),
            };
            match kind {
                ReadKind::Bytes => runtime.allocate(Object::Bytes(data.into()))?,
                ReadKind::LegacyText | ReadKind::Text => match String::from_utf8(data) {
                    Ok(text) => runtime.string(text)?,
                    Err(error) => return read_error(runtime, kind, error.to_string(), None),
                },
            }
        }
        Reply::Unit(result) => return runtime.io_unit_result(result),
        Reply::Metadata(Ok(metadata)) => runtime.file_metadata(metadata)?,
        Reply::Entries(native, Ok(entries)) => {
            let mut output = Vec::with_capacity(entries.len());
            for (entry_name, kind) in entries {
                let path =
                    runtime.allocate(Object::Path(crate::path::join(&native, &entry_name)))?;
                let name = runtime.allocate(Object::NativeString(entry_name))?;
                let kind = runtime.variant(&format!("File::FileKind::{kind}"), vec![])?;
                output.push(
                    runtime.allocate(Object::Record(
                        [
                            ("path".into(), path),
                            ("name".into(), name),
                            ("kind".into(), kind),
                        ]
                        .into(),
                    ))?,
                );
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

fn read_error(
    runtime: &mut Runtime,
    kind: ReadKind,
    message: String,
    host: Option<std::io::Error>,
) -> Result<Handle> {
    if matches!(kind, ReadKind::LegacyText) {
        let error = runtime.string(message)?;
        runtime.variant("Err", vec![error])
    } else if let Some(error) = host {
        runtime.io_result(Err(error))
    } else {
        runtime.io_failure("InvalidData", &message)
    }
}
