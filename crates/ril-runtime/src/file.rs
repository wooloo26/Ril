//! File authority is a task-local opaque identity, shared by all its aliases.
//! Host handles are outside the movable language-value graph and never cloned.
use crate::{
    heap::{Handle, Object},
    native_string::NativeString,
    value::{Result, Runtime, RuntimeError},
};
use std::{
    fs::{self, File},
    io::{Read, Seek, SeekFrom, Write},
    path::{Path, PathBuf},
    sync::{Arc, Mutex},
};
pub(crate) mod filesystem;
pub(crate) mod host;

#[derive(Debug)]
pub(crate) struct FileState {
    file: Option<File>,
    readable: bool,
    writable: bool,
}
pub(crate) fn release_host(state: &Arc<Mutex<FileState>>) {
    let file = state
        .lock()
        .unwrap_or_else(|error| error.into_inner())
        .file
        .take();
    // Implicit release reports no close errors and never flushes/syncs.
    drop(file);
}

fn native_path(value: NativeString) -> std::io::Result<PathBuf> {
    if value.contains_nul() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "path contains NUL",
        ));
    }
    value
        .to_os()
        .map(PathBuf::from)
        .map_err(|kind| std::io::Error::new(std::io::ErrorKind::InvalidInput, kind))
}
fn open(path: &Path, mode: &str) -> std::io::Result<FileState> {
    let (readable, writable) = match mode.rsplit("::").next().unwrap_or(mode) {
        "Read" => (true, false),
        "WriteNew" | "WriteTruncate" | "Append" => (false, true),
        "ReadWrite" => (true, true),
        _ => {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "unknown file mode",
            ));
        }
    };
    Ok(FileState {
        file: Some(crate::platform_file::open(path, mode)?),
        readable,
        writable,
    })
}
fn kind(metadata: &fs::Metadata) -> &'static str {
    let ty = metadata.file_type();
    if ty.is_symlink() {
        "Symlink"
    } else if ty.is_file() {
        "Regular"
    } else if ty.is_dir() {
        "Directory"
    } else {
        "Other"
    }
}
impl Runtime {
    fn file_state(&self, handle: Handle) -> Result<Arc<Mutex<FileState>>> {
        let Object::File(id) = self.heap.get(handle)? else {
            return Err(RuntimeError::internal("expected file authority"));
        };
        self.files
            .get(*id as usize)
            .cloned()
            .ok_or_else(|| RuntimeError::internal("invalid file authority"))
    }
    fn file_handle(&mut self, state: FileState) -> Result<Handle> {
        let id = self.files.len() as u64;
        self.files.push(Arc::new(Mutex::new(state)));
        self.allocate(Object::File(id))
    }
    #[cfg(test)]
    pub(crate) fn release_file(&mut self, handle: Handle) -> Result<bool> {
        if !matches!(self.heap.get(handle)?, Object::File(_)) {
            return Ok(false);
        }
        release_host(&self.file_state(handle)?);
        Ok(true)
    }
    fn file_metadata(&mut self, metadata: fs::Metadata) -> Result<Handle> {
        let file_kind = self.variant(&format!("File::FileKind::{}", kind(&metadata)), vec![])?;
        let size = self.integer(
            if metadata.is_file() {
                i128::from(metadata.len())
            } else {
                0
            },
            64,
            false,
        )?;
        let timestamp = metadata.modified().ok().and_then(|time| {
            let nanos = match time.duration_since(std::time::UNIX_EPOCH) {
                Ok(duration) => i128::try_from(duration.as_nanos()).ok()?,
                Err(error) => -i128::try_from(error.duration().as_nanos()).ok()?,
            };
            Some((
                i64::try_from(nanos.div_euclid(1_000_000_000)).ok()?,
                nanos.rem_euclid(1_000_000_000) as u32,
            ))
        });
        let modified = if let Some((seconds, nanos)) = timestamp {
            let seconds = self.integer(i128::from(seconds), 64, true)?;
            let nanos = self.integer(i128::from(nanos), 32, false)?;
            let value = self.allocate(Object::Record(
                [("seconds".into(), seconds), ("nanos".into(), nanos)].into(),
            ))?;
            self.variant("Some", vec![value])?
        } else {
            self.variant("None", vec![])?
        };
        self.allocate(Object::Record(
            [
                ("kind".into(), file_kind),
                ("size".into(), size),
                ("modified".into(), modified),
            ]
            .into(),
        ))
    }
    pub(crate) fn file_builtin(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let arg = |index| {
            args.get(index)
                .copied()
                .ok_or_else(|| RuntimeError::internal("missing file argument"))
        };
        if matches!(
            name,
            "File::SeekFrom::Start" | "File::SeekFrom::Current" | "File::SeekFrom::End"
        ) {
            return self.variant(name, vec![arg(0)?]);
        }
        if matches!(
            name,
            "File::read_chunk" | "File::write" | "File::seek" | "File::sync" | "File::close"
        ) {
            return self.file_stream(name, args);
        }
        if filesystem::is_operation(name) {
            let request = filesystem::prepare(self, name, args)?;
            return filesystem::finish(self, request.perform()?);
        }
        Err(RuntimeError::internal(
            "file callback operation needs native invocation bridge",
        ))
    }
    fn file_stream(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let request = host::prepare(self, name, args)?;
        host::finish(self, request.perform()?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn path(runtime: &mut Runtime, value: &Path) -> Handle {
        runtime
            .allocate(Object::Path(NativeString::from_os(value.as_os_str())))
            .unwrap()
    }
    fn payload(runtime: &Runtime, value: Handle, expected: &str) -> Handle {
        let Object::Variant { tag, fields } = runtime.heap.get(value).unwrap() else {
            panic!("expected variant");
        };
        assert_eq!(tag, expected);
        assert_eq!(fields.len(), 1);
        fields[0]
    }
    fn failure_kind(runtime: &mut Runtime, value: Handle) -> String {
        let error = payload(runtime, value, "Err");
        let kind = runtime.field(error, "kind").unwrap();
        let Object::Variant { tag, .. } = runtime.heap.get(kind).unwrap() else {
            panic!("kind");
        };
        tag.clone()
    }
    #[test]
    fn file_authority_shares_closure_and_validates_modes_before_empty_requests() {
        let directory = tempfile::tempdir().unwrap();
        let disk_path = directory.path().join("file.bin");
        fs::write(&disk_path, b"abcd").unwrap();
        let mut runtime = Runtime::default();
        let path = path(&mut runtime, &disk_path);
        let mode = runtime.variant("File::OpenMode::Read", vec![]).unwrap();
        let opened = runtime
            .file_builtin("File::open_path", &[path, mode])
            .unwrap();
        let file = payload(&runtime, opened, "Ok");
        assert_eq!(
            runtime.heap.deep_clone(file),
            Err(crate::heap::HeapError::NonClonable)
        );
        let zero = runtime.int(0).unwrap();
        let empty = runtime
            .file_builtin("File::read_chunk", &[file, zero])
            .unwrap();
        let empty = payload(&runtime, empty, "Ok");
        let end = runtime.field(empty, "end").unwrap();
        assert!(!runtime.truth(end).unwrap());
        let bytes = runtime.allocate(Object::Bytes(vec![].into())).unwrap();
        let progress = runtime.file_builtin("File::write", &[file, bytes]).unwrap();
        let error = runtime.field(progress, "error").unwrap();
        let error = payload(&runtime, error, "Some");
        let error = runtime.variant("Err", vec![error]).unwrap();
        assert_eq!(
            failure_kind(&mut runtime, error),
            "Io::ErrorKind::InvalidInput"
        );
        let two = runtime.int(2).unwrap();
        let chunk = runtime
            .file_builtin("File::read_chunk", &[file, two])
            .unwrap();
        let chunk = payload(&runtime, chunk, "Ok");
        let data = runtime.field(chunk, "data").unwrap();
        assert_eq!(runtime.as_bytes(data).unwrap(), b"ab");
        let alias = file;
        runtime.file_builtin("File::close", &[file]).unwrap();
        runtime.file_builtin("File::close", &[alias]).unwrap();
        let closed = runtime
            .file_builtin("File::read_chunk", &[alias, zero])
            .unwrap();
        assert_eq!(failure_kind(&mut runtime, closed), "Io::ErrorKind::Closed");
        let negative = runtime.int(-1).unwrap();
        assert_eq!(
            runtime
                .file_builtin("File::read_chunk", &[alias, negative])
                .unwrap_err()
                .tag,
            ril_runtime_api::abi::OutcomeTag::LanguagePanic
        );
    }
    #[test]
    fn exclusive_creation_rename_and_sorted_directory_names_preserve_existing_files() {
        let directory = tempfile::tempdir().unwrap();
        let mut runtime = Runtime::default();
        let a = path(&mut runtime, &directory.path().join("a"));
        let b = path(&mut runtime, &directory.path().join("b"));
        let mode = runtime.variant("File::OpenMode::WriteNew", vec![]).unwrap();
        let opened = runtime.file_builtin("File::open_path", &[b, mode]).unwrap();
        let file = payload(&runtime, opened, "Ok");
        let bytes = runtime
            .allocate(Object::Bytes(b"old".to_vec().into()))
            .unwrap();
        runtime.file_builtin("File::write", &[file, bytes]).unwrap();
        runtime.release_file(file).unwrap();
        fs::write(directory.path().join("a"), b"source").unwrap();
        let result = runtime.file_builtin("File::open_path", &[b, mode]).unwrap();
        assert_eq!(
            failure_kind(&mut runtime, result),
            "Io::ErrorKind::AlreadyExists"
        );
        let result = runtime.file_builtin("File::rename", &[a, b]).unwrap();
        assert_eq!(
            failure_kind(&mut runtime, result),
            "Io::ErrorKind::AlreadyExists"
        );
        assert_eq!(fs::read(directory.path().join("a")).unwrap(), b"source");
        assert_eq!(fs::read(directory.path().join("b")).unwrap(), b"old");
        let dir = path(&mut runtime, directory.path());
        let entries = runtime.file_builtin("File::read_dir", &[dir]).unwrap();
        let entries = payload(&runtime, entries, "Ok");
        let entries = runtime.sequence(entries).unwrap();
        let names: Vec<_> = entries
            .into_iter()
            .map(|entry| {
                let name = runtime.field(entry, "name").unwrap();
                runtime.as_native(name).unwrap().text().unwrap()
            })
            .collect();
        assert_eq!(names, ["a", "b"]);
        runtime.file_builtin("File::remove_file", &[b]).unwrap();
        let renamed = runtime.file_builtin("File::rename", &[a, b]).unwrap();
        payload(&runtime, renamed, "Ok");
        assert!(!directory.path().join("a").exists());
        assert_eq!(fs::read(directory.path().join("b")).unwrap(), b"source");
    }
    #[test]
    fn seek_failures_do_not_change_position_and_text_reads_are_strict() {
        let directory = tempfile::tempdir().unwrap();
        let disk_path = directory.path().join("bad.txt");
        fs::write(&disk_path, [255, b'a']).unwrap();
        let mut runtime = Runtime::default();
        let path = path(&mut runtime, &disk_path);
        let text = runtime.file_builtin("File::read_text", &[path]).unwrap();
        assert_eq!(
            failure_kind(&mut runtime, text),
            "Io::ErrorKind::InvalidData"
        );
        let bytes = runtime.file_builtin("File::read_bytes", &[path]).unwrap();
        let bytes = payload(&runtime, bytes, "Ok");
        assert_eq!(runtime.as_bytes(bytes).unwrap(), &[255, b'a']);
        let mode = runtime
            .variant("File::OpenMode::ReadWrite", vec![])
            .unwrap();
        let file = runtime
            .file_builtin("File::open_path", &[path, mode])
            .unwrap();
        let file = payload(&runtime, file, "Ok");
        let one = runtime.integer(1, 64, true).unwrap();
        let position = runtime.variant("File::SeekFrom::Start", vec![one]).unwrap();
        let success = runtime
            .file_builtin("File::seek", &[file, position])
            .unwrap();
        assert_eq!(
            runtime
                .as_integer(payload(&runtime, success, "Ok"))
                .unwrap(),
            1
        );
        let negative = runtime.integer(-2, 64, true).unwrap();
        let position = runtime
            .variant("File::SeekFrom::Current", vec![negative])
            .unwrap();
        let invalid = runtime
            .file_builtin("File::seek", &[file, position])
            .unwrap();
        assert_eq!(
            failure_kind(&mut runtime, invalid),
            "Io::ErrorKind::InvalidInput"
        );
        let one = runtime.int(1).unwrap();
        let chunk = runtime
            .file_builtin("File::read_chunk", &[file, one])
            .unwrap();
        let chunk = payload(&runtime, chunk, "Ok");
        let bytes = runtime.field(chunk, "data").unwrap();
        assert_eq!(runtime.as_bytes(bytes).unwrap(), b"a");
        runtime.release_file(file).unwrap();
    }

    #[test]
    fn prepared_filesystem_requests_own_inputs_after_managed_collection() {
        let directory = tempfile::tempdir().unwrap();
        let disk_path = directory.path().join("owned-inputs.bin");
        let mut worker = crate::shared::Worker::new(Runtime::default());
        let (request, source_path, source_bytes) = worker.with(|runtime| {
            let path = path(runtime, &disk_path);
            let bytes = runtime
                .allocate(Object::Bytes(b"\0\xffowned".to_vec().into()))
                .unwrap();
            let request =
                filesystem::prepare(runtime, "File::write_bytes", &[path, bytes]).unwrap();
            (request, path, bytes)
        });
        worker.with(|runtime| {
            runtime.statement_end();
            runtime.collect().unwrap();
            assert!(runtime.heap.get(source_path).is_err());
            assert!(runtime.heap.get(source_bytes).is_err());
        });
        let reply = std::thread::spawn(move || request.perform())
            .join()
            .unwrap()
            .unwrap();
        worker.with(|runtime| {
            let value = filesystem::finish(runtime, reply).unwrap();
            payload(runtime, value, "Ok");
        });
        assert_eq!(fs::read(disk_path).unwrap(), b"\0\xffowned");
    }

    #[test]
    fn prepared_reads_preserve_legacy_errors_and_defer_handle_installation() {
        let directory = tempfile::tempdir().unwrap();
        let disk_path = directory.path().join("invalid-utf8");
        fs::write(&disk_path, [0xff]).unwrap();
        let mut runtime = Runtime::default();
        let legacy_path = runtime.string(disk_path.to_str().unwrap().into()).unwrap();
        let request = filesystem::prepare(&runtime, "File::read", &[legacy_path]).unwrap();
        runtime.statement_end();
        runtime.collect().unwrap();
        let value = filesystem::finish(&mut runtime, request.perform().unwrap()).unwrap();
        assert!(
            !runtime
                .as_string(payload(&runtime, value, "Err"))
                .unwrap()
                .is_empty()
        );
        let source_path = path(&mut runtime, &disk_path);
        let mode = runtime.variant("File::OpenMode::Read", vec![]).unwrap();
        let request =
            filesystem::prepare(&runtime, "File::open_path", &[source_path, mode]).unwrap();
        let reply = request.perform().unwrap();
        assert!(runtime.files.is_empty());
        runtime.statement_end();
        runtime.collect().unwrap();
        let value = filesystem::finish(&mut runtime, reply).unwrap();
        let file = payload(&runtime, value, "Ok");
        assert_eq!(runtime.files.len(), 1);
        runtime.release_file(file).unwrap();
    }
}
