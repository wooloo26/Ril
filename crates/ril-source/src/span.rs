use std::{
    collections::{BTreeMap, HashMap},
    path::{Path, PathBuf},
    sync::Arc,
};

use crate::diag::{Code, Diagnostic};

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FileId(pub usize);

impl FileId {
    /// Dedicated sentinel for synthetic built-in declarations (`ril/prelude`, etc.).
    pub const BUILTIN: Self = Self(usize::MAX);

    /// Compute a deterministic, path-stable `FileId` independent of file enumeration order.
    ///
    /// Never returns `0` or [`Self::BUILTIN`].
    pub fn from_path(path: &Path) -> Self {
        let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
        for component in path.to_string_lossy().as_bytes() {
            let byte = if *component == b'\\' {
                b'/'
            } else {
                *component
            };
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
        let mut raw = usize::try_from(hash).unwrap_or((hash & 0xffff_ffff) as usize);
        if raw == 0 || raw == usize::MAX {
            raw = 1;
        }
        Self(raw)
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Span {
    pub file: FileId,
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub const fn new(file: FileId, start: usize, end: usize) -> Self {
        Self { file, start, end }
    }

    #[must_use]
    pub fn join(self, other: Self) -> Self {
        debug_assert_eq!(self.file, other.file);
        Self::new(
            self.file,
            self.start.min(other.start),
            self.end.max(other.end),
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Location {
    pub line: usize,
    pub column: usize,
}

#[derive(Clone, Debug)]
pub struct SourceFile {
    id: FileId,
    path: PathBuf,
    text: Arc<str>,
    lines: Vec<usize>,
}

impl SourceFile {
    pub fn from_bytes(id: FileId, path: PathBuf, bytes: &[u8]) -> Result<Self, Diagnostic> {
        if bytes.starts_with(&[0xef, 0xbb, 0xbf]) {
            return Err(Diagnostic::error(
                Code::E0104,
                Span::new(id, 0, 3),
                "UTF-8 BOM",
            ));
        }
        let text = std::str::from_utf8(bytes).map_err(|err| {
            let start = err.valid_up_to();
            let end = err.error_len().map_or(bytes.len(), |length| start + length);
            Diagnostic::error(Code::E0104, Span::new(id, start, end), "invalid UTF-8")
        })?;
        let text: Arc<str> = if text.contains("\r\n") {
            text.replace("\r\n", "\n").into()
        } else {
            text.into()
        };
        let lines = std::iter::once(0)
            .chain(text.match_indices('\n').map(|(i, _)| i + 1))
            .collect();
        Ok(Self {
            id,
            path,
            text,
            lines,
        })
    }

    pub const fn id(&self) -> FileId {
        self.id
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn location(&self, offset: usize) -> Option<Location> {
        let line = self.lines.partition_point(|&start| start <= offset);
        let start = *self.lines.get(line.checked_sub(1)?)?;
        let column = self.text.get(start..offset)?.chars().count() + 1;
        Some(Location { line, column })
    }

    pub fn span(&self, start: usize, end: usize) -> Span {
        Span::new(self.id, start, end)
    }
}

#[derive(Clone, Default)]
pub struct SourceMap {
    files: HashMap<FileId, Option<SourceFile>>,
    paths: HashMap<FileId, PathBuf>,
    next_id: usize,
}

impl SourceMap {
    pub fn add(&mut self, path: PathBuf, bytes: &[u8]) -> Result<FileId, Box<Diagnostic>> {
        let mut id = FileId(self.next_id);
        while self.files.contains_key(&id) || id == FileId::BUILTIN {
            self.next_id = self.next_id.wrapping_add(1);
            id = FileId(self.next_id);
        }
        self.next_id = self.next_id.wrapping_add(1);
        self.add_with_id(id, path, bytes)
    }

    /// Register a file under a specific (typically path-hashed) [`FileId`].
    ///
    /// Resolves any hash collision deterministically so two distinct paths never share an ID.
    pub fn add_with_id(
        &mut self,
        mut id: FileId,
        path: PathBuf,
        bytes: &[u8],
    ) -> Result<FileId, Box<Diagnostic>> {
        while self
            .paths
            .get(&id)
            .is_some_and(|existing| existing != &path)
            || id == FileId::BUILTIN
        {
            id = FileId(id.0.wrapping_add(1));
            if id.0 == 0 || id == FileId::BUILTIN {
                id = FileId(1);
            }
        }
        self.paths.insert(id, path.clone());
        match SourceFile::from_bytes(id, path, bytes) {
            Ok(file) => {
                self.files.insert(id, Some(file));
                Ok(id)
            }
            Err(diagnostic) => {
                self.files.insert(id, None);
                Err(Box::new(diagnostic))
            }
        }
    }

    pub fn record_path(&mut self, id: FileId, path: PathBuf) {
        self.paths.entry(id).or_insert(path);
    }

    pub fn get(&self, id: FileId) -> Option<&SourceFile> {
        self.files.get(&id)?.as_ref()
    }

    pub fn path(&self, id: FileId) -> Option<&Path> {
        self.paths.get(&id).map(PathBuf::as_path)
    }

    pub fn file_paths(&self) -> BTreeMap<FileId, PathBuf> {
        self.paths
            .iter()
            .map(|(&id, path)| (id, path.clone()))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_map_supports_sparse_and_path_hashed_file_ids() {
        let mut map = SourceMap::default();
        let id_a = FileId::from_path(Path::new("pkg/alpha.ril"));
        let id_b = FileId::from_path(Path::new("pkg/beta.ril"));
        assert_ne!(id_a, id_b);
        assert_ne!(id_a, FileId::BUILTIN);
        let added_a = map
            .add_with_id(id_a, PathBuf::from("pkg/alpha.ril"), b"let a = 1\n")
            .unwrap_or(FileId(0));
        let added_b = map
            .add_with_id(id_b, PathBuf::from("pkg/beta.ril"), b"let b = 2\n")
            .unwrap_or(FileId(0));
        assert_eq!(added_a, id_a);
        assert_eq!(added_b, id_b);
        assert_eq!(map.get(id_a).map(SourceFile::text), Some("let a = 1\n"));
        assert_eq!(map.get(id_b).map(SourceFile::text), Some("let b = 2\n"));
        assert_eq!(map.path(id_a), Some(Path::new("pkg/alpha.ril")));
    }
}
