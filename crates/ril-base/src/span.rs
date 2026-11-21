use std::{path::PathBuf, sync::Arc};

use crate::diag::{Code, Diagnostic};

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct FileId(pub usize);

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
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

    pub fn path(&self) -> &std::path::Path {
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

#[derive(Default)]
pub struct SourceMap {
    files: Vec<Option<SourceFile>>,
}

impl SourceMap {
    pub fn add(&mut self, path: PathBuf, bytes: &[u8]) -> Result<FileId, Box<Diagnostic>> {
        let id = FileId(self.files.len());
        match SourceFile::from_bytes(id, path, bytes) {
            Ok(file) => {
                self.files.push(Some(file));
                Ok(id)
            }
            Err(diagnostic) => {
                self.files.push(None);
                Err(Box::new(diagnostic))
            }
        }
    }

    pub fn get(&self, id: FileId) -> Option<&SourceFile> {
        self.files.get(id.0)?.as_ref()
    }
}
