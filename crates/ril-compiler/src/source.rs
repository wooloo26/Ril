//! Byte-preserving source storage. Decoding is an explicit, fallible operation.
use std::{
    path::{Path, PathBuf},
    sync::Arc,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnitKind {
    Executable,
    Library,
    External,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(pub u32);

/// Half-open byte offsets, including for sources that are not valid UTF-8.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    pub file: FileId,
    pub start: u32,
    pub end: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceFile {
    path: PathBuf,
    bytes: Arc<[u8]>,
}

impl SourceFile {
    pub fn path(&self) -> &Path {
        &self.path
    }
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
    pub fn text(&self) -> Result<&str, std::str::Utf8Error> {
        std::str::from_utf8(&self.bytes)
    }
}

#[derive(Debug)]
pub enum SourceError {
    TooLarge,
    InvalidSpan,
}

#[derive(Default)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

impl SourceMap {
    pub fn add(
        &mut self,
        path: PathBuf,
        bytes: impl Into<Arc<[u8]>>,
    ) -> Result<FileId, SourceError> {
        let bytes = bytes.into();
        u32::try_from(bytes.len()).map_err(|_| SourceError::TooLarge)?;
        let id = FileId(u32::try_from(self.files.len()).map_err(|_| SourceError::TooLarge)?);
        self.files.push(SourceFile { path, bytes });
        Ok(id)
    }
    pub fn get(&self, id: FileId) -> Option<&SourceFile> {
        self.files.get(id.0 as usize)
    }
    pub fn span(&self, file: FileId, start: u32, end: u32) -> Result<Span, SourceError> {
        let source = self.get(file).ok_or(SourceError::InvalidSpan)?;
        if start > end || end as usize > source.bytes.len() {
            return Err(SourceError::InvalidSpan);
        }
        Ok(Span { file, start, end })
    }
    pub fn slice(&self, span: Span) -> Result<&[u8], SourceError> {
        self.span(span.file, span.start, span.end)?;
        Ok(&self.files[span.file.0 as usize].bytes[span.start as usize..span.end as usize])
    }
}

impl std::fmt::Display for SourceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::TooLarge => "source or source collection exceeds the supported size",
            Self::InvalidSpan => "invalid file or byte range",
        })
    }
}

impl std::error::Error for SourceError {}

impl SourceFile {
    /// One-based line and Unicode scalar column, retaining offsets on bad bytes.
    pub fn location(&self, offset: u32) -> (usize, usize) {
        let prefix = &self.bytes[..(offset as usize).min(self.bytes.len())];
        let mut line = 1;
        let mut start = 0;
        for (i, byte) in prefix.iter().enumerate() {
            if *byte == b'\r' || *byte == b'\n' && (i == 0 || prefix[i - 1] != b'\r') {
                line += 1;
            }
            if matches!(*byte, b'\r' | b'\n') {
                start = i + 1;
            }
        }
        let column = String::from_utf8_lossy(&prefix[start..]).chars().count() + 1;
        (line, column)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn preserves_bytes_and_checks_ranges() {
        let mut sources = SourceMap::default();
        let id = sources
            .add("broken.ril".into(), vec![0xff, 13, 10])
            .unwrap();
        assert!(sources.get(id).unwrap().text().is_err());
        assert_eq!(
            sources.slice(sources.span(id, 0, 3).unwrap()).unwrap(),
            [0xff, 13, 10]
        );
        assert!(sources.span(id, 2, 1).is_err());
        assert!(sources.span(id, 0, 4).is_err());
        assert!(sources.span(FileId(9), 0, 0).is_err());
    }
}
