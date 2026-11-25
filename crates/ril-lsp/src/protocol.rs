use std::{
    io::{BufRead, Write},
    path::{Path, PathBuf},
};

use ril_source::span::{SourceFile, SourceMap, Span};
use serde_json::{Value, json};

pub(crate) fn read_message<R: BufRead>(reader: &mut R) -> Result<Option<Value>, String> {
    let mut content_length: Option<usize> = None;
    let mut line = String::new();
    loop {
        line.clear();
        let read = reader.read_line(&mut line).map_err(|e| e.to_string())?;
        if read == 0 {
            return Ok(None);
        }
        let trimmed = line.trim();
        if trimmed.is_empty() {
            break;
        }
        if let Some(rest) = trimmed
            .strip_prefix("Content-Length:")
            .or_else(|| trimmed.strip_prefix("content-length:"))
        {
            content_length = Some(
                rest.trim()
                    .parse::<usize>()
                    .map_err(|e| format!("invalid Content-Length: {e}"))?,
            );
        }
    }
    let len = content_length.ok_or_else(|| "missing Content-Length header".to_owned())?;
    let mut buf = vec![0u8; len];
    reader.read_exact(&mut buf).map_err(|e| e.to_string())?;
    let value: Value = serde_json::from_slice(&buf).map_err(|e| e.to_string())?;
    Ok(Some(value))
}

pub(crate) fn write_message<W: Write>(writer: &mut W, value: &Value) -> Result<(), String> {
    let body = serde_json::to_vec(value).map_err(|e| e.to_string())?;
    write!(writer, "Content-Length: {}\r\n\r\n", body.len()).map_err(|e| e.to_string())?;
    writer.write_all(&body).map_err(|e| e.to_string())?;
    writer.flush().map_err(|e| e.to_string())
}

pub(crate) fn percent_decode(raw: &str) -> String {
    let bytes = raw.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes.get(i) == Some(&b'%')
            && let (Some(&hi), Some(&lo)) = (bytes.get(i + 1), bytes.get(i + 2))
            && let (Some(h), Some(l)) = (hex_val(hi), hex_val(lo))
        {
            out.push((h << 4) | l);
            i += 3;
            continue;
        }
        if let Some(&b) = bytes.get(i) {
            out.push(b);
        }
        i += 1;
    }
    String::from_utf8(out).unwrap_or_else(|_| raw.to_owned())
}

const fn hex_val(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

pub(crate) fn uri_to_fs_path(uri: &str) -> Option<PathBuf> {
    let rest = uri.strip_prefix("file://")?;
    let path_str = rest.strip_prefix("localhost").unwrap_or(rest);
    if path_str.is_empty() {
        None
    } else {
        Some(PathBuf::from(percent_decode(path_str)))
    }
}

pub(crate) fn fs_path_to_uri(path: &Path) -> String {
    let normalized = path.to_string_lossy().replace('\\', "/");
    if normalized.starts_with('/') {
        format!("file://{normalized}")
    } else {
        format!("file:///{normalized}")
    }
}

pub(crate) fn uri_to_logical_path(uri: &str) -> PathBuf {
    let stripped = uri.strip_prefix("file://").unwrap_or(uri);
    let file_name = Path::new(stripped)
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("main.ril");
    Path::new("pkg").join(file_name)
}

/// Converts a 0-based LSP `(line, utf16_col)` position to a byte offset in `text`.
pub(crate) fn line_col_to_offset(text: &str, target_line: usize, target_col: usize) -> Option<usize> {
    let mut line = 0usize;
    let mut col = 0usize;
    for (idx, ch) in text.char_indices() {
        if line == target_line && col >= target_col {
            return Some(idx);
        }
        if ch == '\n' {
            if line == target_line {
                return Some(idx);
            }
            line += 1;
            col = 0;
        } else {
            col += ch.len_utf16();
        }
    }
    (line == target_line).then_some(text.len())
}

/// Converts a byte offset in `text` to 0-based LSP `(line, utf16_col)`.
pub(crate) fn offset_to_line_col(text: &str, offset: usize) -> (usize, usize) {
    let clamped = offset.min(text.len());
    let mut line = 0usize;
    let mut col = 0usize;
    for (idx, ch) in text.char_indices() {
        if idx >= clamped {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 0;
        } else {
            col += ch.len_utf16();
        }
    }
    (line, col)
}

pub(crate) fn span_to_lsp_range(sources: &SourceMap, span: Span) -> Option<Value> {
    let file = sources.get(span.file)?;
    span_to_file_range(file, span)
}

pub(crate) fn span_to_file_range(file: &SourceFile, span: Span) -> Option<Value> {
    let text = file.text();
    let (start_line, start_col) = offset_to_line_col(text, span.start);
    let (end_line, end_col) = offset_to_line_col(text, span.end.max(span.start));
    Some(json!({
        "start": { "line": start_line, "character": start_col },
        "end": { "line": end_line, "character": end_col }
    }))
}

pub(crate) fn zero_range() -> Value {
    json!({
        "start": { "line": 0, "character": 0 },
        "end": { "line": 0, "character": 0 }
    })
}

pub(crate) fn extract_position(params: &Value) -> Option<(&str, usize, usize)> {
    let uri = params.pointer("/textDocument/uri")?.as_str()?;
    let line = usize::try_from(params.pointer("/position/line")?.as_u64()?).ok()?;
    let character = usize::try_from(params.pointer("/position/character")?.as_u64()?).ok()?;
    Some((uri, line, character))
}

/// Extracts contiguous leading `--` doc comments immediately above `decl_offset`.
pub(crate) fn extract_doc_comment(text: &str, decl_offset: usize) -> Option<String> {
    let (decl_line, _) = offset_to_line_col(text, decl_offset);
    if decl_line == 0 {
        return None;
    }
    let lines: Vec<&str> = text.lines().collect();
    let mut collected = Vec::new();
    let mut line_idx = decl_line;
    while line_idx > 0 {
        line_idx -= 1;
        let trimmed = lines.get(line_idx).map(|s| s.trim()).unwrap_or("");
        if let Some(rest) = trimmed.strip_prefix("--") {
            let cleaned = rest.strip_prefix(' ').unwrap_or(rest);
            collected.push(cleaned);
        } else {
            break;
        }
    }
    if collected.is_empty() {
        return None;
    }
    collected.reverse();
    let doc = collected.join("\n").trim().to_owned();
    (!doc.is_empty()).then_some(doc)
}

/// Returns the LSP range at which a new `use ...` import line should be inserted.
pub(crate) fn import_insert_line(text: &str) -> usize {
    let mut last_use_line: Option<usize> = None;
    let mut first_non_comment: Option<usize> = None;
    for (idx, raw) in text.lines().enumerate() {
        let trimmed = raw.trim();
        if trimmed.is_empty() || trimmed.starts_with("--") {
            continue;
        }
        if first_non_comment.is_none() {
            first_non_comment = Some(idx);
        }
        let is_import = trimmed.starts_with("use ")
            || trimmed.starts_with("pub use ")
            || trimmed.starts_with("pkg use ");
        if is_import && trimmed.contains('/') {
            last_use_line = Some(idx);
        } else if last_use_line.is_some() {
            break;
        }
    }
    if let Some(line) = last_use_line {
        line + 1
    } else {
        first_non_comment.unwrap_or(0)
    }
}
