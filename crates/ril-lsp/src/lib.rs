#![forbid(unsafe_code)]

//! Lightweight JSON-RPC 2.0 Language Server (`ril lsp`) powered by incremental `Compiler`.
//!
//! Supports `initialize`, `textDocument/didOpen`, `textDocument/didChange`,
//! `textDocument/publishDiagnostics`, `textDocument/hover`, `textDocument/definition`,
//! `textDocument/formatting`, `shutdown`, and `exit`.

use std::{
    collections::BTreeMap,
    io::{self, BufRead, Write},
    path::{Path, PathBuf},
};

use ril_hir::Resolution;
use ril_sema::ty::Ty;
use ril_source::{
    diag::Severity,
    span::{FileId, SourceFile, Span},
};
use ril_syntax::{fmt, parser::FileKind};
use ril_test::{Stage, Unit, VirtualPackage};
use serde_json::{Value, json};

use ril_driver::{CompileOptions, Compiler};

/// Runs the LSP server over standard input / standard output.
pub fn serve_stdio() -> Result<(), String> {
    let stdin = io::stdin();
    let stdout = io::stdout();
    handle_session(stdin.lock(), stdout.lock())
}

/// Processes a full LSP JSON-RPC 2.0 session over arbitrary `BufRead`/`Write` streams.
pub fn handle_session<R: BufRead, W: Write>(mut reader: R, mut writer: W) -> Result<(), String> {
    let mut state = LspState::new();
    while let Some(message) = read_message(&mut reader)? {
        let method = message
            .get("method")
            .and_then(Value::as_str)
            .unwrap_or_default();
        let id = message.get("id").cloned();
        let params = message.get("params").cloned().unwrap_or(Value::Null);

        match method {
            "initialize" => {
                if let Some(id) = id {
                    write_message(
                        &mut writer,
                        &json!({
                            "jsonrpc": "2.0",
                            "id": id,
                            "result": {
                                "capabilities": {
                                    "textDocumentSync": 1,
                                    "hoverProvider": true,
                                    "definitionProvider": true,
                                    "documentFormattingProvider": true
                                },
                                "serverInfo": {
                                    "name": "ril-lsp",
                                    "version": env!("CARGO_PKG_VERSION")
                                }
                            }
                        }),
                    )?;
                }
            }
            "initialized" => {}
            "textDocument/didOpen" => {
                if let Some(doc) = params.get("textDocument")
                    && let (Some(uri), Some(text)) = (
                        doc.get("uri").and_then(Value::as_str),
                        doc.get("text").and_then(Value::as_str),
                    )
                {
                    state.documents.insert(uri.to_owned(), text.to_owned());
                    let notif = state.publish_diagnostics(uri);
                    write_message(&mut writer, &notif)?;
                }
            }
            "textDocument/didChange" => {
                if let Some(uri) = params.pointer("/textDocument/uri").and_then(Value::as_str)
                    && let Some(text) = params
                        .pointer("/contentChanges/0/text")
                        .and_then(Value::as_str)
                {
                    state.documents.insert(uri.to_owned(), text.to_owned());
                    let notif = state.publish_diagnostics(uri);
                    write_message(&mut writer, &notif)?;
                }
            }
            "textDocument/hover" => {
                if let Some(id) = id {
                    let result = state.hover(&params).unwrap_or(Value::Null);
                    write_message(
                        &mut writer,
                        &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                    )?;
                }
            }
            "textDocument/definition" => {
                if let Some(id) = id {
                    let result = state.definition(&params).unwrap_or(Value::Null);
                    write_message(
                        &mut writer,
                        &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                    )?;
                }
            }
            "textDocument/formatting" => {
                if let Some(id) = id {
                    let result = state.formatting(&params).unwrap_or_else(|| json!([]));
                    write_message(
                        &mut writer,
                        &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                    )?;
                }
            }
            "shutdown" => {
                state.shutdown = true;
                if let Some(id) = id {
                    write_message(
                        &mut writer,
                        &json!({ "jsonrpc": "2.0", "id": id, "result": Value::Null }),
                    )?;
                }
            }
            "exit" => break,
            _ => {
                if let Some(id) = id {
                    write_message(
                        &mut writer,
                        &json!({
                            "jsonrpc": "2.0",
                            "id": id,
                            "error": { "code": -32601, "message": format!("unsupported method {method}") }
                        }),
                    )?;
                }
            }
        }
    }
    Ok(())
}

struct LspState {
    compiler: Compiler,
    documents: BTreeMap<String, String>,
    shutdown: bool,
}

impl LspState {
    fn new() -> Self {
        Self {
            compiler: Compiler::incremental(CompileOptions::default()),
            documents: BTreeMap::new(),
            shutdown: false,
        }
    }

    fn build_package(&self, uri: &str) -> Option<(VirtualPackage, PathBuf)> {
        let text = self.documents.get(uri)?;
        let logical = uri_to_logical_path(uri);
        let unit = if text.contains("fn main") {
            Unit::Bin
        } else {
            Unit::Lib
        };
        let mut pkg = VirtualPackage::new(unit);
        pkg.entry = logical.clone();
        pkg.insert(logical.clone(), text.as_bytes().to_vec());
        for (other_uri, other_text) in &self.documents {
            if other_uri == uri {
                continue;
            }
            pkg.insert(
                uri_to_logical_path(other_uri),
                other_text.as_bytes().to_vec(),
            );
        }
        Some((pkg, logical))
    }

    fn publish_diagnostics(&self, uri: &str) -> Value {
        let mut diagnostics = Vec::new();
        if let Some((pkg, _)) = self.build_package(uri) {
            let checked = self.compiler.check(&pkg, Stage::Access);
            for diag in &checked.result.diagnostics {
                let range = diag
                    .primary
                    .and_then(|span| span_to_lsp_range(&checked.sources, span))
                    .unwrap_or_else(zero_range);
                let severity = match diag.severity {
                    Severity::Error => 1,
                    Severity::Warning => 2,
                };
                let mut item = json!({
                    "range": range,
                    "severity": severity,
                    "source": "ril",
                    "message": diag.message,
                });
                if let Some(code) = diag.code
                    && let Some(obj) = item.as_object_mut()
                {
                    obj.insert("code".into(), json!(code.as_str()));
                }
                diagnostics.push(item);
            }
        }
        json!({
            "jsonrpc": "2.0",
            "method": "textDocument/publishDiagnostics",
            "params": {
                "uri": uri,
                "diagnostics": diagnostics
            }
        })
    }

    fn hover(&self, params: &Value) -> Option<Value> {
        let uri = params.pointer("/textDocument/uri")?.as_str()?;
        let line = usize::try_from(params.pointer("/position/line")?.as_u64()?).ok()?;
        let character = usize::try_from(params.pointer("/position/character")?.as_u64()?).ok()?;
        let text = self.documents.get(uri)?;
        let offset = line_col_to_offset(text, line, character)?;
        let (pkg, logical) = self.build_package(uri)?;
        let (typed, _) = self.compiler.analyze_cached(&pkg).ok()?;
        let file = typed.hir.files().find(|f| f.path == logical)?;
        let file_id = file.id;

        // 1. Check direct definition under cursor (function or binding).
        for (def_id, def) in typed.hir.definitions() {
            if def.name.span.file == file_id
                && offset >= def.name.span.start
                && offset <= def.name.span.end
            {
                let info = describe_definition(&typed, def_id)?;
                return Some(json!({
                    "contents": { "kind": "markdown", "value": format!("```ril\n{info}\n```") }
                }));
            }
        }

        // 2. Check resolved identifier reference under cursor.
        for (&span, resolution) in typed.hir.resolutions() {
            if span.file == file_id
                && offset >= span.start
                && offset <= span.end
                && let Resolution::Definition(def_id) = *resolution
                && let Some(info) = describe_definition(&typed, def_id)
            {
                return Some(json!({
                    "contents": { "kind": "markdown", "value": format!("```ril\n{info}\n```") }
                }));
            }
        }

        // 3. Fallback: smallest expression span containing the offset in `typed.types`.
        let best = typed
            .types
            .iter()
            .filter(|(span, _)| span.file == file_id && offset >= span.start && offset <= span.end)
            .min_by_key(|(span, _)| span.end.saturating_sub(span.start));
        if let Some((_, ty)) = best {
            let rendered = ty.display(&typed.hir).to_string();
            return Some(json!({
                "contents": { "kind": "markdown", "value": format!("```ril\n{rendered}\n```") }
            }));
        }
        None
    }

    fn definition(&self, params: &Value) -> Option<Value> {
        let uri = params.pointer("/textDocument/uri")?.as_str()?;
        let line = usize::try_from(params.pointer("/position/line")?.as_u64()?).ok()?;
        let character = usize::try_from(params.pointer("/position/character")?.as_u64()?).ok()?;
        let text = self.documents.get(uri)?;
        let offset = line_col_to_offset(text, line, character)?;
        let (pkg, logical) = self.build_package(uri)?;
        let (typed, _) = self.compiler.analyze_cached(&pkg).ok()?;
        let file = typed.hir.files().find(|f| f.path == logical)?;
        let file_id = file.id;

        let target_id = typed
            .hir
            .resolutions()
            .filter(|(span, _)| span.file == file_id && offset >= span.start && offset <= span.end)
            .min_by_key(|(span, _)| span.end.saturating_sub(span.start))
            .and_then(|(_, res)| match *res {
                Resolution::Definition(id) => Some(id),
                _ => None,
            })?;
        let def = typed.hir.definition(target_id);
        let target_file = typed.hir.file(def.name.span.file);
        let range = span_to_file_range(target_file.source(), def.name.span)?;
        let target_uri = self
            .documents
            .keys()
            .find(|u| uri_to_logical_path(u) == target_file.path)
            .cloned()
            .unwrap_or_else(|| uri.to_owned());
        Some(json!({
            "uri": target_uri,
            "range": range
        }))
    }

    fn formatting(&self, params: &Value) -> Option<Value> {
        let uri = params.pointer("/textDocument/uri")?.as_str()?;
        let text = self.documents.get(uri)?;
        let logical = uri_to_logical_path(uri);
        let kind = if text.contains("fn main") {
            FileKind::Executable
        } else {
            FileKind::Module
        };
        let source =
            SourceFile::from_bytes(FileId::from_path(&logical), logical, text.as_bytes()).ok()?;
        let formatted = fmt::format_source(&source, kind).ok()?;
        let end_line = text.lines().count();
        Some(json!([{
            "range": {
                "start": { "line": 0, "character": 0 },
                "end": { "line": end_line + 1, "character": 0 }
            },
            "newText": formatted
        }]))
    }
}

fn describe_definition(
    typed: &ril_sema::ty::TypedProgram,
    id: ril_hir::DefinitionId,
) -> Option<String> {
    let def = typed.hir.definition(id);
    if let Some(callable) = typed.callables.get(&id) {
        let ty = Ty::Callable(callable.clone())
            .display(&typed.hir)
            .to_string();
        let sig = ty
            .strip_prefix("fn")
            .map_or_else(|| ty.clone(), |rest| format!("fn {}{rest}", def.name.value));
        return Some(sig);
    }
    if let Some(ty) = typed.bindings.get(&id) {
        return Some(format!("{}: {}", def.name.value, ty.display(&typed.hir)));
    }
    None
}

fn uri_to_logical_path(uri: &str) -> PathBuf {
    let stripped = uri.strip_prefix("file://").unwrap_or(uri);
    let file_name = Path::new(stripped)
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("main.ril");
    Path::new("pkg").join(file_name)
}

fn line_col_to_offset(text: &str, target_line: usize, target_col: usize) -> Option<usize> {
    let mut line = 0usize;
    let mut col = 0usize;
    for (idx, ch) in text.char_indices() {
        if line == target_line && col == target_col {
            return Some(idx);
        }
        if ch == '\n' {
            if line == target_line {
                return Some(idx);
            }
            line += 1;
            col = 0;
        } else {
            col += 1;
        }
    }
    (line == target_line).then_some(text.len())
}

fn span_to_lsp_range(sources: &ril_source::span::SourceMap, span: Span) -> Option<Value> {
    let file = sources.get(span.file)?;
    span_to_file_range(file, span)
}

fn span_to_file_range(file: &SourceFile, span: Span) -> Option<Value> {
    let start = file.location(span.start)?;
    let end = file.location(span.end).unwrap_or(start);
    Some(json!({
        "start": { "line": start.line.saturating_sub(1), "character": start.column.saturating_sub(1) },
        "end": { "line": end.line.saturating_sub(1), "character": end.column.saturating_sub(1) }
    }))
}

fn zero_range() -> Value {
    json!({
        "start": { "line": 0, "character": 0 },
        "end": { "line": 0, "character": 0 }
    })
}

fn read_message<R: BufRead>(reader: &mut R) -> Result<Option<Value>, String> {
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

fn write_message<W: Write>(writer: &mut W, value: &Value) -> Result<(), String> {
    let body = serde_json::to_vec(value).map_err(|e| e.to_string())?;
    write!(writer, "Content-Length: {}\r\n\r\n", body.len()).map_err(|e| e.to_string())?;
    writer.write_all(&body).map_err(|e| e.to_string())?;
    writer.flush().map_err(|e| e.to_string())
}
