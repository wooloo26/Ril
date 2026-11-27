#![forbid(unsafe_code)]

//! JSON-RPC 2.0 Language Server (`ril lsp`) powered by incremental `Compiler`.
//!
//! Features:
//! - Live `ril.toml` workspace & `std/*.ril` resolution (zero false bodyless errors on stdlib)
//! - Fault-tolerant partial analysis (`publishDiagnostics` + cached `TypedProgram`)
//! - First-parameter-driven pipeline auto-suggestion (`|>`, `|?>`, and optional dot-to-pipe `.`)
//! - Context-aware completion, pipeline-aware signature help, and rich hover with doc comments
//! - TypeScript-Monokai-aligned semantic tokens (`textDocument/semanticTokens/full`)
//! - Go-to-definition, find references, safe rename, document/workspace symbols, inlay hints,
//!   quick-fix code actions, and formatting.

mod analysis;
mod code_actions;
mod completion;
mod hover;
mod inlay_hints;
mod navigation;
mod pipeline;
mod protocol;
mod semantic_tokens;
mod symbols;
mod workspace;

use std::{
    io::{self, BufRead, Write},
    path::PathBuf,
};

use ril_source::{
    diag::Severity,
    span::{FileId, SourceFile},
};
use ril_syntax::{fmt, parser::FileKind};
use serde_json::{Value, json};

use crate::{
    analysis::LspState,
    protocol::{
        read_message, span_to_lsp_range, uri_to_fs_path, uri_to_logical_path, write_message,
        zero_range,
    },
};

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
                if let Some(root_uri) = params.get("rootUri").and_then(Value::as_str) {
                    state.workspace_root = uri_to_fs_path(root_uri);
                } else if let Some(root_path) = params.get("rootPath").and_then(Value::as_str) {
                    state.workspace_root = Some(PathBuf::from(root_path));
                }
                if let Some(opts) = params.get("initializationOptions") {
                    apply_config(&mut state, opts);
                }
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
                                    "referencesProvider": true,
                                    "renameProvider": { "prepareProvider": true },
                                    "documentSymbolProvider": true,
                                    "workspaceSymbolProvider": true,
                                    "documentFormattingProvider": true,
                                    "completionProvider": {
                                        "triggerCharacters": [".", ":", ">", "/", "@"]
                                    },
                                    "signatureHelpProvider": {
                                        "triggerCharacters": ["(", ","]
                                    },
                                    "semanticTokensProvider": {
                                        "legend": semantic_tokens::legend_json(),
                                        "full": true
                                    },
                                    "inlayHintProvider": true,
                                    "codeActionProvider": {
                                        "codeActionKinds": ["quickfix"]
                                    }
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
            "workspace/didChangeConfiguration" => {
                if let Some(settings) = params.get("settings") {
                    let ril_cfg = settings.get("ril").unwrap_or(settings);
                    apply_config(&mut state, ril_cfg);
                }
            }
            "textDocument/didOpen" => {
                if let Some(doc) = params.get("textDocument")
                    && let (Some(uri), Some(text)) = (
                        doc.get("uri").and_then(Value::as_str),
                        doc.get("text").and_then(Value::as_str),
                    )
                {
                    state.documents.insert(uri.to_owned(), text.to_owned());
                    let notif = publish_diagnostics(&mut state, uri);
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
                    let notif = publish_diagnostics(&mut state, uri);
                    write_message(&mut writer, &notif)?;
                }
            }
            "textDocument/didClose" => {
                if let Some(uri) = params.pointer("/textDocument/uri").and_then(Value::as_str) {
                    state.documents.remove(uri);
                    state.cache.remove(uri);
                }
            }
            "textDocument/hover" => {
                if let Some(id) = id {
                    let result = hover::hover(&mut state, &params).unwrap_or(Value::Null);
                    write_message(
                        &mut writer,
                        &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                    )?;
                }
            }
            "textDocument/signatureHelp" => {
                if let Some(id) = id {
                    let result = hover::signature_help(&mut state, &params).unwrap_or(Value::Null);
                    write_message(
                        &mut writer,
                        &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                    )?;
                }
            }
            "textDocument/completion" => {
                if let Some(id) = id {
                    let result = completion::complete(&mut state, &params);
                    write_message(
                        &mut writer,
                        &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                    )?;
                }
            }
            "textDocument/semanticTokens/full" => {
                if let Some(id) = id {
                    let result = semantic_tokens::semantic_tokens_full(&mut state, &params);
                    write_message(
                        &mut writer,
                        &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                    )?;
                }
            }
            "textDocument/definition" => {
                if let Some(id) = id {
                    let result = navigation::definition(&mut state, &params).unwrap_or(Value::Null);
                    write_message(
                        &mut writer,
                        &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                    )?;
                }
            }
            "textDocument/references" => {
                if let Some(id) = id {
                    let result = navigation::references(&mut state, &params);
                    write_message(
                        &mut writer,
                        &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                    )?;
                }
            }
            "textDocument/prepareRename" => {
                if let Some(id) = id {
                    let result =
                        navigation::prepare_rename(&mut state, &params).unwrap_or(Value::Null);
                    write_message(
                        &mut writer,
                        &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                    )?;
                }
            }
            "textDocument/rename" => {
                if let Some(id) = id {
                    let result = navigation::rename(&mut state, &params).unwrap_or(Value::Null);
                    write_message(
                        &mut writer,
                        &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                    )?;
                }
            }
            "textDocument/documentSymbol" => {
                if let Some(id) = id {
                    let result = symbols::document_symbols(&mut state, &params);
                    write_message(
                        &mut writer,
                        &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                    )?;
                }
            }
            "workspace/symbol" => {
                if let Some(id) = id {
                    let result = symbols::workspace_symbols(&mut state, &params);
                    write_message(
                        &mut writer,
                        &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                    )?;
                }
            }
            "textDocument/inlayHint" => {
                if let Some(id) = id {
                    let result = inlay_hints::inlay_hints(&mut state, &params);
                    write_message(
                        &mut writer,
                        &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                    )?;
                }
            }
            "textDocument/codeAction" => {
                if let Some(id) = id {
                    let result = code_actions::code_actions(&state, &params);
                    write_message(
                        &mut writer,
                        &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                    )?;
                }
            }
            "textDocument/formatting" => {
                if let Some(id) = id {
                    let result = formatting(&state, &params).unwrap_or_else(|| json!([]));
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

fn apply_config(state: &mut LspState, opts: &Value) {
    if let Some(v) = opts
        .pointer("/completion/dotToPipe")
        .and_then(Value::as_bool)
    {
        state.config.dot_to_pipe = v;
    } else if let Some(v) = opts.get("dotToPipe").and_then(Value::as_bool) {
        state.config.dot_to_pipe = v;
    }
    if let Some(v) = opts
        .pointer("/completion/autoImport")
        .and_then(Value::as_bool)
    {
        state.config.auto_import = v;
    } else if let Some(v) = opts.get("autoImport").and_then(Value::as_bool) {
        state.config.auto_import = v;
    }
    if let Some(v) = opts.pointer("/inlayHints/enable").and_then(Value::as_bool) {
        state.config.inlay_hints = v;
    } else if let Some(v) = opts.get("inlayHints").and_then(Value::as_bool) {
        state.config.inlay_hints = v;
    }
}

fn publish_diagnostics(state: &mut LspState, uri: &str) -> Value {
    let mut diagnostics = Vec::new();
    if let Some((ws, partial)) = state.refresh_document(uri) {
        let entry_file_id = FileId::from_path(&ws.entry_logical);
        for diag in &partial.diagnostics {
            // Only publish diagnostics belonging to the active file (or unspanned entry errors)
            // so errors in sibling modules don't pollute unrelated line numbers in `uri`.
            if let Some(span) = diag.primary
                && span.file != entry_file_id
            {
                continue;
            }
            let range = diag
                .primary
                .and_then(|span| span_to_lsp_range(&partial.sources, span))
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
            if !diag.labels().is_empty()
                && let Some(obj) = item.as_object_mut()
            {
                let related: Vec<Value> = diag
                    .labels()
                    .iter()
                    .filter_map(|label| {
                        let range = span_to_lsp_range(&partial.sources, label.span)?;
                        Some(json!({
                            "location": { "uri": uri, "range": range },
                            "message": label.message
                        }))
                    })
                    .collect();
                if !related.is_empty() {
                    obj.insert("relatedInformation".into(), json!(related));
                }
            }
            diagnostics.push(item);
        }
        if let Some(ref analysis) = partial.analysis {
            for warn in ril_driver::inspect::defer_warnings_for_file(analysis, entry_file_id) {
                let range =
                    span_to_lsp_range(&partial.sources, warn.defer_span).unwrap_or_else(zero_range);
                let mut item = json!({
                    "range": range,
                    "severity": 2,
                    "code": "W0601",
                    "source": "ril",
                    "message": "defer cleanup may panic; a panic during unwinding aborts the process and bypasses Panic::recover"
                });
                if let Some(scope_span) = warn.scope_panic_span
                    && let Some(scope_range) = span_to_lsp_range(&partial.sources, scope_span)
                    && let Some(obj) = item.as_object_mut()
                {
                    obj.insert(
                        "relatedInformation".into(),
                        json!([{
                            "location": { "uri": uri, "range": scope_range },
                            "message": warn
                                .scope_panic_detail
                                .as_deref()
                                .unwrap_or("enclosing scope may panic here")
                        }]),
                    );
                }
                diagnostics.push(item);
            }
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

fn formatting(state: &LspState, params: &Value) -> Option<Value> {
    let uri = params.pointer("/textDocument/uri")?.as_str()?;
    let text = state.documents.get(uri)?;
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
