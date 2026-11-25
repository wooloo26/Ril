use std::collections::{BTreeMap, BTreeSet};

use ril_hir::{DefinitionId, DefinitionKind};
use ril_sema::ty::TypedProgram;
use ril_source::span::{FileId, Span};
use serde_json::{Value, json};

use crate::{
    analysis::LspState,
    protocol::{extract_position, line_col_to_offset, span_to_file_range},
    workspace::{WorkspacePackage, logical_path_to_uri},
};

pub(crate) fn definition(state: &mut LspState, params: &Value) -> Option<Value> {
    let (uri, line, character) = extract_position(params)?;
    let text = state.documents.get(uri)?.clone();
    let offset = line_col_to_offset(&text, line, character)?;
    let (ws, typed) = state.best_typed(uri)?;
    let file = typed.hir.files().find(|f| f.path == ws.entry_logical)?;
    let file_id = file.id;

    let res = typed
        .hir
        .resolutions()
        .filter(|(span, _)| span.file == file_id && offset >= span.start && offset <= span.end)
        .min_by_key(|(span, _)| span.end.saturating_sub(span.start))
        .map(|(_, r)| *r)?;

    if let Some(target_id) = res.definition() {
        let def = typed.hir.definition(target_id);
        if def.name.span.file == FileId::BUILTIN {
            return None;
        }
        let target_file = typed.hir.file(def.name.span.file);
        let range = span_to_file_range(target_file.source(), def.name.span)?;
        let target_uri =
            logical_path_to_uri(state.workspace_root.as_deref(), &ws, &target_file.path, uri);
        return Some(json!({ "uri": target_uri, "range": range }));
    }

    if let Some(mod_scope) = res.module() {
        let target_file_id = typed.hir.scope_file(mod_scope);
        if target_file_id == FileId::BUILTIN {
            return None;
        }
        let target_file = typed.hir.file(target_file_id);
        let target_uri =
            logical_path_to_uri(state.workspace_root.as_deref(), &ws, &target_file.path, uri);
        return Some(json!({
            "uri": target_uri,
            "range": {
                "start": { "line": 0, "character": 0 },
                "end": { "line": 0, "character": 0 }
            }
        }));
    }

    None
}

pub(crate) fn references(state: &mut LspState, params: &Value) -> Value {
    let Some((uri, line, character)) = extract_position(params) else {
        return json!([]);
    };
    let include_decl = params
        .pointer("/context/includeDeclaration")
        .and_then(Value::as_bool)
        .unwrap_or(true);
    let Some(text) = state.documents.get(uri).cloned() else {
        return json!([]);
    };
    let Some(offset) = line_col_to_offset(&text, line, character) else {
        return json!([]);
    };
    let Some((ws, typed)) = state.best_typed(uri) else {
        return json!([]);
    };
    let Some(file) = typed.hir.files().find(|f| f.path == ws.entry_logical) else {
        return json!([]);
    };
    let Some(target_id) = symbol_under_cursor(&typed, file.id, offset) else {
        return json!([]);
    };

    let spans = collect_symbol_spans(&typed, target_id, include_decl);
    let locations: Vec<Value> = spans
        .into_iter()
        .filter_map(|span| {
            let f = typed.hir.file(span.file);
            let range = span_to_file_range(f.source(), span)?;
            let target_uri =
                logical_path_to_uri(state.workspace_root.as_deref(), &ws, &f.path, uri);
            Some(json!({ "uri": target_uri, "range": range }))
        })
        .collect();
    json!(locations)
}

pub(crate) fn prepare_rename(state: &mut LspState, params: &Value) -> Option<Value> {
    let (uri, line, character) = extract_position(params)?;
    let text = state.documents.get(uri)?.clone();
    let offset = line_col_to_offset(&text, line, character)?;
    let (ws, typed) = state.best_typed(uri)?;
    let file = typed.hir.files().find(|f| f.path == ws.entry_logical)?;
    let (target_id, hit_span) = symbol_and_span_under_cursor(&typed, file.id, offset)?;
    if !is_renameable(&typed, target_id) {
        return None;
    }
    let name_span = trailing_ident_span(file.source_text(), hit_span);
    let range = span_to_file_range(file.source(), name_span)?;
    let placeholder = typed.hir.definition(target_id).name.value.clone();
    Some(json!({ "range": range, "placeholder": placeholder }))
}

pub(crate) fn rename(state: &mut LspState, params: &Value) -> Option<Value> {
    let (uri, line, character) = extract_position(params)?;
    let new_name = params.get("newName")?.as_str()?;
    if new_name.is_empty()
        || !new_name
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_')
    {
        return None;
    }
    let text = state.documents.get(uri)?.clone();
    let offset = line_col_to_offset(&text, line, character)?;
    let (ws, typed) = state.best_typed(uri)?;
    let file = typed.hir.files().find(|f| f.path == ws.entry_logical)?;
    let target_id = symbol_under_cursor(&typed, file.id, offset)?;
    if !is_renameable(&typed, target_id) {
        return None;
    }

    let spans = collect_symbol_spans(&typed, target_id, true);
    let changes = build_rename_changes(
        state.workspace_root.as_deref(),
        &ws,
        &typed,
        uri,
        spans,
        new_name,
    );
    Some(json!({ "changes": changes }))
}

fn is_renameable(typed: &TypedProgram, id: DefinitionId) -> bool {
    let def = typed.hir.definition(id);
    def.name.span.file != FileId::BUILTIN
        && !typed.hir.is_stdlib_file(def.name.span.file)
        && !matches!(def.kind, DefinitionKind::Primitive(_))
}

fn symbol_under_cursor(
    typed: &TypedProgram,
    file_id: FileId,
    offset: usize,
) -> Option<DefinitionId> {
    symbol_and_span_under_cursor(typed, file_id, offset).map(|(id, _)| id)
}

fn symbol_and_span_under_cursor(
    typed: &TypedProgram,
    file_id: FileId,
    offset: usize,
) -> Option<(DefinitionId, Span)> {
    for (id, def) in typed.hir.definitions() {
        if def.name.span.file == file_id
            && offset >= def.name.span.start
            && offset <= def.name.span.end
        {
            return Some((id, def.name.span));
        }
    }
    typed
        .hir
        .resolutions()
        .filter(|(span, _)| span.file == file_id && offset >= span.start && offset <= span.end)
        .min_by_key(|(span, _)| span.end.saturating_sub(span.start))
        .and_then(|(span, res)| res.definition().map(|id| (id, *span)))
}

fn collect_symbol_spans(
    typed: &TypedProgram,
    target_id: DefinitionId,
    include_decl: bool,
) -> Vec<Span> {
    let mut seen: BTreeSet<(usize, usize, usize)> = BTreeSet::new();
    let mut out = Vec::new();
    let def = typed.hir.definition(target_id);
    if include_decl && def.name.span.file != FileId::BUILTIN {
        let s = def.name.span;
        if seen.insert((s.file.0, s.start, s.end)) {
            out.push(s);
        }
    }
    for (span, res) in typed.hir.resolutions() {
        if span.file == FileId::BUILTIN || typed.hir.is_stdlib_file(span.file) {
            continue;
        }
        if res.definition() == Some(target_id) {
            let file = typed.hir.file(span.file);
            let ident_span = trailing_ident_span(file.source_text(), *span);
            if !include_decl && ident_span == def.name.span {
                continue;
            }
            if seen.insert((ident_span.file.0, ident_span.start, ident_span.end)) {
                out.push(ident_span);
            }
        }
    }
    out
}

fn trailing_ident_span(text: &str, span: Span) -> Span {
    if let Some(slice) = text.get(span.start..span.end)
        && let Some(idx) = slice.rfind("::")
    {
        return Span::new(span.file, span.start + idx + 2, span.end);
    }
    span
}

fn build_rename_changes(
    workspace_root: Option<&std::path::Path>,
    ws: &WorkspacePackage,
    typed: &TypedProgram,
    active_uri: &str,
    spans: Vec<Span>,
    new_name: &str,
) -> BTreeMap<String, Vec<Value>> {
    let mut changes: BTreeMap<String, Vec<Value>> = BTreeMap::new();
    for span in spans {
        let file = typed.hir.file(span.file);
        if let Some(range) = span_to_file_range(file.source(), span) {
            let target_uri = logical_path_to_uri(workspace_root, ws, &file.path, active_uri);
            changes.entry(target_uri).or_default().push(json!({
                "range": range,
                "newText": new_name
            }));
        }
    }
    changes
}
