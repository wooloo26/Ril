use ril_hir::{DefinitionKind, File};
use ril_source::span::FileId;
use ril_syntax::syntax::{Pattern, StmtId, StmtKind, TypeDefinition, Variant};
use serde_json::{Value, json};

use crate::{analysis::LspState, protocol::span_to_file_range, workspace::logical_path_to_uri};

pub(crate) fn document_symbols(state: &mut LspState, params: &Value) -> Value {
    let Some(uri) = params.pointer("/textDocument/uri").and_then(Value::as_str) else {
        return json!([]);
    };
    let Some((ws, typed)) = state.best_typed(uri) else {
        return json!([]);
    };
    let Some(file) = typed.hir.files().find(|f| f.path == ws.entry_logical) else {
        return json!([]);
    };
    let symbols = collect_stmt_symbols(file, &file.ast.items);
    json!(symbols)
}

fn collect_stmt_symbols(file: &File, items: &[StmtId]) -> Vec<Value> {
    let mut out = Vec::new();
    for &stmt_id in items {
        let node = file.ast.stmt(stmt_id);
        let Some(full_range) = span_to_file_range(file.source(), node.span) else {
            continue;
        };
        match &node.value.kind {
            StmtKind::Function(fun) => {
                let sel = span_to_file_range(file.source(), fun.name.span)
                    .unwrap_or_else(|| full_range.clone());
                let detail = if fun.is_meta { "meta fn" } else { "fn" };
                out.push(json!({
                    "name": fun.name.value,
                    "detail": detail,
                    "kind": 12, // Function
                    "range": full_range,
                    "selectionRange": sel,
                    "children": []
                }));
            }
            StmtKind::Type(decl) => {
                let sel = span_to_file_range(file.source(), decl.name.span)
                    .unwrap_or_else(|| full_range.clone());
                let (kind, children) = match &decl.definition {
                    TypeDefinition::Sum(variants) => {
                        let kids: Vec<Value> = variants
                            .iter()
                            .filter_map(|v| match v {
                                Variant::Constructor { name, .. } => {
                                    let vr = span_to_file_range(file.source(), name.span)?;
                                    Some(json!({
                                        "name": name.value,
                                        "kind": 22, // EnumMember
                                        "range": vr,
                                        "selectionRange": vr
                                    }))
                                }
                                _ => None,
                            })
                            .collect();
                        (10, kids) // Enum
                    }
                    TypeDefinition::Data(ty_id) => {
                        let kids = match &file.ast.ty(*ty_id).value {
                            ril_syntax::syntax::Type::Record { fields, .. } => fields
                                .iter()
                                .filter_map(|f| {
                                    let fr = span_to_file_range(file.source(), f.name.span)?;
                                    Some(json!({
                                        "name": f.name.value,
                                        "kind": 8, // Field
                                        "range": fr,
                                        "selectionRange": fr
                                    }))
                                })
                                .collect(),
                            _ => Vec::new(),
                        };
                        (23, kids) // Struct
                    }
                    _ => (23, Vec::new()),
                };
                out.push(json!({
                    "name": decl.name.value,
                    "kind": kind,
                    "range": full_range,
                    "selectionRange": sel,
                    "children": children
                }));
            }
            StmtKind::Effect {
                name, operations, ..
            } => {
                let sel = span_to_file_range(file.source(), name.span)
                    .unwrap_or_else(|| full_range.clone());
                let children = collect_stmt_symbols(file, operations);
                out.push(json!({
                    "name": name.value,
                    "detail": "eff",
                    "kind": 11, // Interface
                    "range": full_range,
                    "selectionRange": sel,
                    "children": children
                }));
            }
            StmtKind::Sub { name, items } => {
                let sel = span_to_file_range(file.source(), name.span)
                    .unwrap_or_else(|| full_range.clone());
                let children = collect_stmt_symbols(file, items);
                out.push(json!({
                    "name": name.value,
                    "detail": "sub",
                    "kind": 2, // Module
                    "range": full_range,
                    "selectionRange": sel,
                    "children": children
                }));
            }
            StmtKind::Binding {
                pattern, is_meta, ..
            } => {
                if let Pattern::Binding(_, name) = &file.ast.pattern(*pattern).value {
                    let sel = span_to_file_range(file.source(), name.span)
                        .unwrap_or_else(|| full_range.clone());
                    out.push(json!({
                        "name": name.value,
                        "detail": if *is_meta { "meta let" } else { "let" },
                        "kind": 14, // Constant
                        "range": full_range,
                        "selectionRange": sel
                    }));
                }
            }
            _ => {}
        }
    }
    out
}

pub(crate) fn workspace_symbols(state: &mut LspState, params: &Value) -> Value {
    let query = params
        .get("query")
        .and_then(Value::as_str)
        .unwrap_or("")
        .to_ascii_lowercase();
    let Some(active_uri) = state.documents.keys().next().cloned() else {
        return json!([]);
    };
    let Some((ws, typed)) = state.best_typed(&active_uri) else {
        return json!([]);
    };

    let mut out = Vec::new();
    for (_, def) in typed.hir.definitions() {
        if def.name.span.file == FileId::BUILTIN || typed.hir.is_stdlib_file(def.name.span.file) {
            continue;
        }
        let kind = match def.kind {
            DefinitionKind::Function => 12,
            DefinitionKind::Type => 23,
            DefinitionKind::Sum(_) => 10,
            DefinitionKind::Variant(_) => 22,
            DefinitionKind::Effect(_) => 11,
            DefinitionKind::Namespace(_) => 2,
            DefinitionKind::Constant => 14,
            _ => continue,
        };
        if !query.is_empty() && !def.name.value.to_ascii_lowercase().contains(&query) {
            continue;
        }
        let file = typed.hir.file(def.name.span.file);
        if let Some(range) = span_to_file_range(file.source(), def.name.span) {
            let target_uri = logical_path_to_uri(
                state.workspace_root.as_deref(),
                &ws,
                &file.path,
                &active_uri,
            );
            out.push(json!({
                "name": def.name.value,
                "kind": kind,
                "location": { "uri": target_uri, "range": range }
            }));
        }
    }
    json!(out)
}
