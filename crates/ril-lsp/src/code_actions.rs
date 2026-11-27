use std::collections::HashSet;

use ril_source::fix::{Fix, TextEdit};
use serde_json::{Value, json};

use crate::{
    analysis::LspState,
    protocol::{import_insert_line, span_to_lsp_range},
    workspace::STD_MODULES,
};

pub(crate) fn code_actions(state: &LspState, params: &Value) -> Value {
    let Some(uri) = params.pointer("/textDocument/uri").and_then(Value::as_str) else {
        return json!([]);
    };
    let Some(text) = state.documents.get(uri) else {
        return json!([]);
    };
    let diags = params
        .pointer("/context/diagnostics")
        .and_then(Value::as_array)
        .map(Vec::as_slice)
        .unwrap_or(&[]);
    let only_kinds: Vec<&str> = params
        .pointer("/context/only")
        .and_then(Value::as_array)
        .map(|arr| arr.iter().filter_map(Value::as_str).collect())
        .unwrap_or_default();

    let wants_quickfix =
        only_kinds.is_empty() || only_kinds.iter().any(|k| k.starts_with("quickfix"));
    let wants_fix_all = only_kinds
        .iter()
        .any(|k| *k == "source" || *k == "source.fixAll" || *k == "source.fixAll.ril");
    let wants_organize = only_kinds
        .iter()
        .any(|k| *k == "source" || *k == "source.organizeImports");

    let mut actions = Vec::new();
    let mut seen_fix_ids = HashSet::new();
    let insert_line = import_insert_line(text);

    if let Some(cached) = state.cache.get(uri)
        && let Some(sources) = cached.latest_sources.as_ref()
    {
        if wants_quickfix {
            for lsp_diag in diags {
                let lsp_code = lsp_diag.get("code").and_then(Value::as_str);
                let lsp_range = lsp_diag.get("range");
                let lsp_source = lsp_diag.get("source").and_then(Value::as_str);

                // 1. Compiler diagnostic structured fixes.
                if lsp_source != Some("ril-lint") {
                    for diag in &cached.latest_diagnostics {
                        if diag.fixes().is_empty() || diag.code.map(|c| c.as_str()) != lsp_code {
                            continue;
                        }
                        let diag_range = diag
                            .primary
                            .and_then(|span| span_to_lsp_range(sources, span));
                        if diag_range.as_ref() != lsp_range {
                            continue;
                        }
                        for fix in diag.fixes() {
                            if !seen_fix_ids.insert(fix.id.clone()) {
                                continue;
                            }
                            if let Some(action) =
                                fix_to_action(uri, sources, fix, "quickfix", Some(lsp_diag))
                            {
                                actions.push(action);
                            }
                        }
                    }
                }

                // 2. Lint diagnostic structured fixes.
                for ldiag in &cached.latest_lints {
                    if ldiag.fixes.is_empty() || Some(ldiag.rule.as_str()) != lsp_code {
                        continue;
                    }
                    let diag_range = span_to_lsp_range(sources, ldiag.primary);
                    if diag_range.as_ref() != lsp_range {
                        continue;
                    }
                    for fix in &ldiag.fixes {
                        if !seen_fix_ids.insert(fix.id.clone()) {
                            continue;
                        }
                        if let Some(action) =
                            fix_to_action(uri, sources, fix, "quickfix", Some(lsp_diag))
                        {
                            actions.push(action);
                        }
                    }
                }
            }
        }

        // 3. `source.fixAll.ril`: strictly non-widening Tier 1 safe fixes only (safe on save!).
        if wants_fix_all {
            let mut edits: Vec<TextEdit> = Vec::new();
            for diag in &cached.latest_diagnostics {
                for fix in diag.fixes() {
                    if fix.is_non_widening_safe() {
                        edits.extend(fix.edits.iter().cloned());
                    }
                }
            }
            for ldiag in &cached.latest_lints {
                for fix in &ldiag.fixes {
                    if fix.is_non_widening_safe() {
                        edits.extend(fix.edits.iter().cloned());
                    }
                }
            }
            let lsp_edits = non_overlapping_lsp_edits(sources, edits);
            if !lsp_edits.is_empty() {
                actions.push(json!({
                    "title": "Fix all safe Ril issues",
                    "kind": "source.fixAll.ril",
                    "edit": { "changes": { uri: lsp_edits } }
                }));
            }
        }

        // 4. `source.organizeImports`: import cleanup & canonical ordering.
        if wants_organize {
            let mut edits: Vec<TextEdit> = Vec::new();
            for ldiag in &cached.latest_lints {
                for fix in &ldiag.fixes {
                    if fix.is_organize_imports && fix.is_non_widening_safe() {
                        edits.extend(fix.edits.iter().cloned());
                    }
                }
            }
            let lsp_edits = non_overlapping_lsp_edits(sources, edits);
            if !lsp_edits.is_empty() {
                actions.push(json!({
                    "title": "Organize Ril imports",
                    "kind": "source.organizeImports",
                    "edit": { "changes": { uri: lsp_edits } }
                }));
            }
        }
    }

    // Stdlib auto-import quickfix for unresolved module identifiers (E0204 / E0209).
    if wants_quickfix {
        for diag in diags {
            let code = diag.get("code").and_then(Value::as_str).unwrap_or("");
            let msg = diag.get("message").and_then(Value::as_str).unwrap_or("");

            if matches!(code, "E0204" | "E0209")
                && let Some(sym) = msg.strip_prefix("cannot resolve ")
            {
                let sym = sym.trim();
                if let Some(&(stem, pascal)) = STD_MODULES.iter().find(|&&(_, p)| p == sym)
                    && stem != "prelude"
                {
                    let import_stmt = format!("use ril/{stem}\n");
                    if !text.contains(&format!("use ril/{stem}")) {
                        actions.push(json!({
                            "title": format!("Import `ril/{stem}` ({pascal})"),
                            "kind": "quickfix",
                            "isPreferred": true,
                            "diagnostics": [diag],
                            "edit": {
                                "changes": {
                                    uri: [{
                                        "range": {
                                            "start": { "line": insert_line, "character": 0 },
                                            "end": { "line": insert_line, "character": 0 }
                                        },
                                        "newText": import_stmt
                                    }]
                                }
                            }
                        }));
                    }
                }
            }
        }
    }

    json!(actions)
}

fn fix_to_action(
    uri: &str,
    sources: &ril_source::span::SourceMap,
    fix: &Fix,
    kind: &str,
    diag: Option<&Value>,
) -> Option<Value> {
    let edits: Vec<Value> = fix
        .edits
        .iter()
        .filter_map(|edit| {
            let range = span_to_lsp_range(sources, edit.span)?;
            Some(json!({
                "range": range,
                "newText": edit.replacement
            }))
        })
        .collect();
    if edits.is_empty() {
        return None;
    }
    let mut obj = json!({
        "title": fix.title,
        "kind": kind,
        "isPreferred": fix.is_preferred,
        "edit": {
            "changes": {
                uri: edits
            }
        }
    });
    if let (Some(d), Some(map)) = (diag, obj.as_object_mut()) {
        map.insert("diagnostics".into(), json!([d]));
    }
    Some(obj)
}

fn non_overlapping_lsp_edits(
    sources: &ril_source::span::SourceMap,
    mut edits: Vec<TextEdit>,
) -> Vec<Value> {
    edits.sort_by_key(|e| (e.span.start, e.span.end));
    let mut selected: Vec<TextEdit> = Vec::new();
    let mut last_end = 0usize;
    for edit in edits {
        if selected.is_empty() || edit.span.start >= last_end {
            last_end = edit.span.end;
            selected.push(edit);
        }
    }
    selected
        .into_iter()
        .filter_map(|edit| {
            let range = span_to_lsp_range(sources, edit.span)?;
            Some(json!({
                "range": range,
                "newText": edit.replacement
            }))
        })
        .collect()
}
