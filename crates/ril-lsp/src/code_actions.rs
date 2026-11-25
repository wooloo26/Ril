use serde_json::{Value, json};

use crate::{analysis::LspState, protocol::import_insert_line, workspace::STD_MODULES};

pub(crate) fn code_actions(state: &LspState, params: &Value) -> Value {
    let Some(uri) = params.pointer("/textDocument/uri").and_then(Value::as_str) else {
        return json!([]);
    };
    let Some(text) = state.documents.get(uri) else {
        return json!([]);
    };
    let Some(diags) = params
        .pointer("/context/diagnostics")
        .and_then(Value::as_array)
    else {
        return json!([]);
    };

    let mut actions = Vec::new();
    let insert_line = import_insert_line(text);

    for diag in diags {
        let code = diag.get("code").and_then(Value::as_str).unwrap_or("");
        let msg = diag.get("message").and_then(Value::as_str).unwrap_or("");

        // Quick-fix 1: Unresolved stdlib module (e.g. `cannot resolve Fiber` / `File` / `Channel`).
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

        // Quick-fix 2: Missing call-site mode marker (`mut`, `ref`, `^mut`).
        if let Some(start_pos) = diag.pointer("/range/start") {
            let suggested_mode = if msg.contains("requires `mut`") || msg.contains("expected `mut`") {
                Some("mut")
            } else if msg.contains("requires `ref`") || msg.contains("expected `ref`") {
                Some("ref")
            } else if msg.contains("requires `^mut`") || msg.contains("expected `^mut`") {
                Some("^mut")
            } else {
                None
            };
            if let Some(mode) = suggested_mode {
                actions.push(json!({
                    "title": format!("Insert `{mode}` mode marker"),
                    "kind": "quickfix",
                    "diagnostics": [diag],
                    "edit": {
                        "changes": {
                            uri: [{
                                "range": { "start": start_pos, "end": start_pos },
                                "newText": format!("{mode} ")
                            }]
                        }
                    }
                }));
            }
        }
    }

    json!(actions)
}
