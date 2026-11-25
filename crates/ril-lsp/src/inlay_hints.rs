use ril_sema::ty::Ty;
use ril_syntax::syntax::{Expr, Pattern, StmtKind};
use serde_json::{Value, json};

use crate::{
    analysis::LspState,
    protocol::{line_col_to_offset, offset_to_line_col},
};

pub(crate) fn inlay_hints(state: &mut LspState, params: &Value) -> Value {
    if !state.config.inlay_hints {
        return json!([]);
    }
    let Some(uri) = params.pointer("/textDocument/uri").and_then(Value::as_str) else {
        return json!([]);
    };
    let Some(text) = state.documents.get(uri).cloned() else {
        return json!([]);
    };
    let (range_start, range_end) = parse_request_range(&text, params).unwrap_or((0, text.len()));
    let Some((ws, typed)) = state.best_typed(uri) else {
        return json!([]);
    };
    let Some(file) = typed.hir.files().find(|f| f.path == ws.entry_logical) else {
        return json!([]);
    };

    let mut hints = Vec::new();

    // 1. Inferred types on unannotated `let` / `var` bindings.
    for stmt in file.ast.statements() {
        if stmt.span.end < range_start || stmt.span.start > range_end {
            continue;
        }
        if let StmtKind::Binding {
            pattern,
            ty: None,
            value: Some(_),
            ..
        } = &stmt.value.kind
            && let Pattern::Binding(_, name) = &file.ast.pattern(*pattern).value
            && name.value != "_"
            && let Some(def_id) = typed.hir.resolve(name.span).and_then(|r| r.definition())
            && let Some(inferred) = typed.bindings.get(&def_id)
            && !matches!(inferred, Ty::Unknown | Ty::Infer(_) | Ty::Unit)
        {
            let rendered = inferred.display(&typed.hir).to_string();
            if rendered.len() <= 48 {
                let (line, col) = offset_to_line_col(&text, name.span.end);
                hints.push(json!({
                    "position": { "line": line, "character": col },
                    "label": format!(": {rendered}"),
                    "kind": 1, // Type
                    "paddingLeft": false,
                    "paddingRight": true
                }));
            }
        }
    }

    // 2. Inferred types on unannotated closure parameters (`\x -> ...`).
    for expr in file.ast.expressions() {
        if expr.span.end < range_start || expr.span.start > range_end {
            continue;
        }
        if let Expr::Closure { params, .. } = &expr.value {
            for p in params {
                if p.ty.is_some() {
                    continue;
                }
                if let Some(name) = &p.name
                    && name.value != "_"
                    && let Some(def_id) = typed.hir.resolve(name.span).and_then(|r| r.definition())
                    && let Some(inferred) = typed.bindings.get(&def_id)
                    && !matches!(inferred, Ty::Unknown | Ty::Infer(_))
                {
                    let rendered = inferred.display(&typed.hir).to_string();
                    if rendered.len() <= 36 {
                        let (line, col) = offset_to_line_col(&text, name.span.end);
                        hints.push(json!({
                            "position": { "line": line, "character": col },
                            "label": format!(": {rendered}"),
                            "kind": 1, // Type
                            "paddingLeft": false,
                            "paddingRight": false
                        }));
                    }
                }
            }
        }
    }

    json!(hints)
}

fn parse_request_range(text: &str, params: &Value) -> Option<(usize, usize)> {
    let sl = usize::try_from(params.pointer("/range/start/line")?.as_u64()?).ok()?;
    let sc = usize::try_from(params.pointer("/range/start/character")?.as_u64()?).ok()?;
    let el = usize::try_from(params.pointer("/range/end/line")?.as_u64()?).ok()?;
    let ec = usize::try_from(params.pointer("/range/end/character")?.as_u64()?).ok()?;
    let start = line_col_to_offset(text, sl, sc)?;
    let end = line_col_to_offset(text, el, ec)?;
    Some((start, end))
}
