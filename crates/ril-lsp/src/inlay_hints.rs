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
    let Some((ws, typed, analysis)) = state.best_analysis(uri) else {
        return json!([]);
    };
    let Some(file) = typed.hir.files().find(|f| f.path == ws.entry_logical) else {
        return json!([]);
    };

    let mut hints = Vec::new();

    // 1. Inferred types on unannotated `let` / `var` bindings (skip trivial literal RHS to cut noise).
    for stmt in file.ast.statements() {
        if stmt.span.end < range_start || stmt.span.start > range_end {
            continue;
        }
        match &stmt.value.kind {
            StmtKind::Binding {
                pattern,
                ty: None,
                value: Some(val_id),
                ..
            } => {
                if matches!(file.ast.expr(*val_id).value, Expr::Literal(_) | Expr::Unit) {
                    continue;
                }
                if let Pattern::Binding(_, name) = &file.ast.pattern(*pattern).value
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
            // 2. Expand ambiguous bare `&mut` on functions with >=2 parameters.
            StmtKind::Function(function) => {
                if let Some(analysis) = analysis.as_deref()
                    && function.signature.params.len() >= 2
                    && let Some(def_id) = typed
                        .hir
                        .resolve(function.name.span)
                        .and_then(|r| r.definition())
                {
                    let (mut_params, _) =
                        ril_driver::inspect::expanded_mut_params(&typed, analysis, def_id);
                    if !mut_params.is_empty() {
                        let header_end = function
                            .body
                            .map_or(stmt.span.end, |b| file.ast.expr(b).span.start);
                        if let Some(header) = text.get(function.name.span.end..header_end)
                            && let Some(pos) = find_bare_mut_clause(header)
                        {
                            let abs = function.name.span.end + pos + 4;
                            let (line, col) = offset_to_line_col(&text, abs);
                            hints.push(json!({
                                "position": { "line": line, "character": col },
                                "label": format!("({})", mut_params.join(", ")),
                                "kind": 2, // Parameter
                                "paddingLeft": false,
                                "paddingRight": false
                            }));
                        }
                    }
                }
            }
            _ => {}
        }
    }

    // 3. Inferred types on unannotated closure parameters + non-pure closure effect/capture tail.
    for expr in file.ast.expressions() {
        if expr.span.end < range_start || expr.span.start > range_end {
            continue;
        }
        if let Expr::Closure { params, body, .. } = &expr.value {
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
            if let Some(analysis) = analysis.as_deref()
                && let Some(closure) = analysis
                    .behavior
                    .closures
                    .iter()
                    .find(|c| c.span == expr.span)
            {
                let mut tail_parts = Vec::new();
                for eff in &closure.effect_ops {
                    tail_parts.push(eff.clone());
                }
                if !closure.captures.is_empty() {
                    tail_parts.push(format!("&up({})", closure.captures.join(", ")));
                }
                if !tail_parts.is_empty() {
                    let body_start = file.ast.expr(*body).span.start;
                    if let Some(head) = text.get(expr.span.start..body_start)
                        && let Some(arrow_rel) = head.rfind("->")
                    {
                        let abs = expr.span.start + arrow_rel;
                        let (line, col) = offset_to_line_col(&text, abs);
                        hints.push(json!({
                            "position": { "line": line, "character": col },
                            "label": format!("{} ", tail_parts.join(" ")),
                            "kind": 1,
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

fn find_bare_mut_clause(header: &str) -> Option<usize> {
    let bytes = header.as_bytes();
    let mut i = 0;
    while i + 4 <= bytes.len() {
        if bytes.get(i..i + 4) == Some(b"&mut") {
            let next = bytes.get(i + 4).copied();
            if !matches!(
                next,
                Some(b'(' | b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_')
            ) {
                return Some(i);
            }
        }
        i += 1;
    }
    None
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
