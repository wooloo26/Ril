use ril_hir::{DefinitionId, DefinitionKind};
use ril_sema::ty::{Ty, TypedProgram};
use ril_source::span::FileId;
use ril_syntax::syntax::{StmtKind, TypeDefinition};
use serde_json::{Value, json};

use crate::{
    analysis::LspState,
    pipeline::{callable_params_for_sig_help, is_ident_byte},
    protocol::{extract_doc_comment, extract_position, line_col_to_offset, span_to_file_range},
};

pub(crate) fn hover(state: &mut LspState, params: &Value) -> Option<Value> {
    let (uri, line, character) = extract_position(params)?;
    let text = state.documents.get(uri)?.clone();
    let offset = line_col_to_offset(&text, line, character)?;
    let (ws, typed) = state.best_typed(uri)?;
    let file = typed.hir.files().find(|f| f.path == ws.entry_logical)?;
    let file_id = file.id;

    // 1. Direct definition under cursor.
    for (def_id, def) in typed.hir.definitions() {
        if def.name.span.file == file_id
            && offset >= def.name.span.start
            && offset <= def.name.span.end
        {
            let markdown = render_definition_hover(&typed, def_id)?;
            let range = span_to_file_range(file.source(), def.name.span);
            return Some(json!({
                "contents": { "kind": "markdown", "value": markdown },
                "range": range
            }));
        }
    }

    // 2. Resolved identifier reference under cursor (prefer tightest span).
    if let Some((span, res)) = typed
        .hir
        .resolutions()
        .filter(|(span, _)| span.file == file_id && offset >= span.start && offset <= span.end)
        .min_by_key(|(span, _)| span.end.saturating_sub(span.start))
    {
        if let Some(def_id) = res.definition()
            && let Some(markdown) = render_definition_hover(&typed, def_id)
        {
            let range = span_to_file_range(file.source(), *span);
            return Some(json!({
                "contents": { "kind": "markdown", "value": markdown },
                "range": range
            }));
        }
        if let Some(mod_scope) = res.module() {
            let mod_file = typed.hir.file(typed.hir.scope_file(mod_scope));
            let range = span_to_file_range(file.source(), *span);
            return Some(json!({
                "contents": {
                    "kind": "markdown",
                    "value": format!("```ril\nmodule {}\n```", mod_file.path.display())
                },
                "range": range
            }));
        }
    }

    // 3. Fallback: smallest expression span containing the offset in `typed.types`.
    let (span, ty) = typed
        .types
        .iter()
        .filter(|(span, ty)| {
            span.file == file_id
                && !matches!(ty, Ty::Unknown | Ty::Infer(_))
                && offset >= span.start
                && offset <= span.end
        })
        .min_by_key(|(span, _)| span.end.saturating_sub(span.start))?;
    let rendered = ty.display(&typed.hir).to_string();
    let range = span_to_file_range(file.source(), *span);
    Some(json!({
        "contents": { "kind": "markdown", "value": format!("```ril\n{rendered}\n```") },
        "range": range
    }))
}

pub(crate) fn render_definition_hover(typed: &TypedProgram, id: DefinitionId) -> Option<String> {
    let def = typed.hir.definition(id);
    let code_block = if let Some(callable) = typed.callables.get(&id) {
        let ty = Ty::Callable(callable.clone())
            .display(&typed.hir)
            .to_string();
        ty.strip_prefix("fn")
            .map_or_else(|| ty.clone(), |rest| format!("fn {}{rest}", def.name.value))
    } else if let Some(ty) = typed.bindings.get(&id) {
        let kind_prefix = match def.kind {
            DefinitionKind::Constant => "let ",
            DefinitionKind::Local => "",
            _ => "",
        };
        format!("{kind_prefix}{}: {}", def.name.value, ty.display(&typed.hir))
    } else if def.name.span.file != FileId::BUILTIN
        && let Some(stmt) = def.stmt
    {
        let file = typed.hir.file(def.name.span.file);
        match &file.ast.stmt(stmt).value.kind {
            StmtKind::Function(_) => {
                let span = file.ast.stmt(stmt).span;
                file.source_text()
                    .get(span.start..span.end)
                    .and_then(|s| s.lines().next())
                    .map(|l| l.trim().trim_end_matches('{').trim().to_owned())?
            }
            StmtKind::Type(decl) => {
                let span = file.ast.stmt(stmt).span;
                let snippet = file
                    .source_text()
                    .get(span.start..span.end)
                    .unwrap_or(&def.name.value);
                let lines: Vec<&str> = snippet.lines().take(12).collect();
                let mut text = lines.join("\n");
                if snippet.lines().count() > 12 {
                    text.push_str("\n    ...");
                }
                if matches!(decl.definition, TypeDefinition::Sum(_)) && !text.contains('}') {
                    text.push_str("\n}");
                }
                text
            }
            StmtKind::Effect { .. } => format!("eff {}", def.name.value),
            StmtKind::Sub { .. } => format!("sub {}", def.name.value),
            _ => def.name.value.clone(),
        }
    } else {
        match def.kind {
            DefinitionKind::Variant(sum_id) => {
                format!(
                    "{}::{}",
                    typed.hir.definition(sum_id).name.value,
                    def.name.value
                )
            }
            DefinitionKind::Generic => format!("type parameter {}", def.name.value),
            DefinitionKind::Primitive(_) => format!("primitive {}", def.name.value),
            _ => return None,
        }
    };

    let doc = if def.name.span.file != FileId::BUILTIN {
        let file = typed.hir.file(def.name.span.file);
        let decl_start = def
            .stmt
            .map_or(def.name.span.start, |s| file.ast.stmt(s).span.start);
        extract_doc_comment(file.source_text(), decl_start)
    } else {
        None
    };

    Some(match doc {
        Some(doc) => format!("```ril\n{code_block}\n```\n\n{doc}"),
        None => format!("```ril\n{code_block}\n```"),
    })
}

/// Pipeline-aware `textDocument/signatureHelp`.
///
/// In `Array::map(xs, |)`, `activeParameter` is `1`.
/// In `xs |> Array::map(|)`, parameter 0 (`xs`) is already supplied by `|>`,
/// so `activeParameter` is automatically offset by `+1`!
pub(crate) fn signature_help(state: &mut LspState, params: &Value) -> Option<Value> {
    let (uri, line, character) = extract_position(params)?;
    let text = state.documents.get(uri)?.clone();
    let offset = line_col_to_offset(&text, line, character)?;

    let (open_paren, active_commas) = find_enclosing_call_paren(&text, offset)?;
    let callee_end = open_paren;
    let before_paren = text.get(..callee_end)?.trim_end();
    // Skip optional generic arguments `<...>` before `(`.
    let callee_ident_end = strip_trailing_generics(before_paren);
    let callee_text = before_paren.get(..callee_ident_end)?;

    // Scan back across `Mod::func` or `func`.
    let bytes = callee_text.as_bytes();
    let mut start = bytes.len();
    while start > 0
        && bytes
            .get(start - 1)
            .copied()
            .is_some_and(|b| is_ident_byte(b) || b == b':')
    {
        start -= 1;
    }
    let callee_path = callee_text.get(start..)?;
    if callee_path.is_empty() {
        return None;
    }

    // Check if this call is the RHS of a pipeline (`|>` or `|?>`)!
    let before_callee = callee_text.get(..start)?.trim_end();
    let before_mode = strip_mode_word(before_callee).trim_end();
    let is_piped = before_mode.ends_with("|>") || before_mode.ends_with("|?>");
    let active_param = active_commas + usize::from(is_piped);

    let (ws, typed) = state.best_typed(uri)?;
    let file = typed.hir.files().find(|f| f.path == ws.entry_logical)?;
    let viewer = typed.hir.module_scope(file.id);

    // Resolve callee: prefer HIR resolution at `callee_ident_end - 1`, else resolve by path name.
    let probe_pos = callee_ident_end.saturating_sub(1);
    let def_id = typed
        .hir
        .resolutions()
        .filter(|(span, _)| span.file == file.id && probe_pos >= span.start && probe_pos <= span.end)
        .min_by_key(|(span, _)| span.end.saturating_sub(span.start))
        .and_then(|(_, res)| res.definition())
        .or_else(|| resolve_callee_by_name(&typed.hir, viewer, callee_path))?;

    let (label, param_labels, _ret) = callable_params_for_sig_help(&typed, def_id)?;
    let parameters_json: Vec<Value> = param_labels
        .iter()
        .map(|p| json!({ "label": p }))
        .collect();
    let clamped_active = if parameters_json.is_empty() {
        0
    } else {
        active_param.min(parameters_json.len() - 1)
    };

    Some(json!({
        "signatures": [{
            "label": label,
            "parameters": parameters_json,
            "activeParameter": clamped_active
        }],
        "activeSignature": 0,
        "activeParameter": clamped_active
    }))
}

fn find_enclosing_call_paren(text: &str, offset: usize) -> Option<(usize, usize)> {
    let bytes = text.get(..offset)?.as_bytes();
    let mut i = bytes.len();
    let mut paren_depth = 0i32;
    let mut bracket_depth = 0i32;
    let mut brace_depth = 0i32;
    let mut commas = 0usize;
    let mut in_string = false;

    while i > 0 {
        i -= 1;
        let Some(&b) = bytes.get(i) else {
            break;
        };
        if in_string {
            if b == b'"' && (i == 0 || bytes.get(i - 1) != Some(&b'\\')) {
                in_string = false;
            }
            continue;
        }
        match b {
            b'"' => in_string = true,
            b')' => paren_depth += 1,
            b'(' => {
                if paren_depth == 0 && bracket_depth == 0 && brace_depth == 0 {
                    return Some((i, commas));
                }
                paren_depth -= 1;
            }
            b']' => bracket_depth += 1,
            b'[' => bracket_depth = (bracket_depth - 1).max(0),
            b'}' => brace_depth += 1,
            b'{' => {
                if brace_depth == 0 {
                    return None;
                }
                brace_depth -= 1;
            }
            b',' if paren_depth == 0 && bracket_depth == 0 && brace_depth == 0 => {
                commas += 1;
            }
            _ => {}
        }
    }
    None
}

fn strip_trailing_generics(s: &str) -> usize {
    let bytes = s.as_bytes();
    if bytes.last() != Some(&b'>') {
        return bytes.len();
    }
    let mut depth = 0i32;
    let mut i = bytes.len();
    while i > 0 {
        i -= 1;
        match bytes.get(i).copied() {
            Some(b'>') => depth += 1,
            Some(b'<') => {
                depth -= 1;
                if depth == 0 {
                    return i;
                }
            }
            Some(b'\n' | b';') => return bytes.len(),
            _ => {}
        }
    }
    bytes.len()
}

fn strip_mode_word(s: &str) -> &str {
    for kw in ["^mut", "mut", "ref", "new", "via"] {
        if let Some(rest) = s.strip_suffix(kw)
            && (rest.is_empty() || rest.ends_with([' ', '\t', '>']))
        {
            return rest;
        }
    }
    s
}

fn resolve_callee_by_name(
    hir: &ril_hir::Program,
    viewer: ril_hir::ScopeId,
    callee_path: &str,
) -> Option<DefinitionId> {
    if let Some((qual, member)) = callee_path.split_once("::") {
        for scope in [viewer, hir.prelude_scope()] {
            for (name, res, _) in hir.scope_entries(scope) {
                if name == qual
                    && let Some(mod_scope) = res.module()
                {
                    for (m_name, m_res, _) in hir.scope_entries(mod_scope) {
                        if m_name == member
                            && let Some(id) = m_res.definition()
                        {
                            return Some(id);
                        }
                    }
                }
            }
        }
        return None;
    }
    for scope in [viewer, hir.prelude_scope()] {
        for (name, res, _) in hir.scope_entries(scope) {
            if name == callee_path
                && let Some(id) = res.definition()
            {
                return Some(id);
            }
        }
    }
    None
}
