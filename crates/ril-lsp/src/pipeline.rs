use std::collections::{BTreeMap, BTreeSet};

use ril_hir::{DefinitionId, DefinitionKind, Program, Resolution, ScopeId};
use ril_sema::ty::{AdtKind, GenericValue, Member, Ty, TypedProgram};
use ril_source::span::FileId;
use ril_syntax::syntax::{Function, Mode, StmtKind, Type as AstType};
use serde_json::{Value, json};

use crate::{
    analysis::LspState,
    protocol::{extract_doc_comment, import_insert_line, offset_to_line_col},
    workspace::STD_MODULES,
};

/// Parsed pipeline trigger context at cursor.
#[derive(Debug)]
pub(crate) struct PipelineContext {
    pub(crate) op_start: usize,
    pub(crate) lhs_start: usize,
    pub(crate) lhs_end: usize,
    pub(crate) propagate: bool,
    pub(crate) typed_mode: Option<Mode>,
    pub(crate) qualifier: Option<String>,
    pub(crate) prefix: String,
    pub(crate) prefix_start: usize,
}

/// Detects whether `offset` in `text` is inside a pipeline RHS (`expr |> ...` or `expr |?> ...`).
pub(crate) fn detect_pipeline_context(text: &str, offset: usize) -> Option<PipelineContext> {
    let before = text.get(..offset)?;
    let bytes = before.as_bytes();

    // Scan back past the partial identifier / `Module::ident` prefix at cursor.
    let mut i = bytes.len();
    while i > 0 && bytes.get(i - 1).copied().is_some_and(is_ident_byte) {
        i -= 1;
    }
    let prefix_start = i;
    let prefix = before.get(prefix_start..offset)?.to_owned();

    // Optional `Module::` qualifier immediately before `prefix`.
    let mut qualifier = None;
    let mut scan = prefix_start;
    if scan >= 2 && before.get(scan - 2..scan) == Some("::") {
        let q_end = scan - 2;
        let mut q_start = q_end;
        while q_start > 0 && bytes.get(q_start - 1).copied().is_some_and(is_ident_byte) {
            q_start -= 1;
        }
        if q_start < q_end {
            qualifier = Some(before.get(q_start..q_end)?.to_owned());
            scan = q_start;
        }
    }

    // Skip spaces/tabs between mode keyword or `|>` and qualifier/prefix.
    let before_ident = trim_horiz_end(before.get(..scan)?);

    // Check for optional explicit mode marker typed after `|>` (`mut`, `ref`, `^mut`, `new`, `via`).
    let (after_op, typed_mode) = strip_trailing_mode(before_ident);
    let after_op = trim_horiz_end(after_op);

    let (op_start, propagate) = if let Some(stripped) = after_op.strip_suffix("|?>") {
        (stripped.len(), true)
    } else {
        let stripped = after_op.strip_suffix("|>")?;
        (stripped.len(), false)
    };

    let (lhs_start, lhs_end) = extract_lhs_expr_bounds(text, op_start)?;
    Some(PipelineContext {
        op_start,
        lhs_start,
        lhs_end,
        propagate,
        typed_mode,
        qualifier,
        prefix,
        prefix_start,
    })
}

/// Extracts `(start, end)` byte bounds of the expression immediately preceding `op_start`.
pub(crate) fn extract_lhs_expr_bounds(text: &str, op_start: usize) -> Option<(usize, usize)> {
    let before = text.get(..op_start)?;
    let trimmed = before.trim_end();
    if trimmed.is_empty() {
        return None;
    }
    let lhs_end = trimmed.len();
    let bytes = trimmed.as_bytes();

    // Walk backward across balanced brackets and expression tokens until a statement/clause boundary.
    let mut i = lhs_end;
    let mut paren = 0i32;
    let mut bracket = 0i32;
    let mut brace = 0i32;
    let mut in_string = false;

    while i > 0 {
        let Some(&b) = bytes.get(i - 1) else {
            break;
        };
        if in_string {
            if b == b'"' && (i < 2 || bytes.get(i - 2) != Some(&b'\\')) {
                in_string = false;
            }
            i -= 1;
            continue;
        }
        match b {
            b'"' => {
                in_string = true;
                i -= 1;
            }
            b')' => {
                paren += 1;
                i -= 1;
            }
            b'(' => {
                if paren == 0 {
                    break;
                }
                paren -= 1;
                i -= 1;
            }
            b']' => {
                bracket += 1;
                i -= 1;
            }
            b'[' => {
                if bracket == 0 {
                    break;
                }
                bracket -= 1;
                i -= 1;
            }
            b'}' => {
                brace += 1;
                i -= 1;
            }
            b'{' => {
                if brace == 0 {
                    // Check for `.{` record literal start only when inside brace
                    break;
                }
                brace -= 1;
                i -= 1;
            }
            b';' | b',' if paren == 0 && bracket == 0 && brace == 0 => break,
            b'=' if paren == 0 && bracket == 0 && brace == 0 => {
                // Stop on assignment `=`, `+=`, etc., but not `==` or `!=` or `<=` or `>=`.
                let prev = i
                    .checked_sub(2)
                    .and_then(|idx| bytes.get(idx).copied())
                    .unwrap_or(0);
                let next = bytes.get(i).copied().unwrap_or(0);
                if matches!(prev, b'=' | b'!' | b'<' | b'>') || next == b'=' {
                    i -= 1;
                } else {
                    break;
                }
            }
            b'>' if paren == 0
                && bracket == 0
                && brace == 0
                && i >= 2
                && bytes.get(i - 2) == Some(&b'-') =>
            {
                // Stop after `->` (closure or match arm body start).
                break;
            }
            b'\n' if paren == 0 && bracket == 0 && brace == 0 => {
                // Allow multi-line pipeline continuation if the next non-ws token is `|>` / `|?>` / `.`
                // or the previous line ends with `|>` / `|?>`.
                let after_nl = trimmed.get(i..lhs_end).unwrap_or("").trim_start();
                let before_nl = trimmed.get(..i - 1).unwrap_or("").trim_end();
                if after_nl.starts_with("|>")
                    || after_nl.starts_with("|?>")
                    || after_nl.starts_with('.')
                    || before_nl.ends_with("|>")
                    || before_nl.ends_with("|?>")
                {
                    i -= 1;
                } else {
                    break;
                }
            }
            _ => {
                // Check for statement keywords (`return`, `if`, `while`, `match`, `else`, `in`)
                // at top level when separated by whitespace.
                if paren == 0 && bracket == 0 && brace == 0 && is_ident_byte(b) {
                    let word_end = i;
                    let mut word_start = i;
                    while word_start > 0
                        && bytes
                            .get(word_start - 1)
                            .copied()
                            .is_some_and(is_ident_byte)
                    {
                        word_start -= 1;
                    }
                    let word = trimmed.get(word_start..word_end).unwrap_or("");
                    let preceded_by_boundary = word_start == 0
                        || bytes.get(word_start - 1).copied().is_some_and(|ch| {
                            matches!(ch, b' ' | b'\t' | b'\n' | b'\r' | b'{' | b'(' | b';')
                        });
                    if preceded_by_boundary
                        && matches!(
                            word,
                            "return" | "let" | "var" | "if" | "else" | "while" | "for" | "match"
                        )
                        && word_end < lhs_end
                        && bytes.get(word_end).is_some_and(u8::is_ascii_whitespace)
                    {
                        i = word_end;
                        break;
                    }
                    i = word_start;
                } else {
                    i -= 1;
                }
            }
        }
    }

    let slice = trimmed.get(i..lhs_end)?;
    let lead_ws = slice.len() - slice.trim_start().len();
    let lhs_start = i + lead_ws;
    (lhs_start < lhs_end).then_some((lhs_start, lhs_end))
}

/// Computes pipeline completion items for `expr |> <cursor>` or `expr |?> <cursor>`.
pub(crate) fn pipeline_completions(
    state: &mut LspState,
    uri: &str,
    text: &str,
    offset: usize,
    ctx: &PipelineContext,
) -> Vec<Value> {
    let Some((typed, file_id, raw_lhs_ty)) = resolve_lhs_type(
        state,
        uri,
        text,
        ctx.op_start,
        offset,
        ctx.lhs_start,
        ctx.lhs_end,
    ) else {
        return Vec::new();
    };

    let lhs_ty = if ctx.propagate {
        unwrap_propagated_type(&raw_lhs_ty, &typed.hir)
    } else {
        raw_lhs_ty
    };

    let replace_start = if ctx.qualifier.is_some() {
        ctx.prefix_start
            .saturating_sub(2 + ctx.qualifier.as_deref().map_or(0, str::len))
    } else {
        ctx.prefix_start
    };
    let (start_line, start_col) = offset_to_line_col(text, replace_start);
    let (end_line, end_col) = offset_to_line_col(text, offset);
    let replace_range = json!({
        "start": { "line": start_line, "character": start_col },
        "end": { "line": end_line, "character": end_col }
    });

    collect_pipe_candidates(
        &typed,
        file_id,
        text,
        &lhs_ty,
        ctx.typed_mode,
        ctx.qualifier.as_deref(),
        &ctx.prefix,
        &replace_range,
        false,
        state.config.auto_import,
    )
}

/// Computes optional dot-to-pipe postfix completion items for `expr.<prefix>`
/// that rewrite `.prefix` into ` |> Mod::func($1)`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn dot_to_pipe_completions(
    typed: &TypedProgram,
    file_id: FileId,
    text: &str,
    lhs_ty: &Ty,
    dot_start: usize,
    cursor_offset: usize,
    prefix: &str,
    allow_auto_import: bool,
) -> Vec<Value> {
    let (start_line, start_col) = offset_to_line_col(text, dot_start);
    let (end_line, end_col) = offset_to_line_col(text, cursor_offset);
    let replace_range = json!({
        "start": { "line": start_line, "character": start_col },
        "end": { "line": end_line, "character": end_col }
    });
    collect_pipe_candidates(
        typed,
        file_id,
        text,
        lhs_ty,
        None,
        None,
        prefix,
        &replace_range,
        true,
        allow_auto_import,
    )
}

pub(crate) fn resolve_lhs_type(
    state: &mut LspState,
    uri: &str,
    text: &str,
    op_start: usize,
    cursor_offset: usize,
    lhs_start: usize,
    lhs_end: usize,
) -> Option<(std::sync::Arc<TypedProgram>, ril_source::span::FileId, Ty)> {
    // Build a probe buffer with `op_start..cursor_offset` blanked out to spaces so offsets
    // before `op_start` remain identical and `lhs` parses & typechecks cleanly.
    let mut probe = String::with_capacity(text.len());
    probe.push_str(text.get(..op_start)?);
    for ch in text.get(op_start..cursor_offset)?.chars() {
        if ch == '\n' {
            probe.push('\n');
        } else {
            probe.push(' ');
        }
    }
    probe.push_str(text.get(cursor_offset..)?);

    if let Some(hit) = state.probe_expr_type(uri, &probe, lhs_start, lhs_end) {
        return Some(hit);
    }

    // Second probe: truncate after `lhs_end` and close any unclosed `{` blocks so syntax
    // errors later in the file cannot interfere with typing `lhs`.
    if let Some(prefix_src) = text.get(..lhs_end) {
        let mut trunc = prefix_src.to_owned();
        let mut open_braces = 0usize;
        let mut in_str = false;
        let mut prev = 0u8;
        for b in prefix_src.bytes() {
            if in_str {
                if b == b'"' && prev != b'\\' {
                    in_str = false;
                }
            } else {
                match b {
                    b'"' => in_str = true,
                    b'{' => open_braces += 1,
                    b'}' => open_braces = open_braces.saturating_sub(1),
                    _ => {}
                }
            }
            prev = b;
        }
        for _ in 0..open_braces {
            trunc.push_str("\n}");
        }
        if let Some(hit) = state.probe_expr_type(uri, &trunc, lhs_start, lhs_end) {
            return Some(hit);
        }
    }

    // Fallback to cached best_typed on original text.
    let (ws, typed) = state.best_typed(uri)?;
    let file_id = typed.hir.files().find(|f| f.path == ws.entry_logical)?.id;
    let ty = crate::analysis::lookup_expr_type_near(&typed, file_id, lhs_start, lhs_end)?;
    Some((typed, file_id, ty))
}

fn unwrap_propagated_type(ty: &Ty, hir: &Program) -> Ty {
    if let Some((ok, _)) = ty.as_result(hir) {
        return ok.clone();
    }
    if let Some(inner) = ty.as_option(hir) {
        return inner.clone();
    }
    ty.clone()
}

struct PipeCandidate {
    def_id: DefinitionId,
    /// Display & call path, e.g. `"len"` or `"Array::map"`.
    call_path: String,
    /// Short name for filtering (e.g. `"map"`).
    short_name: String,
    /// Optional module import path to add if not yet imported (e.g. `"ril/file"`).
    auto_import: Option<String>,
    /// Match tier score (higher is better).
    score: u32,
    /// Substituted parameter types (if matched via `Callable`).
    subst: BTreeMap<DefinitionId, Ty>,
    /// First parameter access mode.
    first_mode: Mode,
}

#[allow(clippy::too_many_arguments)]
fn collect_pipe_candidates(
    typed: &TypedProgram,
    file_id: FileId,
    source_text: &str,
    lhs_ty: &Ty,
    typed_mode: Option<Mode>,
    qualifier_filter: Option<&str>,
    prefix: &str,
    replace_range: &Value,
    is_dot_postfix: bool,
    allow_auto_import: bool,
) -> Vec<Value> {
    let hir = &typed.hir;
    let viewer_scope = hir.module_scope(file_id);
    let prelude_scope = hir.prelude_scope();

    let mut seen_defs: BTreeSet<DefinitionId> = BTreeSet::new();
    let mut imported_scopes: BTreeMap<ScopeId, String> = BTreeMap::new();
    let mut candidates: Vec<PipeCandidate> = Vec::new();

    // Helper to evaluate a callable definition against `lhs_ty`.
    let mut consider = |def_id: DefinitionId,
                        call_path: String,
                        short_name: String,
                        scope_bonus: u32,
                        auto_import: Option<String>| {
        if !seen_defs.insert(def_id) {
            return;
        }
        // Skip effect operations and meta-only type-value helpers unless matching TypeValue.
        if hir.operation_effect(def_id).is_some() {
            return;
        }
        let def = hir.definition(def_id);
        if !matches!(
            def.kind,
            DefinitionKind::Function | DefinitionKind::Primitive(_)
        ) {
            return;
        }
        if let Some(q) = qualifier_filter {
            let expected_prefix = format!("{q}::");
            if !call_path.starts_with(&expected_prefix) {
                return;
            }
        }
        if !prefix.is_empty()
            && !short_name
                .to_ascii_lowercase()
                .contains(&prefix.to_ascii_lowercase())
            && !call_path
                .to_ascii_lowercase()
                .contains(&prefix.to_ascii_lowercase())
        {
            return;
        }

        let Some((match_score, first_mode, subst)) = match_first_param(typed, def_id, lhs_ty)
        else {
            return;
        };

        let mut total_score = match_score + scope_bonus;
        if let Some(tm) = typed_mode {
            if first_mode == tm {
                total_score += 25;
            } else if first_mode == Mode::Via {
                total_score += 10;
            } else if tm != Mode::Plain && first_mode == Mode::Plain {
                total_score = total_score.saturating_sub(30);
            }
        }
        // Prefix exact-start boost.
        if !prefix.is_empty() && short_name.starts_with(prefix) {
            total_score += 15;
        }

        candidates.push(PipeCandidate {
            def_id,
            call_path,
            short_name,
            auto_import,
            score: total_score,
            subst,
            first_mode,
        });
    };

    // 1. Current file / module scope entries (local fns + directly imported fns + imported modules).
    for (name, res, vis) in hir.scope_entries(viewer_scope) {
        if !hir.is_visible(viewer_scope, viewer_scope, vis) {
            continue;
        }
        match res {
            Resolution::Definition(id) => {
                consider(id, name.clone(), name, 40, None);
            }
            Resolution::Module(mod_scope) | Resolution::TypeAndModule(_, mod_scope) => {
                imported_scopes.entry(mod_scope).or_insert(name);
            }
        }
    }

    // 2. Prelude scope entries (bare functions like `len`, `clone`, `derive`, `inner`, `println`
    //    AND prelude-reexported modules like `Array`, `String`, `Map`, `Set`, `Bytes`, `Numeric`).
    for (name, res, vis) in hir.scope_entries(prelude_scope) {
        if !hir.is_visible(prelude_scope, viewer_scope, vis) {
            continue;
        }
        match res {
            Resolution::Definition(id) => {
                consider(id, name.clone(), name, 30, None);
            }
            Resolution::Module(mod_scope) | Resolution::TypeAndModule(_, mod_scope) => {
                imported_scopes.entry(mod_scope).or_insert(name);
            }
        }
    }

    // 3. Functions inside already-imported (or prelude-imported) modules (`Array::map`, `String::split`, etc.).
    for (&mod_scope, mod_alias) in &imported_scopes {
        for (fn_name, res, vis) in hir.scope_entries(mod_scope) {
            if !hir.is_visible(mod_scope, viewer_scope, vis) {
                continue;
            }
            if let Resolution::Definition(id) = res {
                let qualified = format!("{mod_alias}::{fn_name}");
                consider(id, qualified, fn_name, 25, None);
            }
        }
    }

    // 4. Unimported `ril/*` stdlib and `pkg/*` modules (auto-import tier, lower rank).
    if allow_auto_import && qualifier_filter.is_none() {
        for (mod_key, mod_scope) in hir.module_scopes() {
            if mod_scope == viewer_scope
                || mod_scope == prelude_scope
                || imported_scopes.contains_key(&mod_scope)
            {
                continue;
            }
            let import_path = mod_key.to_string_lossy().replace('\\', "/");
            if import_path == "ril/prelude" {
                continue;
            }
            let Some(mod_alias) = derive_module_alias(&import_path) else {
                continue;
            };
            for (fn_name, res, vis) in hir.scope_entries(mod_scope) {
                if !hir.is_visible(mod_scope, viewer_scope, vis) {
                    continue;
                }
                if let Resolution::Definition(id) = res {
                    let qualified = format!("{mod_alias}::{fn_name}");
                    consider(id, qualified, fn_name, 0, Some(import_path.clone()));
                }
            }
        }
    }

    // Sort descending by score, then alphabetically by call_path.
    candidates.sort_by(|a, b| {
        b.score
            .cmp(&a.score)
            .then_with(|| a.call_path.cmp(&b.call_path))
    });

    let insert_import_line = import_insert_line(source_text);

    candidates
        .into_iter()
        .enumerate()
        .map(|(rank, cand)| {
            build_pipe_completion_item(
                typed,
                &cand,
                rank,
                typed_mode,
                replace_range,
                is_dot_postfix,
                insert_import_line,
            )
        })
        .collect()
}

fn derive_module_alias(import_path: &str) -> Option<String> {
    let last = import_path.rsplit('/').next()?;
    if let Some(&(_, pascal)) = STD_MODULES.iter().find(|&&(stem, _)| stem == last) {
        return Some(pascal.to_owned());
    }
    let mut out = String::new();
    for part in last.split('_') {
        let mut chars = part.chars();
        let first = chars.next()?;
        out.push(first.to_ascii_uppercase());
        out.push_str(chars.as_str());
    }
    (!out.is_empty()).then_some(out)
}

fn build_pipe_completion_item(
    typed: &TypedProgram,
    cand: &PipeCandidate,
    rank: usize,
    typed_mode: Option<Mode>,
    replace_range: &Value,
    is_dot_postfix: bool,
    import_line: usize,
) -> Value {
    let (remaining_params, ret_display, full_sig) = format_pipe_signature(typed, cand);
    let mode_prefix = if typed_mode.is_none() {
        match cand.first_mode {
            Mode::Mut => "mut ",
            Mode::Ref => "ref ",
            Mode::Shared => "^mut ",
            _ => "",
        }
    } else {
        ""
    };

    let snippet_body = if remaining_params.is_empty() {
        format!("{mode_prefix}{}", cand.call_path)
    } else {
        let args: Vec<String> = remaining_params
            .iter()
            .enumerate()
            .map(|(idx, p)| format!("${{{}:{}}}", idx + 1, p.snippet_placeholder))
            .collect();
        format!("{mode_prefix}{}({})", cand.call_path, args.join(", "))
    };

    let new_text = if is_dot_postfix {
        format!(" |> {snippet_body}")
    } else {
        snippet_body
    };

    let label = if is_dot_postfix {
        format!("|> {mode_prefix}{}", cand.call_path)
    } else if !mode_prefix.is_empty() {
        format!("{mode_prefix}{}", cand.call_path)
    } else {
        cand.call_path.clone()
    };

    let remaining_display = remaining_params
        .iter()
        .map(|p| p.display.as_str())
        .collect::<Vec<_>>()
        .join(", ");
    let mut detail = format!("({remaining_display}) -> {ret_display}");
    if let Some(ref imp) = cand.auto_import {
        detail.push_str(&format!("  (auto-import {imp})"));
    }

    let doc_text = {
        let def = typed.hir.definition(cand.def_id);
        let doc = if def.name.span.file != ril_source::span::FileId::BUILTIN {
            let f = typed.hir.file(def.name.span.file);
            let decl_start = def
                .stmt
                .map_or(def.name.span.start, |s| f.ast.stmt(s).span.start);
            extract_doc_comment(f.source_text(), decl_start)
        } else {
            None
        };
        match doc {
            Some(d) => format!("```ril\n{full_sig}\n```\n\n{d}"),
            None => format!("```ril\n{full_sig}\n```"),
        }
    };

    let sort_text = if is_dot_postfix {
        format!("1_{rank:04}_{}", cand.short_name)
    } else {
        format!("0_{rank:04}_{}", cand.short_name)
    };

    let mut item = json!({
        "label": label,
        "kind": 3, // CompletionItemKind::Function
        "detail": detail,
        "documentation": { "kind": "markdown", "value": doc_text },
        "sortText": sort_text,
        "filterText": if is_dot_postfix {
            format!("{} {}", cand.short_name, cand.call_path)
        } else {
            format!("{} {}", cand.call_path, cand.short_name)
        },
        "insertTextFormat": 2, // Snippet
        "textEdit": {
            "range": replace_range,
            "newText": new_text
        }
    });

    if let Some(ref imp) = cand.auto_import
        && let Some(obj) = item.as_object_mut()
    {
        obj.insert(
            "additionalTextEdits".into(),
            json!([{
                "range": {
                    "start": { "line": import_line, "character": 0 },
                    "end": { "line": import_line, "character": 0 }
                },
                "newText": format!("use {imp}\n")
            }]),
        );
    }

    item
}

struct ParamBrief {
    snippet_placeholder: String,
    display: String,
}

fn format_pipe_signature(
    typed: &TypedProgram,
    cand: &PipeCandidate,
) -> (Vec<ParamBrief>, String, String) {
    let def = typed.hir.definition(cand.def_id);
    if let Some(callable) = typed.callables.get(&cand.def_id) {
        let remaining: Vec<ParamBrief> = callable
            .parameters
            .iter()
            .skip(1)
            .enumerate()
            .filter(|(_, p)| !p.optional)
            .map(|(i, p)| {
                let spec_ty = p.ty.specialize(&cand.subst);
                let mode_str = mode_prefix_str(p.mode);
                let name = p.label.clone().unwrap_or_else(|| format!("arg{}", i + 2));
                let placeholder = if mode_str.is_empty() {
                    name.clone()
                } else {
                    format!("{mode_str}{name}")
                };
                ParamBrief {
                    snippet_placeholder: placeholder,
                    display: format!("{mode_str}{name}: {}", spec_ty.display(&typed.hir)),
                }
            })
            .collect();
        let ret_ty = callable.result.specialize(&cand.subst);
        let ret_mode = mode_prefix_str(callable.result_mode);
        let ret_display = format!("{ret_mode}{}", ret_ty.display(&typed.hir));
        let full_ty = Ty::Callable(callable.clone())
            .display(&typed.hir)
            .to_string();
        let full_sig = full_ty.strip_prefix("fn").map_or_else(
            || full_ty.clone(),
            |rest| format!("fn {}{rest}", cand.call_path),
        );
        return (remaining, ret_display, full_sig);
    }

    // Fallback for bodyless primitives not in `typed.callables`: read AST signature directly.
    if let Some((file, fun)) = ast_function_for(&typed.hir, cand.def_id) {
        let remaining: Vec<ParamBrief> = fun
            .signature
            .params
            .iter()
            .skip(1)
            .enumerate()
            .filter(|(_, p)| p.default.is_none())
            .map(|(i, p)| {
                let name = p
                    .name
                    .as_ref()
                    .map_or_else(|| format!("arg{}", i + 2), |n| n.value.clone());
                let mode_str = mode_prefix_str(p.mode);
                let ty_text =
                    p.ty.and_then(|t| {
                        file.source_text()
                            .get(file.ast.ty(t).span.start..file.ast.ty(t).span.end)
                    })
                    .unwrap_or("_");
                ParamBrief {
                    snippet_placeholder: if mode_str.is_empty() {
                        name.clone()
                    } else {
                        format!("{mode_str}{name}")
                    },
                    display: format!("{mode_str}{name}: {ty_text}"),
                }
            })
            .collect();
        let ret_span = file.ast.ty(fun.signature.result).span;
        let ret_text = file
            .source_text()
            .get(ret_span.start..ret_span.end)
            .unwrap_or("_");
        let ret_display = format!("{}{ret_text}", mode_prefix_str(fun.signature.result_mode));
        let stmt_span = def
            .stmt
            .map(|s| file.ast.stmt(s).span)
            .unwrap_or(def.name.span);
        let full_sig = file
            .source_text()
            .get(stmt_span.start..stmt_span.end)
            .unwrap_or(&def.name.value)
            .lines()
            .next()
            .unwrap_or(&def.name.value)
            .trim()
            .to_owned();
        return (remaining, ret_display, full_sig);
    }

    (Vec::new(), "_".into(), format!("fn {}", cand.call_path))
}

fn mode_prefix_str(mode: Mode) -> &'static str {
    match mode {
        Mode::Plain => "",
        Mode::Ref => "ref ",
        Mode::Mut => "mut ",
        Mode::Shared => "^mut ",
        Mode::New => "new ",
        Mode::Via => "via ",
        Mode::Infer => "infer ",
    }
}

/// Checks whether `def_id`'s 1st parameter accepts `lhs_ty`.
/// Returns `Some((score, first_param_mode, generic_subst))` on match.
fn match_first_param(
    typed: &TypedProgram,
    def_id: DefinitionId,
    lhs_ty: &Ty,
) -> Option<(u32, Mode, BTreeMap<DefinitionId, Ty>)> {
    let hir = &typed.hir;
    if let Some(callable) = typed.callables.get(&def_id) {
        let first = callable.parameters.first()?;
        // Skip meta-only `Type<T>` functions unless LHS is actually a `TypeValue`.
        if matches!(first.ty, Ty::TypeValue(_)) && !matches!(lhs_ty, Ty::TypeValue(_)) {
            return None;
        }
        let mut subst = BTreeMap::new();
        let score = unify_ty(lhs_ty, &first.ty, hir, &mut subst)?;
        // Also validate generic guard/domain bounds from the AST declaration if present.
        if !check_generic_bounds_for_subst(typed, def_id, &subst) {
            return None;
        }
        return Some((score, first.mode, subst));
    }

    // AST fallback for special primitives (`len`, `inner`, `clone`, `derive`, `abort`).
    let (file, fun) = ast_function_for(hir, def_id)?;
    let first = fun.signature.params.first()?;
    let first_ty_id = first.ty?;
    let first_ty = &file.ast.ty(first_ty_id).value;
    let score = match_ast_first_param(typed, file, fun, first_ty, lhs_ty)?;
    Some((score, first.mode, BTreeMap::new()))
}

fn check_generic_bounds_for_subst(
    typed: &TypedProgram,
    def_id: DefinitionId,
    subst: &BTreeMap<DefinitionId, Ty>,
) -> bool {
    if subst.is_empty() {
        return true;
    }
    let Some((file, fun)) = ast_function_for(&typed.hir, def_id) else {
        return true;
    };
    for gp in &fun.generics {
        let Some(Resolution::Definition(gp_id)) = typed.hir.resolve(gp.name.span) else {
            continue;
        };
        let Some(actual) = subst.get(&gp_id) else {
            continue;
        };
        if !gp.bound.is_empty() {
            let ok = gp.bound.iter().any(|&b_id| {
                ast_type_matches_concrete(file, &file.ast.ty(b_id).value, actual, &typed.hir)
            });
            if !ok {
                return false;
            }
        }
        for guard in &gp.guards {
            let guard_name = guard.segments.last().map_or("", |s| s.name.value.as_str());
            if !satisfies_known_guard(guard_name, actual, typed) {
                return false;
            }
        }
    }
    true
}

fn match_ast_first_param(
    typed: &TypedProgram,
    file: &ril_hir::File,
    fun: &Function,
    param_ty: &AstType,
    lhs_ty: &Ty,
) -> Option<u32> {
    match param_ty {
        AstType::Named(path) if path.segments.len() == 1 => {
            let seg = path.segments.first()?;
            let name = seg.name.value.as_str();
            // Check if `name` is one of `fun.generics`.
            if let Some(gp) = fun.generics.iter().find(|g| g.name.value == name) {
                if !gp.bound.is_empty() {
                    let ok = gp.bound.iter().any(|&b_id| {
                        ast_type_matches_concrete(
                            file,
                            &file.ast.ty(b_id).value,
                            lhs_ty,
                            &typed.hir,
                        )
                    });
                    return ok.then_some(70);
                }
                if !gp.guards.is_empty() {
                    let ok = gp.guards.iter().all(|g| {
                        let gname = g.segments.last().map_or("", |s| s.name.value.as_str());
                        satisfies_known_guard(gname, lhs_ty, typed)
                    });
                    return ok.then_some(65);
                }
                return Some(30);
            }
            // Special stdlib types (`Type<T>`, primitives).
            if name == "Type" {
                return matches!(lhs_ty, Ty::TypeValue(_)).then_some(95);
            }
            if ast_type_matches_concrete(file, param_ty, lhs_ty, &typed.hir) {
                return Some(100);
            }
            None
        }
        AstType::Array(_, _) => matches!(lhs_ty, Ty::Array(_)).then_some(85),
        AstType::Map(_, _, _) => matches!(lhs_ty, Ty::Map(_, _)).then_some(85),
        AstType::Option(_) => lhs_ty.is_option(&typed.hir).then_some(85),
        AstType::Result(_, _) => lhs_ty.is_result(&typed.hir).then_some(85),
        AstType::Callable(_) => matches!(lhs_ty, Ty::Callable(_)).then_some(80),
        AstType::Tuple(_) | AstType::TupleAny => matches!(lhs_ty, Ty::Tuple(_)).then_some(85),
        AstType::Record { .. } => matches!(lhs_ty, Ty::Record(_, _)).then_some(85),
        _ => None,
    }
}

fn ast_type_matches_concrete(
    file: &ril_hir::File,
    ast_ty: &AstType,
    actual: &Ty,
    hir: &Program,
) -> bool {
    match ast_ty {
        AstType::Unit => matches!(actual, Ty::Unit),
        AstType::Named(path) => {
            let name = path.segments.last().map_or("", |s| s.name.value.as_str());
            match name {
                "bool" => matches!(actual, Ty::Bool),
                "int" => matches!(actual, Ty::Int),
                "f64" => matches!(actual, Ty::F64),
                "str" => matches!(actual, Ty::Str),
                "bytes" => matches!(actual, Ty::Bytes),
                "never" => matches!(actual, Ty::Never),
                "Draft" => matches!(actual, Ty::Draft(_)),
                "Range" => matches!(actual, Ty::Range),
                _ => match actual {
                    Ty::Adt(adt) => hir.definition(adt.definition).name.value == name,
                    _ => false,
                },
            }
        }
        AstType::Array(_, elem) => {
            matches!(actual, Ty::Array(m) if ast_type_matches_concrete(file, &file.ast.ty(*elem).value, &m.ty, hir))
        }
        _ => false,
    }
}

fn satisfies_known_guard(guard: &str, ty: &Ty, typed: &TypedProgram) -> bool {
    let hir = &typed.hir;
    match guard {
        "LenTarget" => {
            matches!(ty, Ty::Str | Ty::Bytes | Ty::Array(_) | Ty::Map(_, _)) || ty.is_set(hir)
        }
        "SharedObject" => {
            !typed.is_value(ty) && !matches!(ty, Ty::Mode | Ty::Draft(_) | Ty::TypeValue(_))
        }
        "NominalWrapper" => match ty {
            Ty::Draft(_) => true,
            Ty::Adt(adt) => matches!(adt.kind, AdtKind::Nominal | AdtKind::Opaque),
            _ => false,
        },
        "Tuple" => matches!(ty, Ty::Tuple(_)),
        _ => true,
    }
}

/// Structural first-parameter unifier returning a match quality score (0..=100).
fn unify_ty(
    lhs: &Ty,
    param: &Ty,
    hir: &Program,
    subst: &mut BTreeMap<DefinitionId, Ty>,
) -> Option<u32> {
    match (lhs, param) {
        (Ty::Unknown | Ty::Infer(_), _) | (_, Ty::Unknown | Ty::Infer(_)) => None,
        (_, Ty::Param(id)) => {
            if let Some(prev) = subst.get(id) {
                (prev == lhs).then_some(80)
            } else {
                subst.insert(*id, lhs.clone());
                Some(30)
            }
        }
        (Ty::Unit, Ty::Unit)
        | (Ty::Bool, Ty::Bool)
        | (Ty::Int, Ty::Int)
        | (Ty::F64, Ty::F64)
        | (Ty::Str, Ty::Str)
        | (Ty::Bytes, Ty::Bytes)
        | (Ty::Range, Ty::Range)
        | (Ty::Mode, Ty::Mode) => Some(100),
        (Ty::Array(a), Ty::Array(b)) => {
            let inner = unify_member(a, b, hir, subst)?;
            Some(if inner == 100 { 100 } else { 85 })
        }
        (Ty::Map(k1, v1), Ty::Map(k2, v2)) => {
            let ks = unify_ty(k1, k2, hir, subst)?;
            let vs = unify_member(v1, v2, hir, subst)?;
            Some(if ks == 100 && vs == 100 { 100 } else { 85 })
        }
        (Ty::Tuple(a), Ty::Tuple(b)) if a.len() == b.len() => {
            let mut min_s = 100;
            for (ma, mb) in a.iter().zip(b) {
                min_s = min_s.min(unify_member(ma, mb, hir, subst)?);
            }
            Some(if min_s == 100 { 100 } else { 85 })
        }
        (Ty::Record(a, _), Ty::Record(b, b_open)) => {
            if !b_open && a.len() != b.len() {
                return None;
            }
            let mut min_s = 100;
            for (k, mb) in b {
                let ma = a.get(k)?;
                min_s = min_s.min(unify_member(ma, mb, hir, subst)?);
            }
            Some(if min_s == 100 { 100 } else { 85 })
        }
        (Ty::Adt(a), Ty::Adt(b)) if a.definition == b.definition => {
            if a.arguments.len() != b.arguments.len() {
                return None;
            }
            let mut min_s = 100;
            for (ga, gb) in a.arguments.iter().zip(&b.arguments) {
                match (ga, gb) {
                    (GenericValue::Type(ta), GenericValue::Type(tb)) => {
                        min_s = min_s.min(unify_ty(ta, tb, hir, subst)?);
                    }
                    (GenericValue::Data(va), GenericValue::Data(vb)) if va == vb => {}
                    (GenericValue::Mode(_), GenericValue::Mode(_)) => {}
                    _ => return None,
                }
            }
            Some(if min_s == 100 { 100 } else { 85 })
        }
        (Ty::Draft(a), Ty::Draft(b)) => {
            let inner = unify_ty(a, b, hir, subst)?;
            Some(if inner == 100 { 100 } else { 85 })
        }
        (Ty::TypeValue(Some(a)), Ty::TypeValue(Some(b))) => {
            let inner = unify_ty(a, b, hir, subst)?;
            Some(if inner == 100 { 100 } else { 85 })
        }
        (Ty::TypeValue(_), Ty::TypeValue(None)) => Some(80),
        (Ty::Callable(a), Ty::Callable(b)) if a.parameters.len() == b.parameters.len() => {
            let mut min_s = 90;
            for (pa, pb) in a.parameters.iter().zip(&b.parameters) {
                min_s = min_s.min(unify_ty(&pa.ty, &pb.ty, hir, subst)?);
            }
            min_s = min_s.min(unify_ty(&a.result, &b.result, hir, subst)?);
            Some(min_s.max(75))
        }
        _ => None,
    }
}

fn unify_member(
    a: &Member,
    b: &Member,
    hir: &Program,
    subst: &mut BTreeMap<DefinitionId, Ty>,
) -> Option<u32> {
    unify_ty(&a.ty, &b.ty, hir, subst)
}

fn ast_function_for(hir: &Program, def_id: DefinitionId) -> Option<(&ril_hir::File, &Function)> {
    let def = hir.definition(def_id);
    if def.name.span.file == ril_source::span::FileId::BUILTIN {
        return None;
    }
    let stmt = def.stmt?;
    let file = hir.file(def.name.span.file);
    match &file.ast.stmt(stmt).value.kind {
        StmtKind::Function(fun) => Some((file, fun)),
        _ => None,
    }
}

fn trim_horiz_end(s: &str) -> &str {
    s.trim_end_matches([' ', '\t'])
}

fn strip_trailing_mode(s: &str) -> (&str, Option<Mode>) {
    for (kw, mode) in [
        ("^mut", Mode::Shared),
        ("mut", Mode::Mut),
        ("ref", Mode::Ref),
        ("new", Mode::New),
        ("via", Mode::Via),
    ] {
        if let Some(rest) = s.strip_suffix(kw)
            && (rest.is_empty()
                || rest.ends_with([' ', '\t', '>'])
                || rest.ends_with("|>")
                || rest.ends_with("|?>"))
        {
            return (rest, Some(mode));
        }
    }
    (s, None)
}

pub(crate) const fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// Helper for signature help: returns the `Callable` or AST parameter summary of `def_id`.
pub(crate) fn callable_params_for_sig_help(
    typed: &TypedProgram,
    def_id: DefinitionId,
) -> Option<(String, Vec<String>, String)> {
    let def = typed.hir.definition(def_id);
    if let Some(callable) = typed.callables.get(&def_id) {
        let params: Vec<String> = callable
            .parameters
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let mode = mode_prefix_str(p.mode);
                let name = p.label.clone().unwrap_or_else(|| format!("arg{}", i + 1));
                format!("{mode}{name}: {}", p.ty.display(&typed.hir))
            })
            .collect();
        let ret = format!(
            "{}{}",
            mode_prefix_str(callable.result_mode),
            callable.result.display(&typed.hir)
        );
        let full = Ty::Callable(callable.clone())
            .display(&typed.hir)
            .to_string();
        let label = full.strip_prefix("fn").map_or_else(
            || full.clone(),
            |rest| format!("fn {}{rest}", def.name.value),
        );
        return Some((label, params, ret));
    }
    let (file, fun) = ast_function_for(&typed.hir, def_id)?;
    let params: Vec<String> = fun
        .signature
        .params
        .iter()
        .enumerate()
        .map(|(i, p)| {
            let mode = mode_prefix_str(p.mode);
            let name = p
                .name
                .as_ref()
                .map_or_else(|| format!("arg{}", i + 1), |n| n.value.clone());
            let ty_text =
                p.ty.and_then(|t| {
                    file.source_text()
                        .get(file.ast.ty(t).span.start..file.ast.ty(t).span.end)
                })
                .unwrap_or("_");
            format!("{mode}{name}: {ty_text}")
        })
        .collect();
    let ret_span = file.ast.ty(fun.signature.result).span;
    let ret_text = file
        .source_text()
        .get(ret_span.start..ret_span.end)
        .unwrap_or("_");
    let ret = format!("{}{ret_text}", mode_prefix_str(fun.signature.result_mode));
    let label = format!("fn {}({}) -> {ret}", def.name.value, params.join(", "));
    Some((label, params, ret))
}
