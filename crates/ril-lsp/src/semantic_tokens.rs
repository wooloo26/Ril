use std::collections::{BTreeMap, HashSet};

use ril_hir::{DefinitionId, DefinitionKind, Program};
use ril_sema::ty::TypedProgram;
use ril_source::span::{FileId, Span};
use ril_syntax::{
    lexer::Kind,
    syntax::{Expr, Member, Pattern, StmtKind},
};
use serde_json::{Value, json};

use crate::{analysis::LspState, protocol::offset_to_line_col};

pub(crate) const TOKEN_TYPES: &[&str] = &[
    "namespace",     // 0
    "type",          // 1
    "typeParameter", // 2
    "function",      // 3
    "parameter",     // 4
    "variable",      // 5
    "property",      // 6
    "enumMember",    // 7
    "macro",         // 8
];

pub(crate) const TOKEN_MODIFIERS: &[&str] = &[
    "declaration",    // bit 0 (1)
    "readonly",       // bit 1 (2)
    "modification",   // bit 2 (4)
    "defaultLibrary", // bit 3 (8)
];

const TT_NAMESPACE: u32 = 0;
const TT_TYPE: u32 = 1;
const TT_TYPE_PARAM: u32 = 2;
const TT_FUNCTION: u32 = 3;
const TT_PARAMETER: u32 = 4;
const TT_VARIABLE: u32 = 5;
const TT_PROPERTY: u32 = 6;
const TT_ENUM_MEMBER: u32 = 7;
const TT_MACRO: u32 = 8;

const MOD_DECLARATION: u32 = 1 << 0;
const MOD_READONLY: u32 = 1 << 1;
const MOD_MODIFICATION: u32 = 1 << 2;
const MOD_DEFAULT_LIB: u32 = 1 << 3;

pub(crate) fn legend_json() -> Value {
    json!({
        "tokenTypes": TOKEN_TYPES,
        "tokenModifiers": TOKEN_MODIFIERS
    })
}

#[derive(Clone, Copy, Debug)]
struct RawToken {
    start: usize,
    end: usize,
    token_type: u32,
    modifiers: u32,
}

pub(crate) fn semantic_tokens_full(state: &mut LspState, params: &Value) -> Value {
    let Some(uri) = params.pointer("/textDocument/uri").and_then(Value::as_str) else {
        return json!({ "data": [] });
    };
    let Some((ws, typed)) = state.best_typed(uri) else {
        return json!({ "data": [] });
    };
    let Some(file) = typed.hir.files().find(|f| f.path == ws.entry_logical) else {
        return json!({ "data": [] });
    };
    let data = compute_tokens_for_file(&typed, file.id);
    json!({ "data": data })
}

pub(crate) fn compute_tokens_for_file(typed: &TypedProgram, file_id: FileId) -> Vec<u32> {
    let hir = &typed.hir;
    let file = hir.file(file_id);
    let text = file.source_text();

    // Collect parameter DefinitionIds & mutable/var local DefinitionIds from AST.
    let mut param_defs: HashSet<DefinitionId> = HashSet::new();
    let mut mutable_defs: HashSet<DefinitionId> = HashSet::new();
    let mut tokens_by_start: BTreeMap<usize, RawToken> = BTreeMap::new();

    collect_ast_roles(
        hir,
        file,
        &mut param_defs,
        &mut mutable_defs,
        &mut tokens_by_start,
    );

    // 1. Classify all declarations in this file.
    for (def_id, def) in hir.definitions() {
        if def.name.span.file != file_id || def.name.value == "_" {
            continue;
        }
        let Some((tt, mut mods)) = classify_definition(hir, def_id, &param_defs, &mutable_defs)
        else {
            continue;
        };
        mods |= MOD_DECLARATION;
        insert_single_line_token(&mut tokens_by_start, text, def.name.span, tt, mods);
    }

    // 2. Classify all resolved references in this file.
    for (span, res) in hir.resolutions() {
        if span.file != file_id {
            continue;
        }
        // Only highlight single-identifier spans (skip multi-segment paths like `Array::map`;
        // individual segments carry their own resolution or are handled below).
        let Some(slice) = text.get(span.start..span.end) else {
            continue;
        };
        if slice.is_empty() || slice.contains("::") || slice.contains('\n') {
            // For `Mod::member` resolved as a whole path span, highlight the trailing member segment!
            if let Some(colon_idx) = slice.rfind("::") {
                let member_start = span.start + colon_idx + 2;
                let member_span = Span::new(file_id, member_start, span.end);
                if let Some(def_id) = res.definition()
                    && let Some((tt, mods)) =
                        classify_definition(hir, def_id, &param_defs, &mutable_defs)
                {
                    insert_single_line_token(&mut tokens_by_start, text, member_span, tt, mods);
                }
                // Highlight leading module segment(s) as namespace if not already classified.
                let head_end = span.start + colon_idx;
                if let Some(head_str) = text.get(span.start..head_end) {
                    let mut seg_offset = span.start;
                    for seg in head_str.split("::") {
                        let seg_end = seg_offset + seg.len();
                        if !seg.is_empty() && !tokens_by_start.contains_key(&seg_offset) {
                            insert_single_line_token(
                                &mut tokens_by_start,
                                text,
                                Span::new(file_id, seg_offset, seg_end),
                                TT_NAMESPACE,
                                0,
                            );
                        }
                        seg_offset = seg_end + 2;
                    }
                }
            }
            continue;
        }
        if tokens_by_start.contains_key(&span.start) {
            continue;
        }
        if let Some(def_id) = res.definition() {
            if let Some((tt, mods)) = classify_definition(hir, def_id, &param_defs, &mutable_defs) {
                insert_single_line_token(&mut tokens_by_start, text, *span, tt, mods);
            }
        } else if res.module().is_some() {
            insert_single_line_token(&mut tokens_by_start, text, *span, TT_NAMESPACE, 0);
        }
    }

    // 3. Highlight `@io` / `@Effect` annotations via lexer tokens.
    let lex_tokens = file.tokens();
    for pair in lex_tokens.windows(2) {
        if let [at_tok, name_tok] = pair
            && at_tok.text(file.source()) == "@"
            && matches!(name_tok.kind, Kind::Word(_))
            && at_tok.span.end == name_tok.span.start
        {
            let full = Span::new(file_id, at_tok.span.start, name_tok.span.end);
            insert_single_line_token(&mut tokens_by_start, text, full, TT_MACRO, 0);
        }
    }

    // Delta-encode tokens in strict non-overlapping sorted order (UTF-16 columns).
    let mut encoded = Vec::with_capacity(tokens_by_start.len() * 5);
    let mut prev_line = 0u32;
    let mut prev_col = 0u32;
    let mut prev_end_byte = 0usize;

    for tok in tokens_by_start.values() {
        if tok.start < prev_end_byte || tok.end <= tok.start {
            continue;
        }
        let Some(slice) = text.get(tok.start..tok.end) else {
            continue;
        };
        if slice.contains('\n') {
            continue;
        }
        let (line, col) = offset_to_line_col(text, tok.start);
        let utf16_len: usize = slice.chars().map(char::len_utf16).sum();
        if utf16_len == 0 {
            continue;
        }
        let line_u32 = u32::try_from(line).unwrap_or(0);
        let col_u32 = u32::try_from(col).unwrap_or(0);
        let len_u32 = u32::try_from(utf16_len).unwrap_or(0);

        let delta_line = line_u32.saturating_sub(prev_line);
        let delta_start = if delta_line == 0 {
            col_u32.saturating_sub(prev_col)
        } else {
            col_u32
        };
        encoded.extend_from_slice(&[
            delta_line,
            delta_start,
            len_u32,
            tok.token_type,
            tok.modifiers,
        ]);
        prev_line = line_u32;
        prev_col = col_u32;
        prev_end_byte = tok.end;
    }

    encoded
}

fn collect_ast_roles(
    hir: &Program,
    file: &ril_hir::File,
    param_defs: &mut HashSet<DefinitionId>,
    mutable_defs: &mut HashSet<DefinitionId>,
    tokens_by_start: &mut BTreeMap<usize, RawToken>,
) {
    let text = file.source_text();
    let file_id = file.id;

    // Function & closure parameters -> `parameter` (orange italic in Monokai!).
    for stmt in file.ast.statements() {
        match &stmt.value.kind {
            StmtKind::Function(fun) => {
                for p in &fun.signature.params {
                    if let Some(name) = &p.name {
                        if let Some(id) = hir.resolve(name.span).and_then(|r| r.definition()) {
                            param_defs.insert(id);
                            if matches!(
                                p.mode,
                                ril_syntax::syntax::Mode::Mut | ril_syntax::syntax::Mode::Shared
                            ) {
                                mutable_defs.insert(id);
                            }
                        } else if name.value != "_" {
                            insert_single_line_token(
                                tokens_by_start,
                                text,
                                name.span,
                                TT_PARAMETER,
                                MOD_DECLARATION,
                            );
                        }
                    }
                }
            }
            StmtKind::Binding {
                storage, pattern, ..
            } => {
                let is_mut = storage.variable
                    || matches!(
                        storage.mode,
                        ril_syntax::syntax::Mode::Mut | ril_syntax::syntax::Mode::Shared
                    );
                if is_mut
                    && let Pattern::Binding(_, name) = &file.ast.pattern(*pattern).value
                    && let Some(id) = hir.resolve(name.span).and_then(|r| r.definition())
                {
                    mutable_defs.insert(id);
                }
            }
            _ => {}
        }
    }

    for expr in file.ast.expressions() {
        match &expr.value {
            Expr::Closure { params, .. } => {
                for p in params {
                    if let Some(name) = &p.name {
                        if let Some(id) = hir.resolve(name.span).and_then(|r| r.definition()) {
                            param_defs.insert(id);
                            if matches!(
                                p.mode,
                                ril_syntax::syntax::Mode::Mut | ril_syntax::syntax::Mode::Shared
                            ) {
                                mutable_defs.insert(id);
                            }
                        } else if name.value != "_" {
                            let mut mods = MOD_DECLARATION;
                            if matches!(
                                p.mode,
                                ril_syntax::syntax::Mode::Mut | ril_syntax::syntax::Mode::Shared
                            ) {
                                mods |= MOD_MODIFICATION;
                            }
                            insert_single_line_token(
                                tokens_by_start,
                                text,
                                name.span,
                                TT_PARAMETER,
                                mods,
                            );
                        }
                    }
                }
            }
            Expr::Member {
                member: Member::Name(name),
                ..
            } => {
                if name.span.file == file_id {
                    insert_single_line_token(tokens_by_start, text, name.span, TT_PROPERTY, 0);
                }
            }
            Expr::Record { fields, .. } => {
                for f in fields {
                    if f.name.span.file == file_id {
                        insert_single_line_token(
                            tokens_by_start,
                            text,
                            f.name.span,
                            TT_PROPERTY,
                            0,
                        );
                    }
                }
            }
            _ => {}
        }
    }

    for ty_node in file.ast.types_iter() {
        if let ril_syntax::syntax::Type::Record { fields, .. } = &ty_node.value {
            for f in fields {
                if f.name.span.file == file_id {
                    insert_single_line_token(
                        tokens_by_start,
                        text,
                        f.name.span,
                        TT_PROPERTY,
                        MOD_DECLARATION,
                    );
                }
            }
        }
    }
}

fn classify_definition(
    hir: &Program,
    def_id: DefinitionId,
    param_defs: &HashSet<DefinitionId>,
    mutable_defs: &HashSet<DefinitionId>,
) -> Option<(u32, u32)> {
    let def = hir.definition(def_id);
    let is_std = def.name.span.file == FileId::BUILTIN || hir.is_stdlib_file(def.name.span.file);
    let std_mod = if is_std { MOD_DEFAULT_LIB } else { 0 };

    match def.kind {
        DefinitionKind::Function => Some((TT_FUNCTION, std_mod)),
        DefinitionKind::Primitive(_) => {
            // Distinguish primitive types (`int`, `str`, `Draft`) from primitive functions (`len`, `push`).
            let first_upper = def
                .name
                .value
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_uppercase());
            if first_upper
                || matches!(
                    def.name.value.as_str(),
                    "bool" | "int" | "f64" | "str" | "bytes" | "never"
                )
            {
                Some((TT_TYPE, MOD_DEFAULT_LIB))
            } else {
                Some((TT_FUNCTION, MOD_DEFAULT_LIB))
            }
        }
        DefinitionKind::Type | DefinitionKind::Sum(_) => Some((TT_TYPE, std_mod)),
        DefinitionKind::Variant(_) => Some((TT_ENUM_MEMBER, MOD_READONLY | std_mod)),
        DefinitionKind::Namespace(_) => Some((TT_NAMESPACE, std_mod)),
        DefinitionKind::Effect(_) => Some((TT_MACRO, std_mod)),
        DefinitionKind::Generic => Some((TT_TYPE_PARAM, 0)),
        DefinitionKind::Constant => Some((TT_VARIABLE, MOD_READONLY | std_mod)),
        DefinitionKind::Local => {
            if param_defs.contains(&def_id) {
                let mut m = 0;
                if mutable_defs.contains(&def_id) {
                    m |= MOD_MODIFICATION;
                }
                Some((TT_PARAMETER, m))
            } else {
                let m = if mutable_defs.contains(&def_id) {
                    MOD_MODIFICATION
                } else {
                    0
                };
                Some((TT_VARIABLE, m))
            }
        }
    }
}

fn insert_single_line_token(
    map: &mut BTreeMap<usize, RawToken>,
    text: &str,
    span: Span,
    token_type: u32,
    modifiers: u32,
) {
    if span.end <= span.start || span.end > text.len() {
        return;
    }
    if text
        .get(span.start..span.end)
        .is_some_and(|s| !s.contains('\n'))
    {
        map.entry(span.start).or_insert(RawToken {
            start: span.start,
            end: span.end,
            token_type,
            modifiers,
        });
    }
}
