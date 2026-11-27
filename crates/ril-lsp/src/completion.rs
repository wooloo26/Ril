use std::collections::BTreeSet;

use ril_hir::{DefinitionId, DefinitionKind, Program, Resolution, ScopeId};
use ril_sema::ty::{Ty, TypedProgram};
use ril_source::span::FileId;
use ril_syntax::syntax::StmtKind;
use serde_json::{Value, json};

use crate::{
    analysis::LspState,
    pipeline::{
        detect_pipeline_context, dot_to_pipe_completions, extract_lhs_expr_bounds, is_ident_byte,
        pipeline_completions, resolve_lhs_type,
    },
    protocol::{extract_doc_comment, extract_position, line_col_to_offset},
    workspace::{STD_MODULES, WorkspacePackage},
};

const KEYWORDS: &[(&str, &str)] = &[
    ("fn", "fn ${1:name}(${2}) -> ${3:()} {\n    $0\n}"),
    ("ctl", "ctl ${1:op}(${2}) -> ${3:()}"),
    ("let", "let ${1:name} = $0"),
    ("var", "var ${1:name} = $0"),
    ("type", "type ${1:Name} $0"),
    ("eff", "eff ${1:Name} {\n    fn ${2:op}(${3}) -> ${4:()}\n}"),
    ("sub", "sub ${1:Name} {\n    $0\n}"),
    ("if", "if ${1:cond} {\n    $0\n}"),
    ("else", "else {\n    $0\n}"),
    ("match", "match ${1:value} {\n    ${2:_} -> $0\n}"),
    ("while", "while ${1:cond} {\n    $0\n}"),
    ("for", "for ${1:items} as ${2:item} {\n    $0\n}"),
    ("return", "return $0"),
    ("defer", "defer $0"),
    ("use", "use $0"),
    ("with", "with ${1:Eff::op} = $0"),
    ("where", "where $0"),
    ("pub", "pub "),
    ("pkg", "pkg "),
    ("meta", "meta "),
    ("mut", "mut "),
    ("^mut", "^mut "),
    ("ref", "ref "),
    ("new", "new "),
    ("via", "via "),
    ("infer", "infer "),
    ("opaque", "opaque type "),
    ("linear", "linear type "),
    ("typeof", "typeof "),
    ("as", "as "),
    ("break", "break"),
    ("continue", "continue"),
    ("true", "true"),
    ("false", "false"),
];

const PRIMITIVE_TYPES: &[&str] = &[
    "bool", "int", "f64", "str", "bytes", "never", "Type", "KeyOf", "Nominal", "Super",
];

pub(crate) fn complete(state: &mut LspState, params: &Value) -> Value {
    let Some((uri, line, character)) = extract_position(params) else {
        return json!([]);
    };
    let Some(text) = state.documents.get(uri).cloned() else {
        return json!([]);
    };
    let Some(offset) = line_col_to_offset(&text, line, character) else {
        return json!([]);
    };

    // 1. Pipeline completion (`expr |> `, `expr |?> `, `expr |> mut `, `expr |> Array::`).
    if let Some(pipe_ctx) = detect_pipeline_context(&text, offset) {
        let items = pipeline_completions(state, uri, &text, offset, &pipe_ctx);
        return json!({ "isIncomplete": false, "items": items });
    }

    // 2. Import path completion (`use ril/...`, `use pkg/...`).
    if let Some(items) = try_import_path_completion(state, uri, &text, offset) {
        return json!({ "isIncomplete": false, "items": items });
    }

    // 3. Effect completion (`@io`, `@UserEff`).
    if let Some(items) = try_effect_completion(state, uri, &text, offset) {
        return json!({ "isIncomplete": false, "items": items });
    }

    // 4. Namespace / Sum / Effect member completion (`Mod::`, `Option::`, `Eff::`).
    if let Some(items) = try_namespace_completion(state, uri, &text, offset) {
        return json!({ "isIncomplete": false, "items": items });
    }

    // 5. Dot / safe-navigation member completion (`.` / `?.`) + optional dot-to-pipe suggestions.
    if let Some(items) = try_member_completion(state, uri, &text, offset) {
        return json!({ "isIncomplete": false, "items": items });
    }

    // 6. General lexical scope completion (locals, params, module decls, imports, prelude, keywords).
    let items = lexical_completions(state, uri, &text, offset);
    json!({ "isIncomplete": false, "items": items })
}

fn try_import_path_completion(
    state: &mut LspState,
    uri: &str,
    text: &str,
    offset: usize,
) -> Option<Vec<Value>> {
    let before = text.get(..offset)?;
    let line_start = before.rfind('\n').map_or(0, |i| i + 1);
    let line_prefix = before.get(line_start..)?.trim_start();
    let rest = line_prefix
        .strip_prefix("pub use ")
        .or_else(|| line_prefix.strip_prefix("pkg use "))
        .or_else(|| line_prefix.strip_prefix("use "))?;
    if rest.contains("::") || rest.contains('=') || rest.contains(' ') {
        return None;
    }

    let mut items = Vec::new();
    if rest.is_empty() || "ril/".starts_with(rest) {
        items.push(json!({
            "label": "ril/",
            "kind": 9, // Module
            "detail": "Ril standard library"
        }));
    }
    if rest.is_empty() || "pkg/".starts_with(rest) {
        items.push(json!({
            "label": "pkg/",
            "kind": 9,
            "detail": "Current package modules"
        }));
    }
    if let Some(sub) = rest.strip_prefix("ril/") {
        for &(stem, pascal) in STD_MODULES {
            if stem == "prelude" {
                continue;
            }
            if stem.starts_with(sub) {
                items.push(json!({
                    "label": stem,
                    "kind": 9,
                    "detail": format!("ril/{stem} ({pascal})"),
                    "insertText": stem
                }));
            }
        }
    } else if let Some(sub) = rest.strip_prefix("pkg/")
        && let Some((ws, _)) = state.best_typed(uri)
    {
        for logical in ws.pkg.files.keys() {
            if let Ok(rel) = logical.strip_prefix("pkg") {
                let s = rel.to_string_lossy().replace('\\', "/");
                let stem = s.strip_suffix(".ril").unwrap_or(&s);
                if stem.starts_with(sub) {
                    items.push(json!({
                        "label": stem,
                        "kind": 9,
                        "detail": format!("pkg/{stem}"),
                        "insertText": stem
                    }));
                }
            }
        }
    }
    Some(items)
}

fn try_effect_completion(
    state: &mut LspState,
    uri: &str,
    text: &str,
    offset: usize,
) -> Option<Vec<Value>> {
    let before = text.get(..offset)?;
    let bytes = before.as_bytes();
    let mut i = bytes.len();
    while i > 0 && bytes.get(i - 1).copied().is_some_and(is_ident_byte) {
        i -= 1;
    }
    if i == 0 || bytes.get(i - 1) != Some(&b'@') {
        return None;
    }
    let prefix = before.get(i..offset)?;
    let mut items = Vec::new();
    for (name, desc) in [("io", "Built-in I/O system effect")] {
        if name.starts_with(prefix) {
            items.push(json!({
                "label": name,
                "kind": 23, // Event
                "detail": desc
            }));
        }
    }
    if let Some((ws, typed)) = state.best_typed(uri)
        && let Some(file) = typed.hir.files().find(|f| f.path == ws.entry_logical)
    {
        let scope = typed.hir.module_scope(file.id);
        for (name, res, _) in typed.hir.scope_entries(scope) {
            if let Resolution::Definition(id) = res
                && matches!(typed.hir.definition(id).kind, DefinitionKind::Effect(_))
                && name.starts_with(prefix)
            {
                items.push(json!({
                    "label": name,
                    "kind": 23,
                    "detail": "User effect"
                }));
            }
        }
    }
    Some(items)
}

fn try_namespace_completion(
    state: &mut LspState,
    uri: &str,
    text: &str,
    offset: usize,
) -> Option<Vec<Value>> {
    let before = text.get(..offset)?;
    let bytes = before.as_bytes();
    let mut i = bytes.len();
    while i > 0 && bytes.get(i - 1).copied().is_some_and(is_ident_byte) {
        i -= 1;
    }
    let prefix = before.get(i..offset)?;
    if i < 2 || before.get(i - 2..i) != Some("::") {
        return None;
    }
    let seg_end = i - 2;
    let mut seg_start = seg_end;
    while seg_start > 0 && bytes.get(seg_start - 1).copied().is_some_and(is_ident_byte) {
        seg_start -= 1;
    }
    if seg_start == seg_end {
        return None;
    }
    let qual = before.get(seg_start..seg_end)?;

    let (ws, typed) = state.best_typed(uri)?;
    let file = typed.hir.files().find(|f| f.path == ws.entry_logical)?;
    let viewer = typed.hir.module_scope(file.id);

    let Some(target_scope) = resolve_namespace_scope(&typed.hir, viewer, qual) else {
        if !prefix.is_empty() {
            return None;
        }
        // Offer nominal wrap snippet `Name::(...)` when typing `Name::` on a payload nominal/opaque type.
        for scope in [viewer, typed.hir.prelude_scope()] {
            for (name, res, vis) in typed.hir.scope_entries(scope) {
                if name != qual || !typed.hir.is_visible(scope, viewer, vis) {
                    continue;
                }
                if let Some(id) = res.definition() {
                    let def = typed.hir.definition(id);
                    if def.kind == DefinitionKind::Type && !typed.hir.unit_constructor(id) {
                        let snippet = if typed.is_nominal_record(id) {
                            "(.{ ${1} })"
                        } else {
                            "(${1})"
                        };
                        return Some(vec![json!({
                            "label": format!("{name}::(...)"),
                            "kind": 4,
                            "detail": "nominal wrap",
                            "insertText": snippet,
                            "insertTextFormat": 2,
                        })]);
                    }
                }
            }
        }
        return None;
    };
    let mut items = Vec::new();
    for (name, res, vis) in typed.hir.scope_entries(target_scope) {
        if !typed.hir.is_visible(target_scope, viewer, vis) {
            continue;
        }
        if !prefix.is_empty()
            && !name
                .to_ascii_lowercase()
                .starts_with(&prefix.to_ascii_lowercase())
        {
            continue;
        }
        items.push(completion_item_for_resolution(&typed, &name, res));
    }
    Some(items)
}

fn resolve_namespace_scope(hir: &Program, viewer: ScopeId, qual: &str) -> Option<ScopeId> {
    if qual == "Super" {
        return hir.scope_parent(viewer);
    }
    for scope in [viewer, hir.prelude_scope()] {
        for (name, res, vis) in hir.scope_entries(scope) {
            if name != qual || !hir.is_visible(scope, viewer, vis) {
                continue;
            }
            match res {
                Resolution::Module(s) | Resolution::TypeAndModule(_, s) => return Some(s),
                Resolution::Definition(id) => match hir.definition(id).kind {
                    DefinitionKind::Namespace(s)
                    | DefinitionKind::Effect(s)
                    | DefinitionKind::Sum(s) => return Some(s),
                    _ => {}
                },
            }
        }
    }
    // Fallback: match stdlib module alias (e.g. `Array`, `String`, `File`).
    for &(stem, pascal) in STD_MODULES {
        if pascal == qual {
            let key = std::path::PathBuf::from(format!("ril/{stem}"));
            if let Some((_, scope)) = hir.module_scopes().find(|(k, _)| *k == &key) {
                return Some(scope);
            }
        }
    }
    None
}

fn try_member_completion(
    state: &mut LspState,
    uri: &str,
    text: &str,
    offset: usize,
) -> Option<Vec<Value>> {
    let before = text.get(..offset)?;
    let bytes = before.as_bytes();
    let mut i = bytes.len();
    while i > 0 && bytes.get(i - 1).copied().is_some_and(is_ident_byte) {
        i -= 1;
    }
    let prefix = before.get(i..offset)?;
    let (dot_start, safe_nav) = if i >= 2 && before.get(i - 2..i) == Some("?.") {
        (i - 2, true)
    } else if i >= 1
        && bytes.get(i - 1) == Some(&b'.')
        && (i < 2 || bytes.get(i - 2) != Some(&b'.'))
    {
        (i - 1, false)
    } else {
        return None;
    };

    let (lhs_start, lhs_end) = extract_lhs_expr_bounds(text, dot_start)?;
    let (typed, file_id, raw_ty) =
        resolve_lhs_type(state, uri, text, dot_start, offset, lhs_start, lhs_end)?;
    let receiver_ty = if safe_nav {
        raw_ty.as_option(&typed.hir).cloned().unwrap_or(raw_ty)
    } else {
        raw_ty
    };

    let mut items = Vec::new();
    collect_member_fields(&typed, &receiver_ty, prefix, &mut items);

    // Optional Dot-to-Pipe postfix suggestions (`xs.map` -> `xs |> Array::map($1)`).
    if state.config.dot_to_pipe && !safe_nav {
        let pipe_items = dot_to_pipe_completions(
            &typed,
            file_id,
            text,
            &receiver_ty,
            dot_start,
            offset,
            prefix,
            state.config.auto_import,
        );
        items.extend(pipe_items);
    }

    Some(items)
}

fn collect_member_fields(typed: &TypedProgram, ty: &Ty, prefix: &str, out: &mut Vec<Value>) {
    match ty {
        Ty::Record(fields, _) => {
            for (name, member) in fields {
                if !prefix.is_empty() && !name.starts_with(prefix) {
                    continue;
                }
                let ty_str = member.ty.display(&typed.hir).to_string();
                out.push(json!({
                    "label": name,
                    "kind": 5, // Field
                    "detail": ty_str,
                    "sortText": format!("0_{name}")
                }));
            }
        }
        Ty::Tuple(members) => {
            for (idx, member) in members.iter().enumerate() {
                let label = idx.to_string();
                if !prefix.is_empty() && !label.starts_with(prefix) {
                    continue;
                }
                out.push(json!({
                    "label": label,
                    "kind": 5,
                    "detail": member.ty.display(&typed.hir).to_string(),
                    "sortText": format!("0_{idx:03}")
                }));
            }
        }
        Ty::Draft(inner) => collect_member_fields(typed, inner, prefix, out),
        Ty::Adt(adt) => {
            if let Some(layout) = typed.nominal_layout(adt) {
                collect_member_fields(typed, &layout, prefix, out);
            }
        }
        _ => {}
    }
}

fn lexical_completions(state: &mut LspState, uri: &str, text: &str, offset: usize) -> Vec<Value> {
    let before = text.get(..offset).unwrap_or("");
    let bytes = before.as_bytes();
    let mut i = bytes.len();
    while i > 0 && bytes.get(i - 1).copied().is_some_and(is_ident_byte) {
        i -= 1;
    }
    let prefix = before.get(i..offset).unwrap_or("");
    let prefix_lower = prefix.to_ascii_lowercase();

    let mut seen = BTreeSet::new();
    let mut items = Vec::new();

    if let Some((ws, typed)) = state.best_typed(uri)
        && let Some(file) = typed.hir.files().find(|f| f.path == ws.entry_logical)
    {
        let file_id = file.id;
        let viewer = typed.hir.module_scope(file_id);

        // 1. Local bindings / parameters declared before `offset` in the current file.
        for (def_id, def) in typed.hir.definitions() {
            if def.name.span.file == file_id
                && matches!(def.kind, DefinitionKind::Local | DefinitionKind::Generic)
                && def.name.span.start <= offset
                && def.name.value != "_"
                && (prefix_lower.is_empty()
                    || def
                        .name
                        .value
                        .to_ascii_lowercase()
                        .starts_with(&prefix_lower))
                && seen.insert(def.name.value.clone())
            {
                let detail = typed
                    .bindings
                    .get(&def_id)
                    .map(|ty| ty.display(&typed.hir).to_string())
                    .unwrap_or_else(|| {
                        if def.kind == DefinitionKind::Generic {
                            "type parameter".into()
                        } else {
                            "local".into()
                        }
                    });
                items.push(json!({
                    "label": def.name.value,
                    "kind": if def.kind == DefinitionKind::Generic { 25 } else { 6 },
                    "detail": detail,
                    "sortText": format!("0_{}", def.name.value)
                }));
            }
        }

        // 2. Module scope & prelude scope symbols.
        for (rank_prefix, scope) in [("1", viewer), ("2", typed.hir.prelude_scope())] {
            for (name, res, vis) in typed.hir.scope_entries(scope) {
                if !typed.hir.is_visible(scope, viewer, vis) {
                    continue;
                }
                if !prefix_lower.is_empty() && !name.to_ascii_lowercase().starts_with(&prefix_lower)
                {
                    continue;
                }
                if seen.insert(name.clone()) {
                    let mut item = completion_item_for_resolution(&typed, &name, res);
                    if let Some(obj) = item.as_object_mut() {
                        obj.insert("sortText".into(), json!(format!("{rank_prefix}_{name}")));
                    }
                    items.push(item);
                }
            }
        }
    }

    // 3. Primitive types & parent qualifier fallback.
    for &ty_name in PRIMITIVE_TYPES {
        if (prefix_lower.is_empty() || ty_name.to_ascii_lowercase().starts_with(&prefix_lower))
            && seen.insert(ty_name.to_owned())
        {
            if let Some(info) = crate::protocol::builtin_doc(ty_name) {
                items.push(json!({
                    "label": ty_name,
                    "kind": info.kind,
                    "detail": info.detail,
                    "documentation": { "kind": "markdown", "value": info.doc },
                    "sortText": format!("3_{ty_name}")
                }));
            } else {
                items.push(json!({
                    "label": ty_name,
                    "kind": 9, // Module / Qualifier (`Super`)
                    "detail": "parent scope qualifier",
                    "sortText": format!("3_{ty_name}")
                }));
            }
        }
    }

    // 4. Keywords & snippets.
    for &(kw, snippet) in KEYWORDS {
        if (prefix_lower.is_empty() || kw.starts_with(&prefix_lower)) && seen.insert(kw.to_owned())
        {
            let is_snippet = snippet.contains('$');
            let mut item = json!({
                "label": kw,
                "kind": 14, // Keyword
                "insertText": snippet,
                "sortText": format!("4_{kw}")
            });
            if is_snippet && let Some(obj) = item.as_object_mut() {
                obj.insert("insertTextFormat".into(), json!(2));
            }
            items.push(item);
        }
    }

    items
}

fn completion_item_for_resolution(typed: &TypedProgram, name: &str, res: Resolution) -> Value {
    match res {
        Resolution::Module(_) => json!({
            "label": name,
            "kind": 9, // Module
            "detail": "module"
        }),
        Resolution::TypeAndModule(id, _) => {
            let detail = summarize_def_detail(typed, id).unwrap_or_else(|| "type / module".into());
            let mut item = json!({
                "label": name,
                "kind": 7, // Class/Type
                "detail": detail
            });
            if let Some(d) = definition_doc(typed, id)
                && let Some(obj) = item.as_object_mut()
            {
                obj.insert(
                    "documentation".into(),
                    json!({ "kind": "markdown", "value": d }),
                );
            }
            item
        }
        Resolution::Definition(id) => {
            let def = typed.hir.definition(id);
            let builtin = (def.name.span.file == FileId::BUILTIN)
                .then(|| crate::protocol::builtin_doc(&def.name.value))
                .flatten();
            let is_primitive_type = matches!(def.kind, DefinitionKind::Primitive(_))
                && def.stmt.is_some_and(|stmt| {
                    matches!(
                        typed.hir.file(def.name.span.file).ast.stmt(stmt).value.kind,
                        StmtKind::Type(_)
                    )
                });
            let kind = if let Some(info) = &builtin {
                info.kind
            } else if is_primitive_type {
                22 // Struct/Type (e.g. Derived<T>)
            } else {
                match def.kind {
                    DefinitionKind::Function | DefinitionKind::Primitive(_) => 3, // Function
                    DefinitionKind::Constant => 21,                               // Constant
                    DefinitionKind::Type => 22,                                   // Struct/Type
                    DefinitionKind::Sum(_) => 13,                                 // Enum
                    DefinitionKind::Variant(_) => 20,                             // EnumMember
                    DefinitionKind::Namespace(_) => 9,                            // Module
                    DefinitionKind::Effect(_) => 23,                              // Event
                    DefinitionKind::Local => 6,                                   // Variable
                    DefinitionKind::Generic => 25,                                // TypeParameter
                }
            };
            let detail = builtin
                .as_ref()
                .map(|info| info.detail.to_owned())
                .or_else(|| summarize_def_detail(typed, id))
                .unwrap_or_default();
            let doc = builtin
                .as_ref()
                .map(|info| info.doc.to_owned())
                .or_else(|| definition_doc(typed, id));
            let mut item = json!({
                "label": name,
                "kind": kind,
                "detail": detail
            });
            if let Some(d) = doc
                && let Some(obj) = item.as_object_mut()
            {
                obj.insert(
                    "documentation".into(),
                    json!({ "kind": "markdown", "value": d }),
                );
            }
            item
        }
    }
}

fn definition_doc(typed: &TypedProgram, id: DefinitionId) -> Option<String> {
    let def = typed.hir.definition(id);
    if def.name.span.file == FileId::BUILTIN {
        return None;
    }
    let file = typed.hir.file(def.name.span.file);
    let decl_start = if matches!(def.kind, DefinitionKind::Variant(_)) {
        def.name.span.start
    } else {
        def.stmt
            .map_or(def.name.span.start, |s| file.ast.stmt(s).span.start)
    };
    extract_doc_comment(file.source_text(), decl_start)
}

pub(crate) fn summarize_def_detail(typed: &TypedProgram, id: DefinitionId) -> Option<String> {
    let def = typed.hir.definition(id);
    if let Some(callable) = typed.callables.get(&id) {
        let ty = Ty::Callable(callable.clone())
            .display(&typed.hir)
            .to_string();
        return Some(
            ty.strip_prefix("fn")
                .map_or_else(|| ty.clone(), |rest| format!("fn {}{rest}", def.name.value)),
        );
    }
    if let Some(ty) = typed.bindings.get(&id) {
        return Some(ty.display(&typed.hir).to_string());
    }
    if def.name.span.file != FileId::BUILTIN
        && let Some(stmt) = def.stmt
    {
        let file = typed.hir.file(def.name.span.file);
        if let StmtKind::Function(_) | StmtKind::Type(_) = &file.ast.stmt(stmt).value.kind {
            let span = file.ast.stmt(stmt).span;
            if let Some(first_line) = file
                .source_text()
                .get(span.start..span.end)
                .and_then(|s| s.lines().next())
            {
                return Some(first_line.trim().trim_end_matches('{').trim().to_owned());
            }
        }
    }
    match def.kind {
        DefinitionKind::Variant(sum_id) => Some(format!(
            "variant of {}",
            typed.hir.definition(sum_id).name.value
        )),
        DefinitionKind::Sum(_) => Some("sum type".into()),
        DefinitionKind::Type => Some("type".into()),
        DefinitionKind::Effect(_) => Some("effect".into()),
        DefinitionKind::Namespace(_) => Some("sub module".into()),
        _ => None,
    }
}

#[allow(dead_code)]
fn _keep_workspace_import(_: &WorkspacePackage) {}
