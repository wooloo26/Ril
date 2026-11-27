//! HIR lint pass: full-AST resolution-based unused/dead-code/shadowing/import hygiene checks.
//!
//! Uses full HIR `resolutions()` (including `meta if`/`meta match` pruned branches, `typeof(...)`,
//! and `|> Proof(...)` guards) so compile-time pruned branches NEVER cause false unused warnings.

use std::collections::{BTreeMap, BTreeSet};

use ril_hir::{DefinitionId, DefinitionKind, Program, Resolution};
use ril_source::{
    fix::{Fix, FixKind, FixSafety, TextEdit},
    span::{FileId, Span},
};
use ril_syntax::syntax::{
    Ast, Expr, ExprId, Import, ImportTarget, Mode, Pattern, PatternId, StmtId, StmtKind,
    TypeDefinition, Visibility,
};

use crate::{LintContext, registry};

pub fn run(ctx: &mut LintContext<'_>) {
    let Some(hir) = ctx.hir else {
        return;
    };

    // Build full set of referenced DefinitionIds and ScopeIds across the entire HIR program.
    let mut referenced_defs: BTreeSet<DefinitionId> = BTreeSet::new();
    let mut referenced_scopes: BTreeSet<ril_hir::ScopeId> = BTreeSet::new();
    let mut ref_spans_by_file: BTreeMap<FileId, Vec<(Span, Resolution)>> = BTreeMap::new();
    for (&span, &res) in hir.resolutions() {
        if let Some(def) = res.definition()
            && hir.definition(def).name.span != span
        {
            referenced_defs.insert(def);
        }
        if let Some(scope) = res.module() {
            referenced_scopes.insert(scope);
        }
        ref_spans_by_file
            .entry(span.file)
            .or_default()
            .push((span, res));
    }

    let file_ids: Vec<FileId> = ctx.target_files.iter().copied().collect();
    for file_id in file_ids {
        let Some(file) = hir.files().find(|f| f.id == file_id) else {
            continue;
        };
        let ast = file.ast.clone();
        let src = ctx.source_text(file_id).to_owned();
        let is_executable = file.kind == ril_syntax::parser::FileKind::Executable;

        check_imports_in_block(
            ctx,
            hir,
            file_id,
            &ast,
            &src,
            &ast.items,
            &referenced_defs,
            &referenced_scopes,
            ref_spans_by_file.get(&file_id).map_or(&[], Vec::as_slice),
        );

        let mut outer_live: BTreeMap<String, Span> = BTreeMap::new();
        for &stmt_id in &ast.items {
            walk_stmt(
                ctx,
                hir,
                file_id,
                &ast,
                &src,
                stmt_id,
                is_executable,
                false,
                &referenced_defs,
                &mut outer_live,
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn check_imports_in_block(
    ctx: &mut LintContext<'_>,
    hir: &Program,
    file_id: FileId,
    ast: &Ast,
    src: &str,
    stmts: &[StmtId],
    referenced_defs: &BTreeSet<DefinitionId>,
    referenced_scopes: &BTreeSet<ril_hir::ScopeId>,
    file_refs: &[(Span, Resolution)],
) {
    let mut seen_modules: BTreeMap<(Visibility, String), Span> = BTreeMap::new();
    for &stmt_id in stmts {
        let spanned = ast.stmt(stmt_id);
        let StmtKind::Import(imp) = &spanned.value.kind else {
            continue;
        };
        let vis = spanned.value.visibility;
        let mod_key = module_path_key(imp);

        // `duplicate_import_module`
        if let Some(&prev_span) = seen_modules.get(&(vis, mod_key.clone())) {
            if ctx.may_fire(&registry::DUPLICATE_IMPORT_MODULE) {
                ctx.report(
                    &registry::DUPLICATE_IMPORT_MODULE,
                    spanned.span,
                    format!("duplicate `use` import for module `{mod_key}` in the same scope"),
                )
                .with_label(prev_span, "first imported here")
                .with_help("combine into a single `use M::(a, b)` import");
            }
        } else {
            seen_modules.insert((vis, mod_key.clone()), spanned.span);
        }

        // `redundant_import_alias`
        match &imp.target {
            ImportTarget::Module(Some(alias)) => {
                if let Some(default_name) = default_module_alias(imp)
                    && alias.value == default_name
                    && ctx.may_fire(&registry::REDUNDANT_IMPORT_ALIAS)
                {
                    let edit_start = imp
                        .file
                        .as_ref()
                        .and_then(|f| f.last())
                        .map(|n| n.span.end)
                        .or_else(|| imp.modules.last().map(|n| n.span.end))
                        .unwrap_or(alias.span.start);
                    let edit_span = Span::new(file_id, edit_start, alias.span.end);
                    let fix = Fix {
                        id: format!("redundant_import_alias:{}:{}", file_id.0, alias.span.start),
                        title: format!("Remove redundant `as {}` alias", alias.value),
                        safety: FixSafety::Safe,
                        kind: FixKind::Lint,
                        is_preferred: true,
                        is_organize_imports: true,
                        edits: vec![TextEdit::new(edit_span, "")],
                        delta: None,
                    };
                    ctx.report(
                        &registry::REDUNDANT_IMPORT_ALIAS,
                        alias.span,
                        format!(
                            "import alias `as {}` matches the default module name",
                            alias.value
                        ),
                    )
                    .with_fix(fix);
                }
            }
            ImportTarget::Items(items) => {
                for (name, alias) in items {
                    if let Some(a) = alias
                        && a.value == name.value
                        && ctx.may_fire(&registry::REDUNDANT_IMPORT_ALIAS)
                    {
                        let edit_span = Span::new(file_id, name.span.end, a.span.end);
                        let fix = Fix {
                            id: format!("redundant_import_alias:{}:{}", file_id.0, a.span.start),
                            title: format!("Remove redundant `as {}` alias", a.value),
                            safety: FixSafety::Safe,
                            kind: FixKind::Lint,
                            is_preferred: true,
                            is_organize_imports: true,
                            edits: vec![TextEdit::new(edit_span, "")],
                            delta: None,
                        };
                        ctx.report(
                            &registry::REDUNDANT_IMPORT_ALIAS,
                            a.span,
                            format!(
                                "import alias `as {}` is identical to the imported name",
                                a.value
                            ),
                        )
                        .with_fix(fix);
                    }
                }
            }
            _ => {}
        }

        // `unused_import`: exempt `pub use` and `pkg use` re-exports!
        if vis != Visibility::Private || !ctx.may_fire(&registry::UNUSED_IMPORT) {
            continue;
        }
        match &imp.target {
            ImportTarget::Module(alias) => {
                let bound_name = alias
                    .as_ref()
                    .map(|a| a.value.clone())
                    .or_else(|| default_module_alias(imp));
                let Some(bound) = bound_name else {
                    continue;
                };
                // Check if any resolution outside this `use` statement references a symbol/module
                // spelled via `bound` (or whose target scope/def came from this module).
                let used = file_refs.iter().any(|&(ref_span, res)| {
                    if ref_span.start >= spanned.span.start && ref_span.end <= spanned.span.end {
                        return false;
                    }
                    let tok = src.get(ref_span.start..ref_span.end).unwrap_or("");
                    if tok == bound
                        || tok.starts_with(&format!("{bound}::"))
                        || tok.starts_with(&format!("{bound}<"))
                    {
                        return true;
                    }
                    // Also check direct resolution against imported scope/def if available.
                    if let Some(sc) = res.module()
                        && referenced_scopes.contains(&sc)
                        && tok.contains(&bound)
                    {
                        return true;
                    }
                    false
                });
                if !used {
                    let remove_span = line_removal_span(src, spanned.span);
                    let fix = Fix {
                        id: format!("unused_import:{}:{}", file_id.0, spanned.span.start),
                        title: format!("Remove unused import `{bound}`"),
                        safety: FixSafety::Safe,
                        kind: FixKind::Lint,
                        is_preferred: true,
                        is_organize_imports: true,
                        edits: vec![TextEdit::new(remove_span, "")],
                        delta: None,
                    };
                    ctx.report(
                        &registry::UNUSED_IMPORT,
                        spanned.span,
                        format!("imported module `{bound}` is never used"),
                    )
                    .with_fix(fix);
                }
            }
            ImportTarget::Items(items) => {
                let mut all_unused = !items.is_empty();
                let mut unused_names = Vec::new();
                for (name, alias) in items {
                    let bound = alias.as_ref().unwrap_or(name);
                    let is_used = file_refs.iter().any(|&(ref_span, res)| {
                        if ref_span.start >= spanned.span.start && ref_span.end <= spanned.span.end
                        {
                            return false;
                        }
                        let tok = src.get(ref_span.start..ref_span.end).unwrap_or("");
                        if tok == bound.value
                            || tok.starts_with(&format!("{}::", bound.value))
                            || tok.starts_with(&format!("{}<", bound.value))
                        {
                            return true;
                        }
                        if let Some(def_id) = res.definition()
                            && referenced_defs.contains(&def_id)
                            && hir.definition(def_id).name.value == name.value
                            && tok == bound.value
                        {
                            return true;
                        }
                        false
                    });
                    if is_used {
                        all_unused = false;
                    } else {
                        unused_names.push(bound.clone());
                    }
                }
                if all_unused {
                    let remove_span = line_removal_span(src, spanned.span);
                    let fix = Fix {
                        id: format!("unused_import:{}:{}", file_id.0, spanned.span.start),
                        title: "Remove unused `use` statement".to_owned(),
                        safety: FixSafety::Safe,
                        kind: FixKind::Lint,
                        is_preferred: true,
                        is_organize_imports: true,
                        edits: vec![TextEdit::new(remove_span, "")],
                        delta: None,
                    };
                    ctx.report(
                        &registry::UNUSED_IMPORT,
                        spanned.span,
                        "unused `use` import",
                    )
                    .with_fix(fix);
                } else {
                    for bound in unused_names {
                        ctx.report(
                            &registry::UNUSED_IMPORT,
                            bound.span,
                            format!("imported item `{}` is never used", bound.value),
                        );
                    }
                }
            }
            ImportTarget::Glob => {}
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn walk_stmt(
    ctx: &mut LintContext<'_>,
    hir: &Program,
    file_id: FileId,
    ast: &Ast,
    src: &str,
    stmt_id: StmtId,
    is_executable: bool,
    inside_private_sub: bool,
    referenced_defs: &BTreeSet<DefinitionId>,
    outer_live: &mut BTreeMap<String, Span>,
) {
    let spanned = ast.stmt(stmt_id);
    let stmt = &spanned.value;

    // `unreachable_pub`: `pub` item inside a private `sub`.
    if inside_private_sub
        && stmt.visibility == Visibility::Public
        && ctx.may_fire(&registry::UNREACHABLE_PUB)
        && src
            .get(spanned.span.start..spanned.span.start.saturating_add(4))
            .is_some_and(|s| s == "pub ")
    {
        let pub_span = Span::new(file_id, spanned.span.start, spanned.span.start + 4);
        let fix = Fix {
            id: format!("unreachable_pub:{}:{}", file_id.0, pub_span.start),
            title: "Remove unreachable `pub` modifier".to_owned(),
            safety: FixSafety::Safe,
            kind: FixKind::Lint,
            is_preferred: true,
            is_organize_imports: false,
            edits: vec![TextEdit::new(pub_span, "")],
            delta: None,
        };
        ctx.report(
            &registry::UNREACHABLE_PUB,
            Span::new(file_id, spanned.span.start, spanned.span.start + 3),
            "`pub` declaration inside a private `sub` is unreachable outside this module",
        )
        .with_fix(fix);
    }

    match &stmt.kind {
        StmtKind::Function(fun) => {
            let is_main = is_executable && fun.name.value == "main";
            if stmt.visibility == Visibility::Private
                && !is_main
                && !fun.name.value.starts_with('_')
                && fun.body.is_some()
                && ctx.may_fire(&registry::UNUSED_PRIVATE_ITEM)
                && let Some(def_id) = find_def_at(hir, fun.name.span)
                && !referenced_defs.contains(&def_id)
            {
                ctx.report(
                    &registry::UNUSED_PRIVATE_ITEM,
                    fun.name.span,
                    format!(
                        "private function `{}` is never called or referenced",
                        fun.name.value
                    ),
                );
            }

            // `unused_generic_param` on functions.
            if ctx.may_fire(&registry::UNUSED_GENERIC_PARAM) {
                for g in &fun.generics {
                    if !g.name.value.starts_with('_')
                        && let Some(def_id) = find_def_at(hir, g.name.span)
                        && !referenced_defs.contains(&def_id)
                    {
                        ctx.report(
                            &registry::UNUSED_GENERIC_PARAM,
                            g.name.span,
                            format!("generic parameter `{}` is never used", g.name.value),
                        );
                    }
                }
            }

            // `unused_param` (exempt bodyless primitives, `_`-prefixed, and linear/Result params).
            if let Some(body_id) = fun.body {
                let mut fn_live = outer_live.clone();
                for p in &fun.signature.params {
                    if let Some(name) = &p.name {
                        if matches!(p.mode, Mode::Mut | Mode::Shared | Mode::Ref) {
                            fn_live.insert(name.value.clone(), name.span);
                        }
                        if (p.mode == Mode::Plain || p.mode == Mode::Ref)
                            && !name.value.starts_with('_')
                            && ctx.may_fire(&registry::UNUSED_PARAM)
                            && let Some(def_id) = find_def_at(hir, name.span)
                            && !referenced_defs.contains(&def_id)
                            && !is_must_consume_or_result(ctx, def_id)
                        {
                            let insert = Span::new(file_id, name.span.start, name.span.start);
                            let fix = Fix {
                                id: format!("unused_param:{}:{}", file_id.0, name.span.start),
                                title: format!("Prefix parameter with `_`: `_{}`", name.value),
                                safety: FixSafety::Safe,
                                kind: FixKind::Lint,
                                is_preferred: true,
                                is_organize_imports: false,
                                edits: vec![TextEdit::new(insert, "_")],
                                delta: None,
                            };
                            ctx.report(
                                &registry::UNUSED_PARAM,
                                name.span,
                                format!("parameter `{}` is never used", name.value),
                            )
                            .with_fix(fix);
                        }
                    }
                }
                for &h in &fun.helpers {
                    walk_stmt(
                        ctx,
                        hir,
                        file_id,
                        ast,
                        src,
                        h,
                        false,
                        false,
                        referenced_defs,
                        &mut fn_live,
                    );
                }
                walk_expr(
                    ctx,
                    hir,
                    file_id,
                    ast,
                    src,
                    body_id,
                    referenced_defs,
                    &fn_live,
                );
            }
        }
        StmtKind::Type(decl) => {
            if stmt.visibility == Visibility::Private
                && !decl.name.value.starts_with('_')
                && ctx.may_fire(&registry::UNUSED_PRIVATE_ITEM)
                && let Some(def_id) = find_def_at(hir, decl.name.span)
                && !referenced_defs.contains(&def_id)
                && !any_variant_referenced(hir, def_id, referenced_defs)
            {
                ctx.report(
                    &registry::UNUSED_PRIVATE_ITEM,
                    decl.name.span,
                    format!("private type `{}` is never used", decl.name.value),
                );
            }
            // `unused_generic_param`: transparent `type A<T> = ...` ONLY (NEVER nominal/opaque/sum!).
            if decl.kind == ril_syntax::syntax::TypeKind::Alias
                && matches!(decl.definition, TypeDefinition::Data(_))
                && ctx.may_fire(&registry::UNUSED_GENERIC_PARAM)
            {
                for g in &decl.generics {
                    if !g.name.value.starts_with('_')
                        && let Some(def_id) = find_def_at(hir, g.name.span)
                        && !referenced_defs.contains(&def_id)
                    {
                        ctx.report(
                            &registry::UNUSED_GENERIC_PARAM,
                            g.name.span,
                            format!(
                                "generic parameter `{}` on type alias is never used",
                                g.name.value
                            ),
                        );
                    }
                }
            }
        }
        StmtKind::Effect { name, .. } => {
            if stmt.visibility == Visibility::Private
                && !name.value.starts_with('_')
                && ctx.may_fire(&registry::UNUSED_PRIVATE_ITEM)
                && let Some(def_id) = find_def_at(hir, name.span)
                && !referenced_defs.contains(&def_id)
            {
                ctx.report(
                    &registry::UNUSED_PRIVATE_ITEM,
                    name.span,
                    format!("private effect `{}` is never used", name.value),
                );
            }
        }
        StmtKind::Sub { name, items } => {
            let sub_is_private = inside_private_sub || stmt.visibility == Visibility::Private;
            let mut sub_live = BTreeMap::new();
            for &item in items {
                walk_stmt(
                    ctx,
                    hir,
                    file_id,
                    ast,
                    src,
                    item,
                    false,
                    sub_is_private,
                    referenced_defs,
                    &mut sub_live,
                );
            }
            if stmt.visibility == Visibility::Private
                && !name.value.starts_with('_')
                && ctx.may_fire(&registry::UNUSED_PRIVATE_ITEM)
                && let Some(def_id) = find_def_at(hir, name.span)
                && !referenced_defs.contains(&def_id)
            {
                ctx.report(
                    &registry::UNUSED_PRIVATE_ITEM,
                    name.span,
                    format!("private submodule `{}` is never referenced", name.value),
                );
            }
        }
        StmtKind::Binding {
            storage,
            pattern,
            value,
            fallback,
            ..
        } => {
            if let Some(v) = value {
                walk_expr(ctx, hir, file_id, ast, src, *v, referenced_defs, outer_live);
            }
            if let Some(fb) = fallback {
                walk_expr(
                    ctx,
                    hir,
                    file_id,
                    ast,
                    src,
                    *fb,
                    referenced_defs,
                    outer_live,
                );
            }
            // Check unused local bindings (plain `let` / `let ref` only; `var`/`mut`/`^mut` are E0527)
            // and `shadowed_live_binding` when inner block shadows an outer live binding.
            let is_plain_or_ref =
                !storage.variable && matches!(storage.mode, Mode::Plain | Mode::Ref);
            let is_live =
                storage.variable || matches!(storage.mode, Mode::Mut | Mode::Shared | Mode::Ref);
            check_pattern_binders(
                ctx,
                hir,
                file_id,
                ast,
                *pattern,
                is_plain_or_ref,
                is_live,
                referenced_defs,
                outer_live,
            );
        }
        StmtKind::Defer(e) => {
            walk_expr(ctx, hir, file_id, ast, src, *e, referenced_defs, outer_live);
        }
        StmtKind::With(h) => {
            walk_expr(
                ctx,
                hir,
                file_id,
                ast,
                src,
                h.value,
                referenced_defs,
                outer_live,
            );
        }
        StmtKind::Expr(e) => {
            walk_expr(ctx, hir, file_id, ast, src, *e, referenced_defs, outer_live);
        }
        StmtKind::Import(_) | StmtKind::Error => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn check_pattern_binders(
    ctx: &mut LintContext<'_>,
    hir: &Program,
    file_id: FileId,
    ast: &Ast,
    pat_id: PatternId,
    check_unused: bool,
    outer_is_live: bool,
    referenced_defs: &BTreeSet<DefinitionId>,
    outer_live: &mut BTreeMap<String, Span>,
) {
    match &ast.pattern(pat_id).value {
        Pattern::Binding(st, name) => {
            let live = outer_is_live
                || st.variable
                || matches!(st.mode, Mode::Mut | Mode::Shared | Mode::Ref);
            if let Some(&prev_span) = outer_live.get(&name.value)
                && prev_span != name.span
                && ctx.may_fire(&registry::SHADOWED_LIVE_BINDING)
            {
                ctx.report(
                    &registry::SHADOWED_LIVE_BINDING,
                    name.span,
                    format!("binding `{}` shadows an outer live binding", name.value),
                )
                .with_label(prev_span, "outer live binding declared here");
            }
            if live {
                outer_live.insert(name.value.clone(), name.span);
            }
            let local_plain_or_ref =
                check_unused && !st.variable && matches!(st.mode, Mode::Plain | Mode::Ref);
            if local_plain_or_ref
                && !name.value.starts_with('_')
                && ctx.may_fire(&registry::UNUSED_BINDING)
                && let Some(def_id) = find_def_at(hir, name.span)
                && hir.definition(def_id).kind == DefinitionKind::Local
                && !referenced_defs.contains(&def_id)
                && !is_must_consume_or_result(ctx, def_id)
            {
                let insert = Span::new(file_id, name.span.start, name.span.start);
                let fix = Fix {
                    id: format!("unused_binding:{}:{}", file_id.0, name.span.start),
                    title: format!("Prefix unused binding with `_`: `_{}`", name.value),
                    safety: FixSafety::Safe,
                    kind: FixKind::Lint,
                    is_preferred: true,
                    is_organize_imports: false,
                    edits: vec![TextEdit::new(insert, "_")],
                    delta: None,
                };
                ctx.report(
                    &registry::UNUSED_BINDING,
                    name.span,
                    format!("binding `{}` is never used", name.value),
                )
                .with_fix(fix);
            }
        }
        Pattern::Tuple(ps) | Pattern::Wrap(_, ps) => {
            for &p in ps {
                check_pattern_binders(
                    ctx,
                    hir,
                    file_id,
                    ast,
                    p,
                    check_unused,
                    outer_is_live,
                    referenced_defs,
                    outer_live,
                );
            }
        }
        Pattern::Slice { elements, .. } => {
            for &p in elements {
                check_pattern_binders(
                    ctx,
                    hir,
                    file_id,
                    ast,
                    p,
                    check_unused,
                    outer_is_live,
                    referenced_defs,
                    outer_live,
                );
            }
        }
        Pattern::Constructor(_, Some(ps)) => {
            for &p in ps {
                check_pattern_binders(
                    ctx,
                    hir,
                    file_id,
                    ast,
                    p,
                    check_unused,
                    outer_is_live,
                    referenced_defs,
                    outer_live,
                );
            }
        }
        Pattern::Record { fields, .. } => {
            for f in fields {
                if let Some(p) = f.pattern {
                    check_pattern_binders(
                        ctx,
                        hir,
                        file_id,
                        ast,
                        p,
                        check_unused,
                        outer_is_live,
                        referenced_defs,
                        outer_live,
                    );
                } else {
                    let live = outer_is_live
                        || f.storage.variable
                        || matches!(f.storage.mode, Mode::Mut | Mode::Shared | Mode::Ref);
                    if live {
                        outer_live.insert(f.name.value.clone(), f.name.span);
                    }
                }
            }
        }
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn walk_expr(
    ctx: &mut LintContext<'_>,
    hir: &Program,
    file_id: FileId,
    ast: &Ast,
    src: &str,
    expr_id: ExprId,
    referenced_defs: &BTreeSet<DefinitionId>,
    outer_live: &BTreeMap<String, Span>,
) {
    match &ast.expr(expr_id).value {
        Expr::Block {
            statements,
            helpers,
        } => {
            check_redundant_with_shadow(ctx, file_id, ast, statements);
            let mut local_live = outer_live.clone();
            for &s in statements {
                walk_stmt(
                    ctx,
                    hir,
                    file_id,
                    ast,
                    src,
                    s,
                    false,
                    false,
                    referenced_defs,
                    &mut local_live,
                );
            }
            for &h in helpers {
                walk_stmt(
                    ctx,
                    hir,
                    file_id,
                    ast,
                    src,
                    h,
                    false,
                    false,
                    referenced_defs,
                    &mut local_live,
                );
            }
        }
        Expr::With {
            handlers,
            statements,
            helpers,
        } => {
            for h in handlers {
                walk_expr(
                    ctx,
                    hir,
                    file_id,
                    ast,
                    src,
                    h.value,
                    referenced_defs,
                    outer_live,
                );
            }
            check_redundant_with_shadow(ctx, file_id, ast, statements);
            let mut local_live = outer_live.clone();
            for &s in statements {
                walk_stmt(
                    ctx,
                    hir,
                    file_id,
                    ast,
                    src,
                    s,
                    false,
                    false,
                    referenced_defs,
                    &mut local_live,
                );
            }
            for &h in helpers {
                walk_stmt(
                    ctx,
                    hir,
                    file_id,
                    ast,
                    src,
                    h,
                    false,
                    false,
                    referenced_defs,
                    &mut local_live,
                );
            }
        }
        Expr::If {
            condition, yes, no, ..
        } => {
            let mut yes_live = outer_live.clone();
            match condition {
                ril_syntax::syntax::Condition::Expr(c) => {
                    walk_expr(ctx, hir, file_id, ast, src, *c, referenced_defs, outer_live);
                }
                ril_syntax::syntax::Condition::Binding {
                    mode,
                    pattern,
                    value,
                } => {
                    walk_expr(
                        ctx,
                        hir,
                        file_id,
                        ast,
                        src,
                        *value,
                        referenced_defs,
                        outer_live,
                    );
                    let is_live = matches!(mode, Mode::Mut | Mode::Shared | Mode::Ref);
                    check_pattern_binders(
                        ctx,
                        hir,
                        file_id,
                        ast,
                        *pattern,
                        !is_live,
                        is_live,
                        referenced_defs,
                        &mut yes_live,
                    );
                }
            }
            walk_expr(
                ctx,
                hir,
                file_id,
                ast,
                src,
                *yes,
                referenced_defs,
                &yes_live,
            );
            if let Some(n) = no {
                walk_expr(ctx, hir, file_id, ast, src, *n, referenced_defs, outer_live);
            }
        }
        Expr::While { condition, body } => {
            let mut body_live = outer_live.clone();
            match condition {
                ril_syntax::syntax::Condition::Expr(c) => {
                    walk_expr(ctx, hir, file_id, ast, src, *c, referenced_defs, outer_live);
                }
                ril_syntax::syntax::Condition::Binding {
                    mode,
                    pattern,
                    value,
                } => {
                    walk_expr(
                        ctx,
                        hir,
                        file_id,
                        ast,
                        src,
                        *value,
                        referenced_defs,
                        outer_live,
                    );
                    let is_live = matches!(mode, Mode::Mut | Mode::Shared | Mode::Ref);
                    check_pattern_binders(
                        ctx,
                        hir,
                        file_id,
                        ast,
                        *pattern,
                        !is_live,
                        is_live,
                        referenced_defs,
                        &mut body_live,
                    );
                }
            }
            walk_expr(
                ctx,
                hir,
                file_id,
                ast,
                src,
                *body,
                referenced_defs,
                &body_live,
            );
        }
        Expr::For {
            mode,
            iterable,
            pattern,
            body,
        } => {
            walk_expr(
                ctx,
                hir,
                file_id,
                ast,
                src,
                *iterable,
                referenced_defs,
                outer_live,
            );
            let mut body_live = outer_live.clone();
            let is_live = matches!(mode, Mode::Mut | Mode::Shared | Mode::Ref);
            check_pattern_binders(
                ctx,
                hir,
                file_id,
                ast,
                *pattern,
                !is_live,
                is_live,
                referenced_defs,
                &mut body_live,
            );
            walk_expr(
                ctx,
                hir,
                file_id,
                ast,
                src,
                *body,
                referenced_defs,
                &body_live,
            );
        }
        Expr::Match { value, arms, .. } => {
            walk_expr(
                ctx,
                hir,
                file_id,
                ast,
                src,
                *value,
                referenced_defs,
                outer_live,
            );
            for arm in arms {
                let mut arm_live = outer_live.clone();
                check_pattern_binders(
                    ctx,
                    hir,
                    file_id,
                    ast,
                    arm.pattern,
                    true,
                    false,
                    referenced_defs,
                    &mut arm_live,
                );
                if let Some(g) = arm.guard {
                    walk_expr(ctx, hir, file_id, ast, src, g, referenced_defs, &arm_live);
                }
                walk_expr(
                    ctx,
                    hir,
                    file_id,
                    ast,
                    src,
                    arm.body,
                    referenced_defs,
                    &arm_live,
                );
            }
        }
        Expr::Closure { body, .. } => {
            walk_expr(
                ctx,
                hir,
                file_id,
                ast,
                src,
                *body,
                referenced_defs,
                outer_live,
            );
        }
        Expr::Call { callee, args } => {
            walk_expr(
                ctx,
                hir,
                file_id,
                ast,
                src,
                *callee,
                referenced_defs,
                outer_live,
            );
            for a in args {
                walk_expr(
                    ctx,
                    hir,
                    file_id,
                    ast,
                    src,
                    a.value,
                    referenced_defs,
                    outer_live,
                );
            }
        }
        Expr::Binary { left, right, .. } => {
            walk_expr(
                ctx,
                hir,
                file_id,
                ast,
                src,
                *left,
                referenced_defs,
                outer_live,
            );
            walk_expr(
                ctx,
                hir,
                file_id,
                ast,
                src,
                *right,
                referenced_defs,
                outer_live,
            );
        }
        Expr::Pipeline { value, target, .. } => {
            walk_expr(
                ctx,
                hir,
                file_id,
                ast,
                src,
                *value,
                referenced_defs,
                outer_live,
            );
            walk_expr(
                ctx,
                hir,
                file_id,
                ast,
                src,
                *target,
                referenced_defs,
                outer_live,
            );
        }
        Expr::Unary { value, .. }
        | Expr::Meta(value)
        | Expr::Cast { value, .. }
        | Expr::Member { base: value, .. }
        | Expr::Transfer {
            value: Some(value), ..
        } => {
            walk_expr(
                ctx,
                hir,
                file_id,
                ast,
                src,
                *value,
                referenced_defs,
                outer_live,
            );
        }
        Expr::Index { base, index, .. } => {
            walk_expr(
                ctx,
                hir,
                file_id,
                ast,
                src,
                *base,
                referenced_defs,
                outer_live,
            );
            walk_expr(
                ctx,
                hir,
                file_id,
                ast,
                src,
                *index,
                referenced_defs,
                outer_live,
            );
        }
        Expr::Array(items) | Expr::Tuple(items) => {
            for &e in items {
                walk_expr(ctx, hir, file_id, ast, src, e, referenced_defs, outer_live);
            }
        }
        Expr::Map(entries) => {
            for &(k, v) in entries {
                walk_expr(ctx, hir, file_id, ast, src, k, referenced_defs, outer_live);
                walk_expr(ctx, hir, file_id, ast, src, v, referenced_defs, outer_live);
            }
        }
        Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = f.value {
                    walk_expr(ctx, hir, file_id, ast, src, v, referenced_defs, outer_live);
                }
            }
        }
        Expr::Wrap { args, .. } => {
            for a in args {
                walk_expr(
                    ctx,
                    hir,
                    file_id,
                    ast,
                    src,
                    a.value,
                    referenced_defs,
                    outer_live,
                );
            }
        }
        _ => {}
    }
}

fn check_redundant_with_shadow(
    ctx: &mut LintContext<'_>,
    file_id: FileId,
    ast: &Ast,
    statements: &[StmtId],
) {
    if !ctx.may_fire(&registry::REDUNDANT_WITH_SHADOW) {
        return;
    }
    for pair in statements.windows(2) {
        let (Some(&first), Some(&second)) = (pair.first(), pair.get(1)) else {
            continue;
        };
        let s1 = ast.stmt(first);
        let s2 = ast.stmt(second);
        if let (StmtKind::With(h1), StmtKind::With(h2)) = (&s1.value.kind, &s2.value.kind) {
            let op1: Vec<&str> = h1
                .operation
                .segments
                .iter()
                .map(|s| s.name.value.as_str())
                .collect();
            let op2: Vec<&str> = h2
                .operation
                .segments
                .iter()
                .map(|s| s.name.value.as_str())
                .collect();
            if op1 == op2 {
                let fix = Fix {
                    id: format!("redundant_with_shadow:{}:{}", file_id.0, s1.span.start),
                    title: "Remove shadowed `with` handler".to_owned(),
                    safety: FixSafety::Unsafe,
                    kind: FixKind::Lint,
                    is_preferred: false,
                    is_organize_imports: false,
                    edits: vec![TextEdit::new(s1.span, "")],
                    delta: None,
                };
                ctx.report(
                    &registry::REDUNDANT_WITH_SHADOW,
                    s1.span,
                    format!(
                        "`with {}` is immediately shadowed by another handler",
                        op1.join("::")
                    ),
                )
                .with_label(s2.span, "shadowed here")
                .with_fix(fix);
            }
        }
    }
}

fn find_def_at(hir: &Program, name_span: Span) -> Option<DefinitionId> {
    hir.definitions()
        .find(|(_, def)| def.name.span == name_span)
        .map(|(id, _)| id)
}

fn any_variant_referenced(
    hir: &Program,
    sum_id: DefinitionId,
    referenced: &BTreeSet<DefinitionId>,
) -> bool {
    hir.definitions()
        .any(|(id, def)| def.kind == DefinitionKind::Variant(sum_id) && referenced.contains(&id))
}

fn is_must_consume_or_result(ctx: &LintContext<'_>, def_id: DefinitionId) -> bool {
    let Some(typed) = ctx.typed else {
        return false;
    };
    let Some(ty) = typed.bindings.get(&def_id) else {
        return false;
    };
    typed.is_must_consume(ty) || ty.is_result(&typed.hir)
}

fn module_path_key(imp: &Import) -> String {
    let mut key = String::new();
    if let Some(file) = &imp.file {
        for (i, seg) in file.iter().enumerate() {
            if i > 0 {
                key.push('/');
            }
            key.push_str(&seg.value);
        }
    }
    for m in &imp.modules {
        if !key.is_empty() {
            key.push_str("::");
        }
        key.push_str(&m.value);
    }
    key
}

fn default_module_alias(imp: &Import) -> Option<String> {
    if let Some(last) = imp.modules.last() {
        return Some(last.value.clone());
    }
    let stem = imp.file.as_ref()?.last()?.value.as_str();
    let mut pascal = String::new();
    for part in stem.split('_') {
        let mut chars = part.chars();
        if let Some(first) = chars.next() {
            pascal.extend(first.to_uppercase());
            pascal.push_str(chars.as_str());
        }
    }
    (!pascal.is_empty()).then_some(pascal)
}

fn line_removal_span(src: &str, span: Span) -> Span {
    let start = src
        .get(..span.start)
        .and_then(|p| p.rfind('\n'))
        .map_or(0, |i| i + 1);
    let end = src
        .get(span.end..)
        .and_then(|s| s.find('\n'))
        .map_or(src.len(), |i| span.end + i + 1);
    Span::new(span.file, start, end)
}
