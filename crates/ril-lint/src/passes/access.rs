//! Access & Behavior lint pass: Ril-specific snapshot/mode/effect-handler/totality rules.

use ril_hir::{DefinitionKind, Intrinsic};
use ril_sema::{
    access::Analysis,
    behavior::{self, WitnessStep},
    ty::{Ty, TypedProgram},
};
use ril_source::{
    fix::{Fix, FixKind, FixSafety, TextEdit},
    span::{FileId, Span},
};
use ril_syntax::syntax::{Ast, Expr, ExprId, Mode, StmtId, StmtKind, Visibility};

use crate::{LintContext, registry};

pub fn run(ctx: &mut LintContext<'_>) {
    let (Some(typed), Some(analysis)) = (ctx.typed, ctx.analysis) else {
        return;
    };

    // 1. `unexpected_behavior_in_pub`: audit `pub fn` for implicit panic/abort/diverge.
    if ctx.may_fire(&registry::UNEXPECTED_BEHAVIOR_IN_PUB) {
        for (def_id, def) in typed.hir.definitions() {
            if def.kind != DefinitionKind::Function
                || def.visibility != Visibility::Public
                || !ctx.is_target_file(def.name.span.file)
            {
                continue;
            }
            let Some(beh) = analysis.behavior.summaries.get(&def_id) else {
                continue;
            };
            let mut tags = Vec::new();
            if beh.may_panic {
                tags.push("@panic");
            }
            if beh.may_abort {
                tags.push("@abort");
            }
            if beh.may_diverge {
                tags.push("@diverge");
            }
            if !tags.is_empty() {
                let mut builder = ctx.report(
                    &registry::UNEXPECTED_BEHAVIOR_IN_PUB,
                    def.name.span,
                    format!(
                        "public function `{}` has implicit behavior: {}",
                        def.name.value,
                        tags.join(", ")
                    ),
                );
                if let Some(w) = analysis.behavior.witnesses.get(&def_id) {
                    if let Some(chain) = format_witness(&w.may_panic) {
                        builder = builder.with_note(format!("panic path: {chain}"));
                    }
                    if let Some(chain) = format_witness(&w.may_abort) {
                        builder = builder.with_note(format!("abort path: {chain}"));
                    }
                    if let Some(chain) = format_witness(&w.may_diverge) {
                        builder = builder.with_note(format!("diverge path: {chain}"));
                    }
                }
                let _ = builder;
            }
        }
    }

    // 2. `unused_effect_handler`: check `analysis.behavior.with_sites` against `effect_calls`.
    if ctx.may_fire(&registry::UNUSED_EFFECT_HANDLER) {
        for site in &analysis.behavior.with_sites {
            if !ctx.is_target_file(site.span.file) {
                continue;
            }
            let bound = analysis
                .behavior
                .effect_calls
                .iter()
                .any(|call| call.bound_by == Some(site.span));
            if bound {
                continue;
            }
            // Conservative exclusion: suppress if governed scope calls any open-`@` callback,
            // `unwind_ctl`, or references the handler effect in a pruned `meta if` branch.
            let file = typed.hir.file(site.scope.file);
            if scope_may_dispatch_dynamically(typed, &file.ast, site.scope) {
                continue;
            }
            ctx.report(
                &registry::UNUSED_EFFECT_HANDLER,
                site.span,
                format!(
                    "`with {}` handler is never exercised in its governed scope",
                    site.op
                ),
            );
        }
    }

    // 3. Per-file AST walks for `redundant_clone`, `noop_derive`, `clone_in_loop`, `unused_pure_expr`.
    let file_ids: Vec<FileId> = ctx.target_files.iter().copied().collect();
    for file_id in file_ids {
        let Some(file) = typed.hir.files().find(|f| f.id == file_id) else {
            continue;
        };
        let ast = file.ast.clone();
        let src = ctx.source_text(file_id).to_owned();
        for &stmt_id in &ast.items {
            walk_stmt(ctx, typed, analysis, file_id, &ast, &src, stmt_id, false);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn walk_stmt(
    ctx: &mut LintContext<'_>,
    typed: &TypedProgram,
    analysis: &Analysis,
    file_id: FileId,
    ast: &Ast,
    src: &str,
    stmt_id: StmtId,
    in_loop: bool,
) {
    let spanned = ast.stmt(stmt_id);
    if ctx.is_in_pruned_meta_branch(spanned.span) {
        return;
    }
    match &spanned.value.kind {
        StmtKind::Function(fun) => {
            for &h in &fun.helpers {
                walk_stmt(ctx, typed, analysis, file_id, ast, src, h, false);
            }
            if let Some(body) = fun.body {
                walk_expr(ctx, typed, analysis, file_id, ast, src, body, false);
            }
        }
        StmtKind::Sub { items, .. } => {
            for &item in items {
                walk_stmt(ctx, typed, analysis, file_id, ast, src, item, false);
            }
        }
        StmtKind::Binding {
            storage,
            value: Some(val_id),
            fallback,
            ..
        } => {
            // `redundant_clone`: `let x = clone(snap)` where binding is plain immutable
            // AND `snap` is already a deeply immutable snapshot (not `ref`/`mut`/`^mut`).
            let needs_new = storage.mode == Mode::Mut || storage.mode == Mode::Shared;
            if !needs_new && ctx.may_fire(&registry::REDUNDANT_CLONE) {
                check_redundant_clone(ctx, typed, file_id, ast, src, *val_id);
            }
            walk_expr(ctx, typed, analysis, file_id, ast, src, *val_id, in_loop);
            if let Some(fb) = fallback {
                walk_expr(ctx, typed, analysis, file_id, ast, src, *fb, in_loop);
            }
        }
        StmtKind::Defer(e) => {
            walk_expr(ctx, typed, analysis, file_id, ast, src, *e, in_loop);
        }
        StmtKind::With(h) => {
            walk_expr(ctx, typed, analysis, file_id, ast, src, h.value, in_loop);
        }
        StmtKind::Expr(e) => {
            walk_expr(ctx, typed, analysis, file_id, ast, src, *e, in_loop);
        }
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn walk_expr(
    ctx: &mut LintContext<'_>,
    typed: &TypedProgram,
    analysis: &Analysis,
    file_id: FileId,
    ast: &Ast,
    src: &str,
    expr_id: ExprId,
    in_loop: bool,
) {
    let spanned = ast.expr(expr_id);
    let span = spanned.span;
    if ctx.is_in_pruned_meta_branch(span) {
        return;
    }

    match &spanned.value {
        Expr::Block {
            statements,
            helpers,
        } => {
            check_unused_pure_stmts(ctx, typed, analysis, ast, statements);
            for &s in statements {
                walk_stmt(ctx, typed, analysis, file_id, ast, src, s, in_loop);
            }
            for &h in helpers {
                walk_stmt(ctx, typed, analysis, file_id, ast, src, h, false);
            }
        }
        Expr::With {
            handlers,
            statements,
            helpers,
        } => {
            for h in handlers {
                walk_expr(ctx, typed, analysis, file_id, ast, src, h.value, in_loop);
            }
            check_unused_pure_stmts(ctx, typed, analysis, ast, statements);
            for &s in statements {
                walk_stmt(ctx, typed, analysis, file_id, ast, src, s, in_loop);
            }
            for &h in helpers {
                walk_stmt(ctx, typed, analysis, file_id, ast, src, h, false);
            }
        }
        Expr::While { condition, body } => {
            match condition {
                ril_syntax::syntax::Condition::Expr(c)
                | ril_syntax::syntax::Condition::Binding { value: c, .. } => {
                    walk_expr(ctx, typed, analysis, file_id, ast, src, *c, true);
                }
            }
            walk_expr(ctx, typed, analysis, file_id, ast, src, *body, true);
        }
        Expr::For { iterable, body, .. } => {
            walk_expr(ctx, typed, analysis, file_id, ast, src, *iterable, in_loop);
            walk_expr(ctx, typed, analysis, file_id, ast, src, *body, true);
        }
        Expr::Call { callee, args } => {
            // `clone_in_loop`
            if in_loop
                && ctx.may_fire(&registry::CLONE_IN_LOOP)
                && is_intrinsic_call(typed, ast, *callee, Intrinsic::Clone)
            {
                ctx.report(
                    &registry::CLONE_IN_LOOP,
                    span,
                    "`clone(...)` inside a loop deep-copies the entire `SharedObject` graph every iteration",
                )
                .with_help("hoist invariant clones outside the loop or share immutable snapshots");
            }

            // `noop_derive`: `derive(x, \mut _d -> ())` with zero writes to `d`.
            if is_intrinsic_call(typed, ast, *callee, Intrinsic::Derive)
                && args.len() == 2
                && let (Some(base_arg), Some(updater_arg)) = (args.first(), args.get(1))
                && ctx.may_fire(&registry::NOOP_DERIVE)
                && is_noop_derive_closure(ast, updater_arg.value)
            {
                let base_span = ast.expr(base_arg.value).span;
                let mut builder = ctx.report(
                    &registry::NOOP_DERIVE,
                    span,
                    "`derive` updater performs no writes on its `Derived<T>` handle",
                );
                if let Some(base_txt) = src.get(base_span.start..base_span.end) {
                    let fix = Fix {
                        id: format!("noop_derive:{}:{}", file_id.0, span.start),
                        title: format!("Replace no-op `derive` with `{base_txt}`"),
                        safety: FixSafety::Safe,
                        kind: FixKind::Lint,
                        is_preferred: true,
                        is_organize_imports: false,
                        edits: vec![TextEdit::new(span, base_txt.to_owned())],
                        delta: None,
                    };
                    builder = builder.with_fix(fix);
                }
                let _ = builder;
            }

            walk_expr(ctx, typed, analysis, file_id, ast, src, *callee, in_loop);
            for a in args {
                walk_expr(ctx, typed, analysis, file_id, ast, src, a.value, in_loop);
            }
        }
        Expr::Pipeline { value, target, .. } => {
            // `x |> derive \mut _d -> ()`
            if ctx.may_fire(&registry::NOOP_DERIVE)
                && let Expr::Call { callee, args } = &ast.expr(*target).value
                && is_intrinsic_call(typed, ast, *callee, Intrinsic::Derive)
                && args.len() == 1
                && let Some(updater_arg) = args.first()
                && is_noop_derive_closure(ast, updater_arg.value)
            {
                let base_span = ast.expr(*value).span;
                let mut builder = ctx.report(
                    &registry::NOOP_DERIVE,
                    span,
                    "`derive` updater performs no writes on its `Derived<T>` handle",
                );
                if let Some(base_txt) = src.get(base_span.start..base_span.end) {
                    let fix = Fix {
                        id: format!("noop_derive:{}:{}", file_id.0, span.start),
                        title: format!("Replace no-op `derive` with `{base_txt}`"),
                        safety: FixSafety::Safe,
                        kind: FixKind::Lint,
                        is_preferred: true,
                        is_organize_imports: false,
                        edits: vec![TextEdit::new(span, base_txt.to_owned())],
                        delta: None,
                    };
                    builder = builder.with_fix(fix);
                }
                let _ = builder;
            }
            walk_expr(ctx, typed, analysis, file_id, ast, src, *value, in_loop);
            walk_expr(ctx, typed, analysis, file_id, ast, src, *target, in_loop);
        }
        Expr::If {
            condition, yes, no, ..
        } => {
            match condition {
                ril_syntax::syntax::Condition::Expr(c)
                | ril_syntax::syntax::Condition::Binding { value: c, .. } => {
                    walk_expr(ctx, typed, analysis, file_id, ast, src, *c, in_loop);
                }
            }
            walk_expr(ctx, typed, analysis, file_id, ast, src, *yes, in_loop);
            if let Some(n) = no {
                walk_expr(ctx, typed, analysis, file_id, ast, src, *n, in_loop);
            }
        }
        Expr::Match { value, arms, .. } => {
            walk_expr(ctx, typed, analysis, file_id, ast, src, *value, in_loop);
            for arm in arms {
                if let Some(g) = arm.guard {
                    walk_expr(ctx, typed, analysis, file_id, ast, src, g, in_loop);
                }
                walk_expr(ctx, typed, analysis, file_id, ast, src, arm.body, in_loop);
            }
        }
        Expr::Closure { body, .. } => {
            walk_expr(ctx, typed, analysis, file_id, ast, src, *body, in_loop);
        }
        Expr::Binary { left, right, .. } => {
            walk_expr(ctx, typed, analysis, file_id, ast, src, *left, in_loop);
            walk_expr(ctx, typed, analysis, file_id, ast, src, *right, in_loop);
        }
        Expr::Unary { value, .. }
        | Expr::Meta(value)
        | Expr::Cast { value, .. }
        | Expr::Member { base: value, .. }
        | Expr::Transfer {
            value: Some(value), ..
        } => {
            walk_expr(ctx, typed, analysis, file_id, ast, src, *value, in_loop);
        }
        Expr::Index { base, index, .. } => {
            walk_expr(ctx, typed, analysis, file_id, ast, src, *base, in_loop);
            walk_expr(ctx, typed, analysis, file_id, ast, src, *index, in_loop);
        }
        Expr::Array(items) | Expr::Tuple(items) => {
            for &e in items {
                walk_expr(ctx, typed, analysis, file_id, ast, src, e, in_loop);
            }
        }
        Expr::Map(entries) => {
            for &(k, v) in entries {
                walk_expr(ctx, typed, analysis, file_id, ast, src, k, in_loop);
                walk_expr(ctx, typed, analysis, file_id, ast, src, v, in_loop);
            }
        }
        Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = f.value {
                    walk_expr(ctx, typed, analysis, file_id, ast, src, v, in_loop);
                }
            }
        }
        Expr::Wrap { args, .. } => {
            for a in args {
                walk_expr(ctx, typed, analysis, file_id, ast, src, a.value, in_loop);
            }
        }
        _ => {}
    }
}

fn check_redundant_clone(
    ctx: &mut LintContext<'_>,
    typed: &TypedProgram,
    file_id: FileId,
    ast: &Ast,
    src: &str,
    expr_id: ExprId,
) {
    let span = ast.expr(expr_id).span;
    let Expr::Call { callee, args } = &ast.expr(expr_id).value else {
        return;
    };
    if !is_intrinsic_call(typed, ast, *callee, Intrinsic::Clone) || args.len() != 1 {
        return;
    }
    let Some(arg0) = args.first() else {
        return;
    };
    // If arg carries explicit `ref`/`mut`/`^mut` mode, cloning a live writer is meaningful!
    if arg0.mode != Mode::Plain {
        return;
    }
    let arg_span = ast.expr(arg0.value).span;
    if let Some(arg_txt) = src.get(arg_span.start..arg_span.end) {
        let fix = Fix {
            id: format!("redundant_clone:{}:{}", file_id.0, span.start),
            title: format!("Replace `clone({arg_txt})` with `{arg_txt}`"),
            safety: FixSafety::Safe,
            kind: FixKind::Lint,
            is_preferred: true,
            is_organize_imports: false,
            edits: vec![TextEdit::new(span, arg_txt.to_owned())],
            delta: None,
        };
        ctx.report(
            &registry::REDUNDANT_CLONE,
            span,
            "redundant `clone` on deeply immutable snapshot",
        )
        .with_note("plain bindings in Ril already share deeply immutable snapshots in O(1)")
        .with_fix(fix);
    }
}

fn check_unused_pure_stmts(
    ctx: &mut LintContext<'_>,
    typed: &TypedProgram,
    analysis: &Analysis,
    ast: &Ast,
    statements: &[StmtId],
) {
    if !ctx.may_fire(&registry::UNUSED_PURE_EXPR) || statements.len() < 2 {
        return;
    }
    let last_idx = statements.len() - 1;
    for &stmt_id in statements.get(..last_idx).unwrap_or(&[]) {
        let StmtKind::Expr(e_id) = ast.stmt(stmt_id).value.kind else {
            continue;
        };
        let e_span = ast.expr(e_id).span;
        let Some(ty) = typed.types.get(&e_span) else {
            continue;
        };
        if matches!(ty, Ty::Unit | Ty::Never | Ty::Unknown)
            || ty.is_result(&typed.hir)
            || ty.is_option(&typed.hir)
        {
            continue;
        }
        if is_observationally_pure_expr(typed, analysis, ast, e_id) {
            ctx.report(
                &registry::UNUSED_PURE_EXPR,
                e_span,
                "pure expression value is unused",
            )
            .with_help("bind the value with `let` or remove the unused expression");
        }
    }
}

fn is_observationally_pure_expr(
    typed: &TypedProgram,
    analysis: &Analysis,
    ast: &Ast,
    expr_id: ExprId,
) -> bool {
    match &ast.expr(expr_id).value {
        Expr::Path(_) | Expr::Literal(_) | Expr::Unit => true,
        Expr::Binary { op, left, right } => {
            !matches!(
                op.value.as_str(),
                "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>="
            ) && !matches!(op.value.as_str(), "/" | "%" | "<<" | ">>")
                && is_observationally_pure_expr(typed, analysis, ast, *left)
                && is_observationally_pure_expr(typed, analysis, ast, *right)
        }
        Expr::Call { callee, args } => {
            let Expr::Path(p) = &ast.expr(*callee).value else {
                return false;
            };
            let Some(def_id) = typed.hir.resolve(p.span).and_then(|r| r.definition()) else {
                return false;
            };
            let pure_fn = if typed.hir.intrinsic(def_id) == Some(Intrinsic::Len) {
                true
            } else if let (Some(callable), Some(summary)) = (
                typed.callables.get(&def_id),
                analysis.summaries.get(&def_id),
            ) {
                let beh = analysis.behavior.summaries.get(&def_id);
                behavior::is_pure(callable, summary)
                    && beh.is_none_or(|b| !b.may_panic && !b.may_abort)
            } else {
                false
            };
            pure_fn
                && args.iter().all(|a| {
                    a.mode == Mode::Plain
                        && is_observationally_pure_expr(typed, analysis, ast, a.value)
                })
        }
        _ => false,
    }
}

fn is_intrinsic_call(typed: &TypedProgram, ast: &Ast, callee: ExprId, want: Intrinsic) -> bool {
    let Expr::Path(p) = &ast.expr(callee).value else {
        return false;
    };
    typed
        .hir
        .resolve(p.span)
        .and_then(|r| r.definition())
        .is_some_and(|id| typed.hir.intrinsic(id) == Some(want))
}

fn is_noop_derive_closure(ast: &Ast, expr_id: ExprId) -> bool {
    let Expr::Closure { body, .. } = &ast.expr(expr_id).value else {
        return false;
    };
    match &ast.expr(*body).value {
        Expr::Unit => true,
        Expr::Block {
            statements,
            helpers,
        } => statements.is_empty() && helpers.is_empty(),
        _ => false,
    }
}

fn scope_may_dispatch_dynamically(typed: &TypedProgram, ast: &Ast, scope: Span) -> bool {
    for node in ast.expressions() {
        if node.span.start < scope.start || node.span.end > scope.end {
            continue;
        }
        if let Expr::Call { callee, .. } = &node.value {
            if let Some(Ty::Callable(c)) = typed.types.get(&ast.expr(*callee).span)
                && (c.open_effects
                    || c.direct_open_effects
                    || !c.effect_vars.is_empty()
                    || c.has_open_effect_param()
                    || !c.effects.is_empty())
            {
                return true;
            }
            if is_intrinsic_call(typed, ast, *callee, Intrinsic::UnwindCtl) {
                return true;
            }
        }
        if matches!(
            node.value,
            Expr::If { is_meta: true, .. } | Expr::Match { is_meta: true, .. }
        ) {
            return true;
        }
    }
    false
}

fn format_witness(steps: &[WitnessStep]) -> Option<String> {
    if steps.is_empty() {
        return None;
    }
    let parts: Vec<String> = steps
        .iter()
        .filter_map(|s| {
            if let Some(call) = &s.call {
                Some(call.clone())
            } else if let Some(cause) = s.cause {
                Some(cause.as_str().to_owned())
            } else {
                s.detail.clone()
            }
        })
        .collect();
    (!parts.is_empty()).then(|| parts.join(" -> "))
}
