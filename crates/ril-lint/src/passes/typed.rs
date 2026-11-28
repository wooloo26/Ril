//! TypedProgram lint pass: type-aware correctness, idiom, and performance rules.

use ril_hir::{DefinitionId, DefinitionKind, GuardKind, Intrinsic};
use ril_sema::ty::{Callable, Ty, TypedProgram};
use ril_source::{
    fix::{Fix, FixKind, FixSafety, TextEdit},
    span::{FileId, Span},
};
use ril_syntax::syntax::{
    Ast, Condition, Expr, ExprId, Function, LiteralKind, Mode, Pattern, StmtId, StmtKind,
    StringPart, Transfer, Type, TypeDefinition,
};

use crate::{LintContext, registry};

pub fn run(ctx: &mut LintContext<'_>) {
    let Some(typed) = ctx.typed else {
        return;
    };
    let file_ids: Vec<FileId> = ctx.target_files.iter().copied().collect();
    for file_id in file_ids {
        let Some(file) = typed.hir.files().find(|f| f.id == file_id) else {
            continue;
        };
        let ast = file.ast.clone();
        let src = ctx.source_text(file_id).to_owned();
        for &stmt_id in &ast.items {
            walk_stmt(ctx, typed, file_id, &ast, &src, stmt_id, false, false);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn walk_stmt(
    ctx: &mut LintContext<'_>,
    typed: &TypedProgram,
    file_id: FileId,
    ast: &Ast,
    src: &str,
    stmt_id: StmtId,
    in_loop: bool,
    in_fallible_fn: bool,
) {
    let spanned = ast.stmt(stmt_id);
    if ctx.is_in_pruned_meta_branch(spanned.span) {
        return;
    }
    match &spanned.value.kind {
        StmtKind::Function(fun) => {
            let fn_def = typed
                .hir
                .definitions()
                .find(|(_, d)| d.name.span == fun.name.span)
                .map(|(id, _)| id);
            let fn_callable = fn_def.and_then(|id| typed.callables.get(&id));
            let fn_fallible = fn_callable.is_some_and(|c| c.result.is_result(&typed.hir));
            check_redundant_proof_base_types(
                ctx,
                typed,
                file_id,
                ast,
                src,
                fun,
                fn_callable.map(|v| &**v),
            );
            for &h in &fun.helpers {
                walk_stmt(ctx, typed, file_id, ast, src, h, false, false);
            }
            if let Some(body) = fun.body {
                check_needless_return(ctx, file_id, ast, src, body);
                walk_expr(ctx, typed, file_id, ast, src, body, false, fn_fallible);
            }
        }
        StmtKind::Sub { items, .. } => {
            for &item in items {
                walk_stmt(ctx, typed, file_id, ast, src, item, false, false);
            }
        }
        StmtKind::Binding {
            pattern,
            value: Some(val_id),
            fallback,
            ..
        } => {
            // `redundant_let_discard`: `let _ = expr` where `ty(expr) == Ty::Unit`.
            if matches!(ast.pattern(*pattern).value, Pattern::Wildcard)
                && fallback.is_none()
                && ctx.may_fire(&registry::REDUNDANT_LET_DISCARD)
            {
                let val_span = ast.expr(*val_id).span;
                if let Some(Ty::Unit) = typed.types.get(&val_span)
                    && let Some(val_txt) = src.get(val_span.start..val_span.end)
                {
                    let fix = Fix {
                        id: format!("redundant_let_discard:{}:{}", file_id.0, spanned.span.start),
                        title: "Remove redundant `let _ =`".to_owned(),
                        safety: FixSafety::Safe,
                        kind: FixKind::Lint,
                        is_preferred: true,
                        is_organize_imports: false,
                        edits: vec![TextEdit::new(spanned.span, val_txt.to_owned())],
                        delta: None,
                    };
                    ctx.report(
                        &registry::REDUNDANT_LET_DISCARD,
                        spanned.span,
                        "redundant `let _ =` on an expression of type `()`",
                    )
                    .with_fix(fix);
                }
            }
            // `prefer_let_else`: `let x = match e { Pat(v) -> v; _ -> return ... }`
            if let Pattern::Binding(_, bind_name) = &ast.pattern(*pattern).value
                && fallback.is_none()
                && ctx.may_fire(&registry::PREFER_LET_ELSE)
                && let Expr::Match {
                    is_meta: false,
                    mode: Mode::Plain,
                    value: scrutinee,
                    arms,
                } = &ast.expr(*val_id).value
                && arms.len() == 2
                && let (Some(a0), Some(a1)) = (arms.first(), arms.get(1))
                && a0.guard.is_none()
                && a1.guard.is_none()
                && matches!(ast.pattern(a1.pattern).value, Pattern::Wildcard)
                && typed.types.get(&ast.expr(a1.body).span) == Some(&Ty::Never)
                && let Expr::Path(p) = &ast.expr(a0.body).value
                && p.segments.len() == 1
            {
                let _ = (bind_name, scrutinee);
                ctx.report(
                    &registry::PREFER_LET_ELSE,
                    spanned.span,
                    "`let x = match ...` with a diverging wildcard arm can use `let ... else`",
                );
            }
            walk_expr(
                ctx,
                typed,
                file_id,
                ast,
                src,
                *val_id,
                in_loop,
                in_fallible_fn,
            );
            if let Some(fb) = fallback {
                walk_expr(ctx, typed, file_id, ast, src, *fb, in_loop, in_fallible_fn);
            }
        }
        StmtKind::Defer(e) => {
            walk_expr(ctx, typed, file_id, ast, src, *e, in_loop, in_fallible_fn);
        }
        StmtKind::With(h) => {
            walk_expr(
                ctx,
                typed,
                file_id,
                ast,
                src,
                h.value,
                in_loop,
                in_fallible_fn,
            );
        }
        StmtKind::Expr(e) => {
            walk_expr(ctx, typed, file_id, ast, src, *e, in_loop, in_fallible_fn);
        }
        _ => {}
    }
}

fn check_needless_return(
    ctx: &mut LintContext<'_>,
    file_id: FileId,
    ast: &Ast,
    src: &str,
    body_id: ExprId,
) {
    if !ctx.may_fire(&registry::NEEDLESS_RETURN) {
        return;
    }
    let Expr::Block { statements, .. } = &ast.expr(body_id).value else {
        return;
    };
    // CRITICAL Ril exclusion: top-level statement `with ctl` gives `return` special answer semantics!
    let has_with_ctl = statements
        .iter()
        .any(|&s| matches!(&ast.stmt(s).value.kind, StmtKind::With(h) if h.is_ctl));
    if has_with_ctl {
        return;
    }
    let Some(&last_stmt) = statements.last() else {
        return;
    };
    if let StmtKind::Expr(last_expr) = ast.stmt(last_stmt).value.kind
        && let Expr::Transfer {
            kind: Transfer::Return,
            value: Some(val_id),
        } = ast.expr(last_expr).value
    {
        let ret_span = ast.expr(last_expr).span;
        let val_span = ast.expr(val_id).span;
        if let Some(val_txt) = src.get(val_span.start..val_span.end) {
            let fix = Fix {
                id: format!("needless_return:{}:{}", file_id.0, ret_span.start),
                title: "Remove unnecessary `return` keyword".to_owned(),
                safety: FixSafety::Safe,
                kind: FixKind::Lint,
                is_preferred: true,
                is_organize_imports: false,
                edits: vec![TextEdit::new(ret_span, val_txt.to_owned())],
                delta: None,
            };
            ctx.report(
                &registry::NEEDLESS_RETURN,
                ret_span,
                "unnecessary `return` on final expression of function",
            )
            .with_fix(fix);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn walk_expr(
    ctx: &mut LintContext<'_>,
    typed: &TypedProgram,
    file_id: FileId,
    ast: &Ast,
    src: &str,
    expr_id: ExprId,
    in_loop: bool,
    in_fallible_fn: bool,
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
            check_block_statements(
                ctx,
                typed,
                file_id,
                ast,
                src,
                statements,
                in_loop,
                in_fallible_fn,
            );
            for &h in helpers {
                walk_stmt(ctx, typed, file_id, ast, src, h, false, false);
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
                    typed,
                    file_id,
                    ast,
                    src,
                    h.value,
                    in_loop,
                    in_fallible_fn,
                );
            }
            check_block_statements(
                ctx,
                typed,
                file_id,
                ast,
                src,
                statements,
                in_loop,
                in_fallible_fn,
            );
            for &h in helpers {
                walk_stmt(ctx, typed, file_id, ast, src, h, false, false);
            }
        }
        Expr::Binary { op, left, right } => {
            let l_span = ast.expr(*left).span;
            let r_span = ast.expr(*right).span;
            let l_txt = src.get(l_span.start..l_span.end).unwrap_or("").trim();
            let r_txt = src.get(r_span.start..r_span.end).unwrap_or("").trim();

            // `self_assignment`: `x = x`
            if op.value == "="
                && l_txt == r_txt
                && is_simple_place(ast, *left)
                && ctx.may_fire(&registry::SELF_ASSIGNMENT)
            {
                ctx.report(
                    &registry::SELF_ASSIGNMENT,
                    span,
                    format!("self-assignment `{l_txt} = {l_txt}` has no effect"),
                );
            }

            // `string_concat_in_loop`: `s = "{s}..."` on outer var str in loop.
            if in_loop
                && op.value == "="
                && matches!(typed.types.get(&l_span), Some(Ty::Str))
                && let Expr::Interpolated(parts) = &ast.expr(*right).value
                && ctx.may_fire(&registry::STRING_CONCAT_IN_LOOP)
            {
                let references_lhs = parts.iter().any(|part| {
                    if let StringPart::Interpolation(e) = part {
                        src.get(ast.expr(*e).span.start..ast.expr(*e).span.end)
                            .map(str::trim)
                            == Some(l_txt)
                    } else {
                        false
                    }
                });
                if references_lhs {
                    ctx.report(
                        &registry::STRING_CONCAT_IN_LOOP,
                        span,
                        "repeated string interpolation onto an outer `var` in a loop is O(n²)",
                    )
                    .with_help(
                        "collect parts into `let mut parts: []str = []` and join with `String::join`",
                    );
                }
            }

            // `self_comparison`: exempt `f64` `==` / `!=` (IEEE-754 NaN test).
            if matches!(op.value.as_str(), "==" | "!=" | "<" | "<=" | ">" | ">=")
                && l_txt == r_txt
                && is_pure_syntactic(ast, *left)
                && ctx.may_fire(&registry::SELF_COMPARISON)
            {
                let is_f64_eq = matches!(op.value.as_str(), "==" | "!=")
                    && matches!(typed.types.get(&l_span), Some(Ty::F64));
                if !is_f64_eq {
                    ctx.report(
                        &registry::SELF_COMPARISON,
                        span,
                        format!(
                            "comparing `{l_txt}` to itself with `{}` is always constant",
                            op.value
                        ),
                    );
                }
            }

            // `erasing_op`: pure `int` `x * 0`, `0 * x`, `0 / x`, `x & 0`, `x ^ x`, `x - x`.
            if matches!(typed.types.get(&l_span), Some(Ty::Int))
                && matches!(typed.types.get(&r_span), Some(Ty::Int))
                && ctx.may_fire(&registry::ERASING_OP)
            {
                let erasing = match op.value.as_str() {
                    "*" | "&" => {
                        (is_zero_int(ast, *right) && is_pure_syntactic(ast, *left))
                            || (is_zero_int(ast, *left) && is_pure_syntactic(ast, *right))
                    }
                    "/" => is_zero_int(ast, *left) && is_pure_syntactic(ast, *right),
                    "^" | "-" => l_txt == r_txt && is_pure_syntactic(ast, *left),
                    _ => false,
                };
                if erasing {
                    ctx.report(
                        &registry::ERASING_OP,
                        span,
                        format!(
                            "integer expression `{l_txt} {} {r_txt}` always evaluates to `0`",
                            op.value
                        ),
                    );
                }
            }

            // `redundant_bool_branch`: `x == true` → `x`, `x == false` → `!x`.
            if op.value == "=="
                && matches!(typed.types.get(&l_span), Some(Ty::Bool))
                && let Expr::Literal(lit) = &ast.expr(*right).value
                && lit.kind == LiteralKind::Bool
                && ctx.may_fire(&registry::REDUNDANT_BOOL_BRANCH)
            {
                let repl = if lit.text == "true" {
                    l_txt.to_owned()
                } else {
                    format!("!{l_txt}")
                };
                let fix = Fix {
                    id: format!("redundant_bool_branch:{}:{}", file_id.0, span.start),
                    title: format!("Simplify to `{repl}`"),
                    safety: FixSafety::Safe,
                    kind: FixKind::Lint,
                    is_preferred: true,
                    is_organize_imports: false,
                    edits: vec![TextEdit::new(span, repl)],
                    delta: None,
                };
                ctx.report(
                    &registry::REDUNDANT_BOOL_BRANCH,
                    span,
                    "redundant comparison with boolean literal",
                )
                .with_fix(fix);
            }

            walk_expr(
                ctx,
                typed,
                file_id,
                ast,
                src,
                *left,
                in_loop,
                in_fallible_fn,
            );
            walk_expr(
                ctx,
                typed,
                file_id,
                ast,
                src,
                *right,
                in_loop,
                in_fallible_fn,
            );
        }
        Expr::If {
            is_meta,
            condition,
            yes,
            no,
        } => {
            if !*is_meta {
                // `unreachable_code` on literal `if false`.
                if let Condition::Expr(c) = condition
                    && is_bool_lit(ast, *c, false)
                    && ctx.may_fire(&registry::UNREACHABLE_CODE)
                {
                    ctx.report(
                        &registry::UNREACHABLE_CODE,
                        ast.expr(*yes).span,
                        "branch under literal `if false` is unreachable",
                    );
                }

                // `identical_branches` and `redundant_bool_branch` (`if c { true } else { false }`).
                if let Some(no_id) = no {
                    let yes_inner = single_block_expr(ast, *yes);
                    let no_inner = single_block_expr(ast, *no_id);
                    if let (Condition::Expr(c), Some(yi), Some(ni)) =
                        (condition, yes_inner, no_inner)
                    {
                        if is_bool_lit(ast, yi, true)
                            && is_bool_lit(ast, ni, false)
                            && ctx.may_fire(&registry::REDUNDANT_BOOL_BRANCH)
                        {
                            let c_txt = src
                                .get(ast.expr(*c).span.start..ast.expr(*c).span.end)
                                .unwrap_or("");
                            let fix = Fix {
                                id: format!("redundant_bool_branch:{}:{}", file_id.0, span.start),
                                title: format!("Simplify to `{c_txt}`"),
                                safety: FixSafety::Safe,
                                kind: FixKind::Lint,
                                is_preferred: true,
                                is_organize_imports: false,
                                edits: vec![TextEdit::new(span, c_txt.to_owned())],
                                delta: None,
                            };
                            ctx.report(
                                &registry::REDUNDANT_BOOL_BRANCH,
                                span,
                                "`if c { true } else { false }` can be simplified to `c`",
                            )
                            .with_fix(fix);
                        } else if is_bool_lit(ast, yi, false)
                            && is_bool_lit(ast, ni, true)
                            && ctx.may_fire(&registry::REDUNDANT_BOOL_BRANCH)
                        {
                            let c_txt = src
                                .get(ast.expr(*c).span.start..ast.expr(*c).span.end)
                                .unwrap_or("");
                            let fix = Fix {
                                id: format!("redundant_bool_branch:{}:{}", file_id.0, span.start),
                                title: format!("Simplify to `!({c_txt})`"),
                                safety: FixSafety::Safe,
                                kind: FixKind::Lint,
                                is_preferred: true,
                                is_organize_imports: false,
                                edits: vec![TextEdit::new(span, format!("!({c_txt})"))],
                                delta: None,
                            };
                            ctx.report(
                                &registry::REDUNDANT_BOOL_BRANCH,
                                span,
                                "`if c { false } else { true }` can be simplified to `!c`",
                            )
                            .with_fix(fix);
                        }
                    }
                    let y_txt = src
                        .get(ast.expr(*yes).span.start..ast.expr(*yes).span.end)
                        .unwrap_or("")
                        .trim();
                    let n_txt = src
                        .get(ast.expr(*no_id).span.start..ast.expr(*no_id).span.end)
                        .unwrap_or("")
                        .trim();
                    if !y_txt.is_empty()
                        && y_txt == n_txt
                        && ctx.may_fire(&registry::IDENTICAL_BRANCHES)
                    {
                        ctx.report(
                            &registry::IDENTICAL_BRANCHES,
                            span,
                            "`if` and `else` branches have identical bodies",
                        );
                    }
                } else if let Condition::Expr(c1) = condition
                    && let Some(inner_if) = single_block_expr(ast, *yes)
                    && let Expr::If {
                        is_meta: false,
                        condition: Condition::Expr(c2),
                        no: None,
                        ..
                    } = ast.expr(inner_if).value
                    && ctx.may_fire(&registry::COLLAPSIBLE_IF)
                {
                    let _ = (c1, c2);
                    ctx.report(
                        &registry::COLLAPSIBLE_IF,
                        span,
                        "nested `if` statements can be collapsed with `&&`",
                    );
                }
            }
            match condition {
                Condition::Expr(c) => {
                    walk_expr(ctx, typed, file_id, ast, src, *c, in_loop, in_fallible_fn);
                }
                Condition::Binding { value, .. } => {
                    walk_expr(
                        ctx,
                        typed,
                        file_id,
                        ast,
                        src,
                        *value,
                        in_loop,
                        in_fallible_fn,
                    );
                }
            }
            walk_expr(ctx, typed, file_id, ast, src, *yes, in_loop, in_fallible_fn);
            if let Some(n) = no {
                walk_expr(ctx, typed, file_id, ast, src, *n, in_loop, in_fallible_fn);
            }
        }
        Expr::While { condition, body } => {
            if let Condition::Expr(c) = condition {
                if is_bool_lit(ast, *c, false) && ctx.may_fire(&registry::UNREACHABLE_CODE) {
                    ctx.report(
                        &registry::UNREACHABLE_CODE,
                        ast.expr(*body).span,
                        "body of `while false` is unreachable",
                    );
                }
                walk_expr(ctx, typed, file_id, ast, src, *c, true, in_fallible_fn);
            } else if let Condition::Binding { value, .. } = condition {
                walk_expr(ctx, typed, file_id, ast, src, *value, true, in_fallible_fn);
            }
            walk_expr(ctx, typed, file_id, ast, src, *body, true, in_fallible_fn);
        }
        Expr::For { iterable, body, .. } => {
            walk_expr(
                ctx,
                typed,
                file_id,
                ast,
                src,
                *iterable,
                in_loop,
                in_fallible_fn,
            );
            walk_expr(ctx, typed, file_id, ast, src, *body, true, in_fallible_fn);
        }
        Expr::Match {
            is_meta,
            value,
            arms,
            ..
        } => {
            if !*is_meta {
                check_match_idioms(ctx, typed, file_id, ast, src, span, *value, arms);
            }
            walk_expr(
                ctx,
                typed,
                file_id,
                ast,
                src,
                *value,
                in_loop,
                in_fallible_fn,
            );
            for arm in arms {
                if let Some(g) = arm.guard {
                    walk_expr(ctx, typed, file_id, ast, src, g, in_loop, in_fallible_fn);
                }
                walk_expr(
                    ctx,
                    typed,
                    file_id,
                    ast,
                    src,
                    arm.body,
                    in_loop,
                    in_fallible_fn,
                );
            }
        }
        Expr::Closure {
            params,
            obligations,
            body,
        } => {
            // `prefer_accessor_shorthand`: `\x -> x.a.b` → `\.a.b`
            if params.len() == 1
                && obligations.effects.is_empty()
                && obligations.state.is_empty()
                && !obligations.open_effects
                && !obligations.open_state
                && let Some(p) = params.first()
                && p.mode == Mode::Plain
                && p.ty.is_none()
                && p.default.is_none()
                && !p.is_meta
                && let Some(p_name) = &p.name
            {
                if ctx.may_fire(&registry::PREFER_ACCESSOR_SHORTHAND)
                    && let Some(chain) = extract_accessor_chain(ast, *body, &p_name.value)
                {
                    let fix = Fix {
                        id: format!("prefer_accessor_shorthand:{}:{}", file_id.0, span.start),
                        title: format!("Use accessor shorthand `\\{chain}`"),
                        safety: FixSafety::Safe,
                        kind: FixKind::Lint,
                        is_preferred: true,
                        is_organize_imports: false,
                        edits: vec![TextEdit::new(span, format!("\\{chain}"))],
                        delta: None,
                    };
                    ctx.report(
                        &registry::PREFER_ACCESSOR_SHORTHAND,
                        span,
                        format!("projection closure can use shorthand `\\{chain}`"),
                    )
                    .with_fix(fix);
                }

                // `redundant_closure`: `\x -> f(x)` → `f`
                if ctx.may_fire(&registry::REDUNDANT_CLOSURE)
                    && let Expr::Call { callee, args } = &ast.expr(*body).value
                    && args.len() == 1
                    && let Some(arg0) = args.first()
                    && arg0.name.is_none()
                    && arg0.mode == Mode::Plain
                    && let Expr::Path(arg_p) = &ast.expr(arg0.value).value
                    && arg_p.segments.len() == 1
                    && arg_p
                        .segments
                        .first()
                        .is_some_and(|s| s.name.value == p_name.value)
                    && let Expr::Path(callee_p) = &ast.expr(*callee).value
                    && let Some(def_id) = typed
                        .hir
                        .resolve(callee_p.span)
                        .and_then(|r| r.definition())
                    && let def = typed.hir.definition(def_id)
                    && def.kind == DefinitionKind::Function
                    && let Some(sig) = typed.callables.get(&def_id)
                    && sig.parameters.len() == 1
                    && sig
                        .parameters
                        .first()
                        .is_some_and(|sp| sp.mode == Mode::Plain && !sp.is_meta)
                    && !fn_is_meta_or_has_proofs(typed, def_id)
                {
                    let callee_txt = src
                        .get(callee_p.span.start..callee_p.span.end)
                        .unwrap_or("");
                    if !callee_txt.is_empty() {
                        let fix = Fix {
                            id: format!("redundant_closure:{}:{}", file_id.0, span.start),
                            title: format!("Replace closure with `{callee_txt}`"),
                            safety: FixSafety::Safe,
                            kind: FixKind::Lint,
                            is_preferred: true,
                            is_organize_imports: false,
                            edits: vec![TextEdit::new(span, callee_txt.to_owned())],
                            delta: None,
                        };
                        ctx.report(
                            &registry::REDUNDANT_CLOSURE,
                            span,
                            format!("redundant closure can be simplified to `{callee_txt}`"),
                        )
                        .with_fix(fix);
                    }
                }
            }
            walk_expr(
                ctx,
                typed,
                file_id,
                ast,
                src,
                *body,
                in_loop,
                in_fallible_fn,
            );
        }
        Expr::Call { callee, args } => {
            // `panic_in_fallible_fn`
            if in_fallible_fn
                && ctx.may_fire(&registry::PANIC_IN_FALLIBLE_FN)
                && let Expr::Path(p) = &ast.expr(*callee).value
                && let Some(def_id) = typed.hir.resolve(p.span).and_then(|r| r.definition())
                && typed.hir.intrinsic(def_id) == Some(Intrinsic::Panic)
            {
                ctx.report(
                    &registry::PANIC_IN_FALLIBLE_FN,
                    span,
                    "explicit `panic(...)` inside a fallible `!<T, E>` function",
                )
                .with_help("consider returning `Err(...)` instead");
            }
            // `needless_nominal_roundtrip`: `inner(T::(x))`
            if args.len() == 1
                && ctx.may_fire(&registry::NEEDLESS_NOMINAL_ROUNDTRIP)
                && let Expr::Path(p) = &ast.expr(*callee).value
                && let Some(def_id) = typed.hir.resolve(p.span).and_then(|r| r.definition())
                && typed.hir.intrinsic(def_id) == Some(Intrinsic::Inner)
                && let Some(arg0) = args.first()
                && let Expr::Wrap {
                    path: wrap_p,
                    args: wargs,
                } = &ast.expr(arg0.value).value
                && wargs.len() == 1
                && let Some(warg0) = wargs.first()
            {
                let has_inv = typed
                    .hir
                    .resolve(wrap_p.span)
                    .and_then(|r| r.definition())
                    .is_some_and(|tid| typed.has_type_invariants(tid));
                if !has_inv
                    && let Some(inner_txt) =
                        src.get(ast.expr(warg0.value).span.start..ast.expr(warg0.value).span.end)
                {
                    let fix = Fix {
                        id: format!("needless_nominal_roundtrip:{}:{}", file_id.0, span.start),
                        title: format!("Simplify to `{inner_txt}`"),
                        safety: FixSafety::Safe,
                        kind: FixKind::Lint,
                        is_preferred: true,
                        is_organize_imports: false,
                        edits: vec![TextEdit::new(span, inner_txt.to_owned())],
                        delta: None,
                    };
                    ctx.report(
                        &registry::NEEDLESS_NOMINAL_ROUNDTRIP,
                        span,
                        "unnecessary `inner(T::(x))` wrap/unwrap round-trip",
                    )
                    .with_fix(fix);
                }
            }
            walk_expr(
                ctx,
                typed,
                file_id,
                ast,
                src,
                *callee,
                in_loop,
                in_fallible_fn,
            );
            for a in args {
                walk_expr(
                    ctx,
                    typed,
                    file_id,
                    ast,
                    src,
                    a.value,
                    in_loop,
                    in_fallible_fn,
                );
            }
        }
        Expr::Wrap { path, args } => {
            // `needless_nominal_roundtrip`: `T::(inner(w))` where `typeof(w) == T`
            if args.len() == 1
                && ctx.may_fire(&registry::NEEDLESS_NOMINAL_ROUNDTRIP)
                && let Some(arg0) = args.first()
                && let Expr::Call {
                    callee,
                    args: cargs,
                } = &ast.expr(arg0.value).value
                && cargs.len() == 1
                && let Some(carg0) = cargs.first()
                && let Expr::Path(cp) = &ast.expr(*callee).value
                && let Some(def_id) = typed.hir.resolve(cp.span).and_then(|r| r.definition())
                && typed.hir.intrinsic(def_id) == Some(Intrinsic::Inner)
            {
                let w_span = ast.expr(carg0.value).span;
                if typed.types.get(&span) == typed.types.get(&w_span)
                    && let Some(w_txt) = src.get(w_span.start..w_span.end)
                {
                    let _ = path;
                    let fix = Fix {
                        id: format!("needless_nominal_roundtrip:{}:{}", file_id.0, span.start),
                        title: format!("Simplify to `{w_txt}`"),
                        safety: FixSafety::Safe,
                        kind: FixKind::Lint,
                        is_preferred: true,
                        is_organize_imports: false,
                        edits: vec![TextEdit::new(span, w_txt.to_owned())],
                        delta: None,
                    };
                    ctx.report(
                        &registry::NEEDLESS_NOMINAL_ROUNDTRIP,
                        span,
                        "unnecessary `T::(inner(w))` unwrap/rewrap round-trip",
                    )
                    .with_fix(fix);
                }
            }
            for a in args {
                walk_expr(
                    ctx,
                    typed,
                    file_id,
                    ast,
                    src,
                    a.value,
                    in_loop,
                    in_fallible_fn,
                );
            }
        }
        Expr::Index { base, index, safe } => {
            // `redundant_checked_access`: driven STRICTLY by DBM `proved_ops` (never heuristic!).
            if *safe
                && typed.proved_ops.contains(&span)
                && ctx.may_fire(&registry::REDUNDANT_CHECKED_ACCESS)
            {
                ctx.report(
                    &registry::REDUNDANT_CHECKED_ACCESS,
                    span,
                    "checked `?[...]` access is already statically proved in bounds by Ril's DBM prover",
                )
                .with_help("direct `[...]` indexing is statically safe here");
            }
            walk_expr(
                ctx,
                typed,
                file_id,
                ast,
                src,
                *base,
                in_loop,
                in_fallible_fn,
            );
            walk_expr(
                ctx,
                typed,
                file_id,
                ast,
                src,
                *index,
                in_loop,
                in_fallible_fn,
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
                typed,
                file_id,
                ast,
                src,
                *value,
                in_loop,
                in_fallible_fn,
            );
        }
        Expr::Pipeline { value, target, .. } => {
            walk_expr(
                ctx,
                typed,
                file_id,
                ast,
                src,
                *value,
                in_loop,
                in_fallible_fn,
            );
            walk_expr(
                ctx,
                typed,
                file_id,
                ast,
                src,
                *target,
                in_loop,
                in_fallible_fn,
            );
        }
        Expr::Array(items) | Expr::Tuple(items) => {
            for &e in items {
                walk_expr(ctx, typed, file_id, ast, src, e, in_loop, in_fallible_fn);
            }
        }
        Expr::Map(entries) => {
            for &(k, v) in entries {
                walk_expr(ctx, typed, file_id, ast, src, k, in_loop, in_fallible_fn);
                walk_expr(ctx, typed, file_id, ast, src, v, in_loop, in_fallible_fn);
            }
        }
        Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = f.value {
                    walk_expr(ctx, typed, file_id, ast, src, v, in_loop, in_fallible_fn);
                }
            }
        }
        Expr::Interpolated(parts) => {
            for p in parts {
                if let StringPart::Interpolation(e) = p {
                    walk_expr(ctx, typed, file_id, ast, src, *e, in_loop, in_fallible_fn);
                }
            }
        }
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn check_block_statements(
    ctx: &mut LintContext<'_>,
    typed: &TypedProgram,
    file_id: FileId,
    ast: &Ast,
    src: &str,
    statements: &[StmtId],
    in_loop: bool,
    in_fallible_fn: bool,
) {
    let mut diverged_at: Option<Span> = None;
    let last_idx = statements.len().saturating_sub(1);

    for (idx, &stmt_id) in statements.iter().enumerate() {
        let s_span = ast.stmt(stmt_id).span;
        if let Some(prev_never) = diverged_at {
            if ctx.may_fire(&registry::UNREACHABLE_CODE)
                && !matches!(ast.stmt(stmt_id).value.kind, StmtKind::Expr(e) if matches!(ast.expr(e).value, Expr::Hole))
            {
                ctx.report(
                    &registry::UNREACHABLE_CODE,
                    s_span,
                    "statement is unreachable after diverging expression",
                )
                .with_label(prev_never, "control flow diverges here");
            }
            // Only report the first unreachable statement in the sequence.
            break;
        }

        // `ignored_option_result`: non-tail expression statement of type `?T`.
        if idx < last_idx
            && let StmtKind::Expr(e_id) = ast.stmt(stmt_id).value.kind
            && let e_span = ast.expr(e_id).span
            && let Some(ty) = typed.types.get(&e_span)
            && ty.is_option(&typed.hir)
            && ctx.may_fire(&registry::IGNORED_OPTION_RESULT)
        {
            let insert = Span::new(file_id, e_span.start, e_span.start);
            let fix = Fix {
                id: format!("ignored_option_result:{}:{}", file_id.0, e_span.start),
                title: "Explicitly discard with `let _ = `".to_owned(),
                safety: FixSafety::Unsafe,
                kind: FixKind::Lint,
                is_preferred: false,
                is_organize_imports: false,
                edits: vec![TextEdit::new(insert, "let _ = ")],
                delta: None,
            };
            ctx.report(
                &registry::IGNORED_OPTION_RESULT,
                e_span,
                "optional `?T` value is discarded; bind with `let _ = ...` if intentional",
            )
            .with_fix(fix);
        }

        walk_stmt(
            ctx,
            typed,
            file_id,
            ast,
            src,
            stmt_id,
            in_loop,
            in_fallible_fn,
        );

        if let StmtKind::Expr(e_id) = ast.stmt(stmt_id).value.kind
            && typed.types.get(&ast.expr(e_id).span) == Some(&Ty::Never)
        {
            diverged_at = Some(s_span);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn check_match_idioms(
    ctx: &mut LintContext<'_>,
    typed: &TypedProgram,
    file_id: FileId,
    ast: &Ast,
    src: &str,
    match_span: Span,
    scrutinee: ExprId,
    arms: &[ril_syntax::syntax::MatchArm],
) {
    let scr_span = ast.expr(scrutinee).span;
    let scr_ty = typed.types.get(&scr_span);
    let scr_txt = src.get(scr_span.start..scr_span.end).unwrap_or("");

    // `match_on_bool`
    if scr_ty == Some(&Ty::Bool)
        && arms.len() == 2
        && arms.iter().all(|a| a.guard.is_none())
        && ctx.may_fire(&registry::MATCH_ON_BOOL)
        && let (Some(a0), Some(a1)) = (arms.first(), arms.get(1))
        && matches!(
            (&ast.pattern(a0.pattern).value, &ast.pattern(a1.pattern).value),
            (Pattern::Literal(l0), Pattern::Literal(l1))
                if l0.kind == LiteralKind::Bool && l1.kind == LiteralKind::Bool
        )
    {
        ctx.report(
            &registry::MATCH_ON_BOOL,
            match_span,
            "`match` on `bool` is clearer as `if / else`",
        );
    }

    // `single_arm_match` on `?T` (exempt `!<T, E>` and linear types!).
    if arms.len() == 2
        && arms.iter().all(|a| a.guard.is_none())
        && scr_ty.is_some_and(|t| t.is_option(&typed.hir) && !typed.is_must_consume(t))
        && let (Some(a0), Some(a1)) = (arms.first(), arms.get(1))
    {
        if is_ctor_name(ast, a0.pattern, "Some")
            && (is_ctor_name(ast, a1.pattern, "None")
                || matches!(ast.pattern(a1.pattern).value, Pattern::Wildcard))
            && is_unit_expr(ast, a1.body)
            && ctx.may_fire(&registry::SINGLE_ARM_MATCH)
        {
            ctx.report(
                &registry::SINGLE_ARM_MATCH,
                match_span,
                "single-action `match` on `?T` can be written with `if let Some(...) = ...`",
            );
        }

        // `manual_fallback`: `match opt { Some(v) -> v; None -> fb }` → `opt ?? fb`
        if is_ctor_name_with_single_binding(ast, a0.pattern, "Some", a0.body)
            && is_ctor_name(ast, a1.pattern, "None")
            && !contains_control_transfer(ast, a1.body)
            && ctx.may_fire(&registry::MANUAL_FALLBACK)
        {
            let fb_span = ast.expr(a1.body).span;
            if let Some(fb_txt) = src.get(fb_span.start..fb_span.end) {
                let fix = Fix {
                    id: format!("manual_fallback:{}:{}", file_id.0, match_span.start),
                    title: format!("Simplify to `{scr_txt} ?? {fb_txt}`"),
                    safety: FixSafety::Safe,
                    kind: FixKind::Lint,
                    is_preferred: true,
                    is_organize_imports: false,
                    edits: vec![TextEdit::new(match_span, format!("{scr_txt} ?? {fb_txt}"))],
                    delta: None,
                };
                ctx.report(
                    &registry::MANUAL_FALLBACK,
                    match_span,
                    "manual `Option` fallback `match` can use `??`",
                )
                .with_fix(fix);
            }
        }

        // `manual_safe_nav`: `match opt { Some(v) -> Some(v.f); None -> None }`
        if is_ctor_name(ast, a1.pattern, "None")
            && is_path_name(ast, a1.body, "None")
            && let Some(bound_name) = single_ctor_binding_name(ast, a0.pattern, "Some")
            && let Expr::Call { callee, args } = &ast.expr(a0.body).value
            && is_path_name(ast, *callee, "Some")
            && args.len() == 1
            && let Some(arg0) = args.first()
            && let Expr::Member {
                base,
                member,
                safe: false,
            } = &ast.expr(arg0.value).value
            && is_path_name(ast, *base, &bound_name)
            && let ril_syntax::syntax::Member::Name(field_name) = member
            && !typed
                .types
                .get(&ast.expr(arg0.value).span)
                .is_some_and(|t| t.is_option(&typed.hir))
            && ctx.may_fire(&registry::MANUAL_SAFE_NAV)
        {
            let repl = format!("{scr_txt}?.{}", field_name.value);
            let fix = Fix {
                id: format!("manual_safe_nav:{}:{}", file_id.0, match_span.start),
                title: format!("Simplify to `{repl}`"),
                safety: FixSafety::Safe,
                kind: FixKind::Lint,
                is_preferred: true,
                is_organize_imports: false,
                edits: vec![TextEdit::new(match_span, repl)],
                delta: None,
            };
            ctx.report(
                &registry::MANUAL_SAFE_NAV,
                match_span,
                "manual `Option` projection can use `?.` safe navigation",
            )
            .with_fix(fix);
        }
    }

    // `manual_question_mark`: `match e { Ok(v) -> v; Err(err) -> return Err(err) }`
    if arms.len() == 2
        && arms.iter().all(|a| a.guard.is_none())
        && scr_ty.is_some_and(|t| t.is_result(&typed.hir))
        && let (Some(a0), Some(a1)) = (arms.first(), arms.get(1))
        && is_ctor_name_with_single_binding(ast, a0.pattern, "Ok", a0.body)
        && let Some(err_name) = single_ctor_binding_name(ast, a1.pattern, "Err")
        && let Expr::Transfer {
            kind: Transfer::Return,
            value: Some(ret_val),
        } = ast.expr(a1.body).value
        && let Expr::Call { callee, args } = &ast.expr(ret_val).value
        && is_path_name(ast, *callee, "Err")
        && args.len() == 1
        && args
            .first()
            .is_some_and(|a| is_path_name(ast, a.value, &err_name))
        && ctx.may_fire(&registry::MANUAL_QUESTION_MARK)
    {
        ctx.report(
            &registry::MANUAL_QUESTION_MARK,
            match_span,
            "trivial `Result` propagation `match` can use `?`",
        )
        .with_help(format!("consider replacing with `{scr_txt}?`"));
    }

    // `identical_branches` across adjacent match arms (when neither binds new names).
    if arms.len() >= 2 && ctx.may_fire(&registry::IDENTICAL_BRANCHES) {
        let mut seen: Vec<(Span, &str)> = Vec::new();
        for arm in arms {
            if arm.guard.is_some() || pattern_has_bindings(ast, arm.pattern) {
                continue;
            }
            let b_span = ast.expr(arm.body).span;
            let b_txt = src.get(b_span.start..b_span.end).unwrap_or("").trim();
            if b_txt.is_empty() || b_txt == "()" {
                continue;
            }
            if let Some(&(prev_span, _)) = seen.iter().find(|&&(_, txt)| txt == b_txt) {
                ctx.report(
                    &registry::IDENTICAL_BRANCHES,
                    b_span,
                    "match arm body is identical to an earlier arm (consider merging with `|`)",
                )
                .with_label(prev_span, "identical arm here");
                break;
            }
            seen.push((b_span, b_txt));
        }
    }
}

fn is_simple_place(ast: &Ast, id: ExprId) -> bool {
    match &ast.expr(id).value {
        Expr::Path(_) => true,
        Expr::Member {
            base, safe: false, ..
        } => is_simple_place(ast, *base),
        _ => false,
    }
}

fn is_pure_syntactic(ast: &Ast, id: ExprId) -> bool {
    match &ast.expr(id).value {
        Expr::Path(_) | Expr::Literal(_) | Expr::Unit => true,
        Expr::Member {
            base, safe: false, ..
        } => is_pure_syntactic(ast, *base),
        _ => false,
    }
}

fn is_zero_int(ast: &Ast, id: ExprId) -> bool {
    matches!(&ast.expr(id).value, Expr::Literal(l) if l.kind == LiteralKind::Int && l.text == "0")
}

fn is_bool_lit(ast: &Ast, id: ExprId, expected: bool) -> bool {
    let want = if expected { "true" } else { "false" };
    matches!(&ast.expr(id).value, Expr::Literal(l) if l.kind == LiteralKind::Bool && l.text == want)
}

fn single_block_expr(ast: &Ast, id: ExprId) -> Option<ExprId> {
    match &ast.expr(id).value {
        Expr::Block {
            statements,
            helpers,
        } if helpers.is_empty() && statements.len() == 1 => {
            if let StmtKind::Expr(e) = ast.stmt(*statements.first()?).value.kind {
                Some(e)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn extract_accessor_chain(ast: &Ast, expr_id: ExprId, param_name: &str) -> Option<String> {
    let mut parts = Vec::new();
    let mut cur = expr_id;
    loop {
        match &ast.expr(cur).value {
            Expr::Member { base, member, safe } => {
                let op = if *safe { "?." } else { "." };
                let seg = match member {
                    ril_syntax::syntax::Member::Name(n) | ril_syntax::syntax::Member::Index(n) => {
                        format!("{op}{}", n.value)
                    }
                    ril_syntax::syntax::Member::Computed(_) => return None,
                };
                parts.push(seg);
                cur = *base;
            }
            Expr::Path(p)
                if p.segments.len() == 1
                    && p.segments
                        .first()
                        .is_some_and(|s| s.name.value == param_name) =>
            {
                if parts.is_empty() {
                    return None;
                }
                parts.reverse();
                return Some(parts.concat());
            }
            _ => return None,
        }
    }
}

fn fn_is_meta_or_has_proofs(typed: &TypedProgram, def_id: ril_hir::DefinitionId) -> bool {
    let def = typed.hir.definition(def_id);
    let Some(stmt_id) = def.stmt else {
        return false;
    };
    let ast = &typed.hir.file(def.name.span.file).ast;
    match &ast.stmt(stmt_id).value.kind {
        StmtKind::Function(fun) => {
            fun.is_meta
                || fun
                    .signature
                    .params
                    .iter()
                    .any(|p| !p.guards.is_empty() || p.default.is_some())
        }
        _ => true,
    }
}

fn is_ctor_name(ast: &Ast, pat_id: ril_syntax::syntax::PatternId, name: &str) -> bool {
    matches!(
        &ast.pattern(pat_id).value,
        Pattern::Constructor(p, _) if p.segments.last().is_some_and(|s| s.name.value == name)
    )
}

fn single_ctor_binding_name(
    ast: &Ast,
    pat_id: ril_syntax::syntax::PatternId,
    ctor_name: &str,
) -> Option<String> {
    let Pattern::Constructor(p, Some(args)) = &ast.pattern(pat_id).value else {
        return None;
    };
    if !p.segments.last().is_some_and(|s| s.name.value == ctor_name) || args.len() != 1 {
        return None;
    }
    if let Pattern::Binding(_, n) = &ast.pattern(*args.first()?).value {
        Some(n.value.clone())
    } else {
        None
    }
}

fn is_ctor_name_with_single_binding(
    ast: &Ast,
    pat_id: ril_syntax::syntax::PatternId,
    ctor_name: &str,
    body_id: ExprId,
) -> bool {
    let Some(bound) = single_ctor_binding_name(ast, pat_id, ctor_name) else {
        return false;
    };
    is_path_name(ast, body_id, &bound)
}

fn is_path_name(ast: &Ast, expr_id: ExprId, name: &str) -> bool {
    matches!(
        &ast.expr(expr_id).value,
        Expr::Path(p) if p.segments.len() == 1 && p.segments.first().is_some_and(|s| s.name.value == name)
    )
}

fn is_unit_expr(ast: &Ast, id: ExprId) -> bool {
    match &ast.expr(id).value {
        Expr::Unit => true,
        Expr::Block {
            statements,
            helpers,
        } => statements.is_empty() && helpers.is_empty(),
        _ => false,
    }
}

fn contains_control_transfer(ast: &Ast, id: ExprId) -> bool {
    match &ast.expr(id).value {
        Expr::Transfer { .. } => true,
        Expr::Block { statements, .. } => {
            statements.iter().any(|&s| match ast.stmt(s).value.kind {
                StmtKind::Expr(e) => contains_control_transfer(ast, e),
                StmtKind::Binding { value: Some(e), .. } => contains_control_transfer(ast, e),
                _ => false,
            })
        }
        Expr::If { yes, no, .. } => {
            contains_control_transfer(ast, *yes)
                || no.is_some_and(|n| contains_control_transfer(ast, n))
        }
        _ => false,
    }
}

fn pattern_has_bindings(ast: &Ast, pat_id: ril_syntax::syntax::PatternId) -> bool {
    match &ast.pattern(pat_id).value {
        Pattern::Binding(_, _) | Pattern::TypeBinding(_) => true,
        Pattern::Rest(Some(_)) => true,
        Pattern::Or(ps) | Pattern::Tuple(ps) | Pattern::Wrap(_, ps) => {
            ps.iter().any(|&p| pattern_has_bindings(ast, p))
        }
        Pattern::Constructor(_, Some(ps)) => ps.iter().any(|&p| pattern_has_bindings(ast, p)),
        Pattern::Slice { elements, .. } => elements.iter().any(|&p| pattern_has_bindings(ast, p)),
        Pattern::Record { fields, .. } => !fields.is_empty(),
        _ => false,
    }
}

fn static_proof_uniquely_determines_subject(typed: &TypedProgram, tf_id: DefinitionId) -> bool {
    let def = typed.hir.definition(tf_id);
    let Some(stmt) = def.stmt else {
        return false;
    };
    let def_file = def.name.span.file;
    let Some(file) = typed.hir.files().find(|f| f.id == def_file) else {
        return false;
    };
    let StmtKind::Type(decl) = &file.ast.stmt(stmt).value.kind else {
        return false;
    };
    let TypeDefinition::Function(params, _) = &decl.definition else {
        return false;
    };
    let v = params
        .iter()
        .take_while(|p| {
            p.name
                .value
                .starts_with(|c: char| c.is_ascii_lowercase() || c == '_')
        })
        .count();
    if v == 0 {
        return false;
    }
    let (value_params, type_params) = params.split_at(v);
    let Some((subject, trailing)) = value_params.split_first() else {
        return false;
    };
    if subject.bound.is_empty() {
        return false;
    }
    if type_params.is_empty() {
        return true;
    }
    let type_param_ids: std::collections::HashSet<DefinitionId> = type_params
        .iter()
        .filter_map(|tp| {
            typed
                .hir
                .definitions()
                .find(|(_, d)| d.name.span == tp.name.span)
                .map(|(id, _)| id)
        })
        .collect();
    let mut bound_by_trailing: std::collections::HashSet<DefinitionId> =
        std::collections::HashSet::new();
    for tp in trailing {
        for &b in &tp.bound {
            let b_span = file.ast.ty(b).span;
            for (_, rid) in typed.hir.references_within(b_span) {
                if type_param_ids.contains(&rid) {
                    bound_by_trailing.insert(rid);
                }
            }
        }
    }
    for &b in &subject.bound {
        let b_span = file.ast.ty(b).span;
        for (_, rid) in typed.hir.references_within(b_span) {
            if type_param_ids.contains(&rid) && !bound_by_trailing.contains(&rid) {
                return false;
            }
        }
    }
    true
}

fn check_redundant_proof_base_types(
    ctx: &mut LintContext<'_>,
    typed: &TypedProgram,
    file_id: FileId,
    ast: &Ast,
    src: &str,
    fun: &Function,
    callable: Option<&Callable>,
) {
    if !ctx.may_fire(&registry::REDUNDANT_PROOF_BASE_TYPE) {
        return;
    }
    for param in &fun.signature.params {
        if param.is_meta {
            continue;
        }
        let Some(&first_guard) = param.guards.first() else {
            continue;
        };
        if let Some(ty_id) = param.ty
            && matches!(ast.ty(ty_id).value, Type::Proof(_))
        {
            continue;
        }
        let GuardKind::StaticProof(tf_id) = typed.hir.classify_guard(file_id, first_guard) else {
            continue;
        };
        if !static_proof_uniquely_determines_subject(typed, tf_id) {
            continue;
        }
        let guard_span = ast.expr(first_guard).span;
        let Some(guard_txt) = src.get(guard_span.start..guard_span.end) else {
            continue;
        };
        if let Some(ty_id) = param.ty {
            let ty_span = ast.ty(ty_id).span;
            let full_span = Span::new(file_id, ty_span.start, guard_span.end);
            let fix = Fix {
                id: format!(
                    "redundant_proof_base_type:{}:{}",
                    file_id.0, full_span.start
                ),
                title: format!("Simplify to `{guard_txt}`"),
                safety: FixSafety::Safe,
                kind: FixKind::Lint,
                is_preferred: true,
                is_organize_imports: false,
                edits: vec![TextEdit::new(full_span, guard_txt.to_owned())],
                delta: None,
            };
            ctx.report(
                &registry::REDUNDANT_PROOF_BASE_TYPE,
                full_span,
                format!(
                    "redundant base type before `|> {guard_txt}`; write `{guard_txt}` directly"
                ),
            )
            .with_fix(fix);
        } else if let Some(name) = &param.name {
            let replace_span = Span::new(file_id, name.span.end, guard_span.end);
            let full_span = Span::new(file_id, name.span.start, guard_span.end);
            let fix = Fix {
                id: format!(
                    "redundant_proof_base_type:{}:{}",
                    file_id.0, full_span.start
                ),
                title: format!("Rewrite as `{}: {guard_txt}`", name.value),
                safety: FixSafety::Safe,
                kind: FixKind::Lint,
                is_preferred: true,
                is_organize_imports: false,
                edits: vec![TextEdit::new(replace_span, format!(": {guard_txt}"))],
                delta: None,
            };
            ctx.report(
                &registry::REDUNDANT_PROOF_BASE_TYPE,
                full_span,
                format!(
                    "prefer `{}: {guard_txt}` over `{} |> {guard_txt}`",
                    name.value, name.value
                ),
            )
            .with_fix(fix);
        }
    }

    // Check return type (skip `?T |> Proof` and `!<T, E> |> Proof` payload proofs).
    let Some(&first_ret_guard) = fun.signature.guards.first() else {
        return;
    };
    let ret_ty_node = ast.ty(fun.signature.result);
    if matches!(
        ret_ty_node.value,
        Type::Proof(_) | Type::Option(_) | Type::Result(_, _)
    ) {
        return;
    }
    if callable.is_some_and(|c| c.result.is_option(&typed.hir) || c.result.is_result(&typed.hir)) {
        return;
    }
    let GuardKind::StaticProof(tf_id) = typed.hir.classify_guard(file_id, first_ret_guard) else {
        return;
    };
    if !static_proof_uniquely_determines_subject(typed, tf_id) {
        return;
    }
    let guard_span = ast.expr(first_ret_guard).span;
    let Some(guard_txt) = src.get(guard_span.start..guard_span.end) else {
        return;
    };
    let full_span = Span::new(file_id, ret_ty_node.span.start, guard_span.end);
    let fix = Fix {
        id: format!(
            "redundant_proof_base_type:{}:{}",
            file_id.0, full_span.start
        ),
        title: format!("Simplify return type to `{guard_txt}`"),
        safety: FixSafety::Safe,
        kind: FixKind::Lint,
        is_preferred: true,
        is_organize_imports: false,
        edits: vec![TextEdit::new(full_span, guard_txt.to_owned())],
        delta: None,
    };
    ctx.report(
        &registry::REDUNDANT_PROOF_BASE_TYPE,
        full_span,
        format!("redundant return base type before `|> {guard_txt}`; write `{guard_txt}` directly"),
    )
    .with_fix(fix);
}
