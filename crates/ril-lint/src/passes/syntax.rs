//! Syntax/CST/AST lint pass: runs even when later HIR/type stages fail.

use ril_source::{
    fix::{Fix, FixKind, FixSafety, TextEdit},
    span::{FileId, Span},
};
use ril_syntax::{
    directive::is_lint_directive_comment,
    lexer::Kind,
    syntax::{
        Ast, Condition, Expr, ExprId, GenericArg, Import, ImportTarget, Pattern, StmtId, StmtKind,
        Type, TypeId, Visibility,
    },
};

use crate::{LintContext, registry};

pub fn run(ctx: &mut LintContext<'_>) {
    let file_ids: Vec<FileId> = ctx.target_files.iter().copied().collect();
    for file_id in file_ids {
        let Some(data) = ctx.syntax_files.get(&file_id) else {
            continue;
        };
        let ast = data.ast.clone();
        let tokens = data.lexed.tokens.clone();
        let src = ctx.source_text(file_id).to_owned();

        check_import_order(ctx, file_id, &ast, &src);
        for &item in &ast.items {
            walk_stmt(ctx, file_id, &ast, &tokens, &src, item, true, 0);
        }
    }
}

fn check_import_order(ctx: &mut LintContext<'_>, file_id: FileId, ast: &Ast, src: &str) {
    if !ctx.may_fire(&registry::IMPORT_ORDER) {
        return;
    }
    // Check contiguous runs of top-level `use` statements of identical visibility that have no
    // intervening blank lines or section comments.
    let mut run: Vec<(StmtId, Span, Import, Visibility)> = Vec::new();
    let flush_run = |ctx: &mut LintContext<'_>,
                     run: &mut Vec<(StmtId, Span, Import, Visibility)>| {
        if run.len() < 2 {
            run.clear();
            return;
        }
        let keys: Vec<(u8, String)> = run
            .iter()
            .map(|(_, _, imp, _)| import_sort_key(imp))
            .collect();
        let mut sorted_indices: Vec<usize> = (0..run.len()).collect();
        sorted_indices.sort_by(|&a, &b| keys.get(a).cmp(&keys.get(b)));
        if sorted_indices.iter().enumerate().any(|(i, &idx)| i != idx)
            && let (Some(first), Some(last)) = (run.first(), run.last())
        {
            let full_span = first.1.join(last.1);
            let mut reordered = String::new();
            for (pos, &idx) in sorted_indices.iter().enumerate() {
                if pos > 0 {
                    reordered.push('\n');
                }
                if let Some((_, sp, _, _)) = run.get(idx)
                    && let Some(line) = src.get(sp.start..sp.end)
                {
                    reordered.push_str(line);
                }
            }
            let fix = Fix {
                id: format!("import_order:{}:{}", file_id.0, full_span.start),
                title: "Sort `use` imports canonically".to_owned(),
                safety: FixSafety::Safe,
                kind: FixKind::Lint,
                is_preferred: true,
                is_organize_imports: true,
                edits: vec![TextEdit::new(full_span, reordered)],
                delta: None,
            };
            ctx.report(
                &registry::IMPORT_ORDER,
                full_span,
                "top-level `use` imports are not canonically ordered (`ril/` → deps → `pkg/`)",
            )
            .with_fix(fix);
        }
        run.clear();
    };

    for &stmt_id in &ast.items {
        let spanned = ast.stmt(stmt_id);
        if let StmtKind::Import(imp) = &spanned.value.kind
            && spanned.value.attrs.is_empty()
        {
            let can_continue = run.last().is_some_and(|(_, prev_span, _, prev_vis)| {
                *prev_vis == spanned.value.visibility
                    && !has_blank_or_comment(src, prev_span.end, spanned.span.start)
            });
            if !can_continue {
                flush_run(ctx, &mut run);
            }
            run.push((stmt_id, spanned.span, imp.clone(), spanned.value.visibility));
        } else {
            flush_run(ctx, &mut run);
        }
    }
    flush_run(ctx, &mut run);
}

fn import_sort_key(imp: &Import) -> (u8, String) {
    let mut path = String::new();
    let group = if let Some(file) = &imp.file {
        for (i, seg) in file.iter().enumerate() {
            if i > 0 {
                path.push('/');
            }
            path.push_str(&seg.value);
        }
        match file.first().map(|s| s.value.as_str()) {
            Some("ril") => 0,
            Some("pkg") => 2,
            _ => 1,
        }
    } else {
        3
    };
    for m in &imp.modules {
        if !path.is_empty() {
            path.push_str("::");
        }
        path.push_str(&m.value);
    }
    (group, path)
}

fn has_blank_or_comment(src: &str, start: usize, end: usize) -> bool {
    let Some(between) = src.get(start..end) else {
        return true;
    };
    if between.contains("--") {
        return true;
    }
    between.bytes().filter(|&b| b == b'\n').count() >= 2
}

#[allow(clippy::too_many_arguments)]
fn walk_stmt(
    ctx: &mut LintContext<'_>,
    file_id: FileId,
    ast: &Ast,
    tokens: &[ril_syntax::lexer::Token],
    src: &str,
    stmt_id: StmtId,
    is_module_level: bool,
    nesting: usize,
) {
    let spanned = ast.stmt(stmt_id);
    let span = spanned.span;
    let stmt = &spanned.value;

    // `missing_doc_comment` on pub declarations (ignoring `-- ril:` and `meta(...)`).
    if stmt.visibility == Visibility::Public
        && matches!(
            stmt.kind,
            StmtKind::Function(_)
                | StmtKind::Type(_)
                | StmtKind::Effect { .. }
                | StmtKind::Sub { .. }
        )
        && ctx.may_fire(&registry::MISSING_DOC_COMMENT)
        && !has_doc_comment_above(src, span.start)
    {
        ctx.report(
            &registry::MISSING_DOC_COMMENT,
            span,
            "public declaration is missing a leading `--` documentation comment",
        );
    }

    match &stmt.kind {
        StmtKind::Function(fun) => {
            if fun.body.is_some()
                && fun.signature.params.len() > ctx.config.options.max_args
                && ctx.may_fire(&registry::TOO_MANY_ARGUMENTS)
            {
                ctx.report(
                    &registry::TOO_MANY_ARGUMENTS,
                    fun.name.span,
                    format!(
                        "function `{}` has {} parameters (max configured: {})",
                        fun.name.value,
                        fun.signature.params.len(),
                        ctx.config.options.max_args
                    ),
                )
                .with_help("consider grouping related parameters into a record parameter");
            }
            for p in &fun.signature.params {
                if let Some(ty) = p.ty {
                    walk_type(ctx, file_id, ast, src, ty);
                }
                if let Some(def) = p.default {
                    walk_expr(ctx, file_id, ast, tokens, src, def, nesting);
                }
            }
            walk_type(ctx, file_id, ast, src, fun.signature.result);
            for &h in &fun.helpers {
                walk_stmt(ctx, file_id, ast, tokens, src, h, false, nesting);
            }
            if let Some(body_id) = fun.body {
                let body_span = ast.expr(body_id).span;
                let lines = src
                    .get(body_span.start..body_span.end)
                    .map_or(0, |s| s.lines().count());
                if lines > ctx.config.options.max_lines && ctx.may_fire(&registry::LARGE_FUNCTION) {
                    ctx.report(
                        &registry::LARGE_FUNCTION,
                        fun.name.span,
                        format!(
                            "function `{}` spans {lines} lines (max configured: {})",
                            fun.name.value, ctx.config.options.max_lines
                        ),
                    )
                    .with_help("consider extracting `where` helper functions");
                }
                walk_expr(ctx, file_id, ast, tokens, src, body_id, 0);
            }
        }
        StmtKind::Type(decl) => match &decl.definition {
            ril_syntax::syntax::TypeDefinition::Data(t) => walk_type(ctx, file_id, ast, src, *t),
            ril_syntax::syntax::TypeDefinition::Function(_, e) => {
                walk_expr(ctx, file_id, ast, tokens, src, *e, 0);
            }
            ril_syntax::syntax::TypeDefinition::Sum(variants) => {
                for v in variants {
                    if let ril_syntax::syntax::Variant::Constructor {
                        payload: Some(tys), ..
                    } = v
                    {
                        for &t in tys {
                            walk_type(ctx, file_id, ast, src, t);
                        }
                    }
                }
            }
            ril_syntax::syntax::TypeDefinition::Opaque => {}
        },
        StmtKind::Effect { operations, .. } => {
            for &op in operations {
                walk_stmt(ctx, file_id, ast, tokens, src, op, false, 0);
            }
        }
        StmtKind::Sub { items, .. } => {
            for &item in items {
                walk_stmt(ctx, file_id, ast, tokens, src, item, true, 0);
            }
        }
        StmtKind::Import(imp) => {
            if is_module_level
                && matches!(imp.target, ImportTarget::Glob)
                && ctx.may_fire(&registry::GLOB_IMPORT)
            {
                ctx.report(
                    &registry::GLOB_IMPORT,
                    span,
                    "module-level wildcard `use ...::*` risks name collisions",
                )
                .with_help("prefer explicit `use M::(a, b)` imports");
            }
        }
        StmtKind::Binding {
            pattern,
            ty,
            value,
            fallback,
            ..
        } => {
            walk_pattern(ctx, file_id, ast, src, *pattern);
            if let Some(t) = ty {
                walk_type(ctx, file_id, ast, src, *t);
            }
            if let Some(v) = value {
                walk_expr(ctx, file_id, ast, tokens, src, *v, nesting);
            }
            if let Some(fb) = fallback {
                walk_expr(ctx, file_id, ast, tokens, src, *fb, nesting + 1);
            }
        }
        StmtKind::Defer(e) => {
            let expr = &ast.expr(*e).value;
            let is_empty = match expr {
                Expr::Unit => true,
                Expr::Block {
                    statements,
                    helpers,
                } => statements.is_empty() && helpers.is_empty(),
                _ => false,
            };
            if is_empty && ctx.may_fire(&registry::SUSPICIOUS_EMPTY_DEFER) {
                let fix = Fix {
                    id: format!("suspicious_empty_defer:{}:{}", file_id.0, span.start),
                    title: "Remove empty `defer` statement".to_owned(),
                    safety: FixSafety::Unsafe,
                    kind: FixKind::Lint,
                    is_preferred: false,
                    is_organize_imports: false,
                    edits: vec![TextEdit::new(span, "")],
                    delta: None,
                };
                ctx.report(
                    &registry::SUSPICIOUS_EMPTY_DEFER,
                    span,
                    "empty `defer` statement performs no cleanup",
                )
                .with_fix(fix);
            }
            walk_expr(ctx, file_id, ast, tokens, src, *e, nesting);
        }
        StmtKind::With(h) => {
            walk_expr(ctx, file_id, ast, tokens, src, h.value, nesting);
        }
        StmtKind::Expr(e) => {
            walk_expr(ctx, file_id, ast, tokens, src, *e, nesting);
        }
        StmtKind::Error => {}
    }
}

fn walk_type(ctx: &mut LintContext<'_>, file_id: FileId, ast: &Ast, src: &str, ty_id: TypeId) {
    let spanned = ast.ty(ty_id);
    let span = spanned.span;
    match &spanned.value {
        Type::Named(path) => {
            if path.segments.len() == 1
                && let Some(seg) = path.segments.first()
                && ctx.may_fire(&registry::NON_CANONICAL_FALLIBLE_TYPE)
            {
                if seg.name.value == "Option"
                    && seg.arguments.len() == 1
                    && let Some(GenericArg::Type(inner)) = seg.arguments.first()
                {
                    let inner_txt = src
                        .get(ast.ty(*inner).span.start..ast.ty(*inner).span.end)
                        .unwrap_or("");
                    if !inner_txt.is_empty() {
                        let fix = Fix {
                            id: format!("non_canonical_fallible_type:{}:{}", file_id.0, span.start),
                            title: format!("Replace with `?{inner_txt}`"),
                            safety: FixSafety::Safe,
                            kind: FixKind::Lint,
                            is_preferred: true,
                            is_organize_imports: false,
                            edits: vec![TextEdit::new(span, format!("?{inner_txt}"))],
                            delta: None,
                        };
                        ctx.report(
                            &registry::NON_CANONICAL_FALLIBLE_TYPE,
                            span,
                            "prefer idiomatic `?T` shorthand over `Option<T>`",
                        )
                        .with_fix(fix);
                    }
                } else if seg.name.value == "Result"
                    && seg.arguments.len() == 2
                    && let (Some(GenericArg::Type(ok)), Some(GenericArg::Type(err))) =
                        (seg.arguments.first(), seg.arguments.get(1))
                {
                    let ok_txt = src
                        .get(ast.ty(*ok).span.start..ast.ty(*ok).span.end)
                        .unwrap_or("");
                    let err_txt = src
                        .get(ast.ty(*err).span.start..ast.ty(*err).span.end)
                        .unwrap_or("");
                    if !ok_txt.is_empty() && !err_txt.is_empty() {
                        let fix = Fix {
                            id: format!("non_canonical_fallible_type:{}:{}", file_id.0, span.start),
                            title: format!("Replace with `!<{ok_txt}, {err_txt}>`"),
                            safety: FixSafety::Safe,
                            kind: FixKind::Lint,
                            is_preferred: true,
                            is_organize_imports: false,
                            edits: vec![TextEdit::new(span, format!("!<{ok_txt}, {err_txt}>"))],
                            delta: None,
                        };
                        ctx.report(
                            &registry::NON_CANONICAL_FALLIBLE_TYPE,
                            span,
                            "prefer idiomatic `!<T, E>` shorthand over `Result<T, E>`",
                        )
                        .with_fix(fix);
                    }
                }
            }
            for seg in &path.segments {
                for arg in &seg.arguments {
                    if let GenericArg::Type(t) = arg {
                        walk_type(ctx, file_id, ast, src, *t);
                    }
                }
            }
        }
        Type::Tuple(elems) => {
            for (_, t) in elems {
                walk_type(ctx, file_id, ast, src, *t);
            }
        }
        Type::Array(_, t) | Type::Option(t) => walk_type(ctx, file_id, ast, src, *t),
        Type::Map(k, _, v) | Type::Result(k, v) => {
            walk_type(ctx, file_id, ast, src, *k);
            walk_type(ctx, file_id, ast, src, *v);
        }
        Type::Record { fields, .. } => {
            for f in fields {
                walk_type(ctx, file_id, ast, src, f.ty);
            }
        }
        Type::Mapped { field, .. } => walk_type(ctx, file_id, ast, src, *field),
        Type::Callable(sig) => {
            for p in &sig.params {
                if let Some(t) = p.ty {
                    walk_type(ctx, file_id, ast, src, t);
                }
            }
            walk_type(ctx, file_id, ast, src, sig.result);
        }
        Type::Project { base, .. } => walk_type(ctx, file_id, ast, src, *base),
        _ => {}
    }
}

fn walk_pattern(
    ctx: &mut LintContext<'_>,
    file_id: FileId,
    ast: &Ast,
    _src: &str,
    pat_id: ril_syntax::syntax::PatternId,
) {
    match &ast.pattern(pat_id).value {
        Pattern::Record { fields, .. } => {
            for f in fields {
                if let Some(inner_pat) = f.pattern
                    && let Pattern::Binding(st, inner_name) = &ast.pattern(inner_pat).value
                    && !st.variable
                    && st.mode == ril_syntax::syntax::Mode::Plain
                    && inner_name.value == f.name.value
                    && ctx.may_fire(&registry::PREFER_SHORTHAND_RECORD)
                {
                    let field_span = f.name.span.join(inner_name.span);
                    let fix = Fix {
                        id: format!("prefer_shorthand_record:{}:{}", file_id.0, field_span.start),
                        title: format!("Use shorthand record pattern `{}`", f.name.value),
                        safety: FixSafety::Safe,
                        kind: FixKind::Lint,
                        is_preferred: true,
                        is_organize_imports: false,
                        edits: vec![TextEdit::new(field_span, f.name.value.clone())],
                        delta: None,
                    };
                    ctx.report(
                        &registry::PREFER_SHORTHAND_RECORD,
                        field_span,
                        format!(
                            "record pattern `{0}: {0}` can be shortened to `{0}`",
                            f.name.value
                        ),
                    )
                    .with_fix(fix);
                }
                if let Some(p) = f.pattern {
                    walk_pattern(ctx, file_id, ast, _src, p);
                }
            }
        }
        Pattern::Or(ps) | Pattern::Tuple(ps) | Pattern::Wrap(_, ps) => {
            for &p in ps {
                walk_pattern(ctx, file_id, ast, _src, p);
            }
        }
        Pattern::Slice { elements, .. } => {
            for &p in elements {
                walk_pattern(ctx, file_id, ast, _src, p);
            }
        }
        Pattern::Constructor(_, Some(ps)) => {
            for &p in ps {
                walk_pattern(ctx, file_id, ast, _src, p);
            }
        }
        Pattern::Subset {
            binding: Some(p), ..
        } => walk_pattern(ctx, file_id, ast, _src, *p),
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn walk_expr(
    ctx: &mut LintContext<'_>,
    file_id: FileId,
    ast: &Ast,
    tokens: &[ril_syntax::lexer::Token],
    src: &str,
    expr_id: ExprId,
    nesting: usize,
) {
    let spanned = ast.expr(expr_id);
    let span = spanned.span;

    match &spanned.value {
        Expr::Block {
            statements,
            helpers,
        } => {
            for &s in statements {
                walk_stmt(ctx, file_id, ast, tokens, src, s, false, nesting);
            }
            for &h in helpers {
                walk_stmt(ctx, file_id, ast, tokens, src, h, false, nesting);
            }
        }
        Expr::With {
            handlers,
            statements,
            helpers,
        } => {
            for h in handlers {
                walk_expr(ctx, file_id, ast, tokens, src, h.value, nesting);
            }
            for &s in statements {
                walk_stmt(ctx, file_id, ast, tokens, src, s, false, nesting + 1);
            }
            for &h in helpers {
                walk_stmt(ctx, file_id, ast, tokens, src, h, false, nesting);
            }
        }
        Expr::If {
            condition, yes, no, ..
        } => {
            let next_nesting = nesting + 1;
            if next_nesting > ctx.config.options.max_nesting
                && ctx.may_fire(&registry::DEEP_NESTING)
            {
                ctx.report(
                    &registry::DEEP_NESTING,
                    span,
                    format!(
                        "control-flow nesting depth {next_nesting} exceeds max {}",
                        ctx.config.options.max_nesting
                    ),
                );
            }
            if let Condition::Expr(c) = condition {
                check_redundant_parens_on(ctx, file_id, ast, src, *c, "if condition");
                walk_expr(ctx, file_id, ast, tokens, src, *c, nesting);
            } else if let Condition::Binding { value, .. } = condition {
                walk_expr(ctx, file_id, ast, tokens, src, *value, nesting);
            }
            walk_expr(ctx, file_id, ast, tokens, src, *yes, next_nesting);
            if let Some(n) = no {
                let n_nest = if matches!(ast.expr(*n).value, Expr::If { .. }) {
                    nesting
                } else {
                    next_nesting
                };
                walk_expr(ctx, file_id, ast, tokens, src, *n, n_nest);
            }
        }
        Expr::While { condition, body } => {
            let next_nesting = nesting + 1;
            if next_nesting > ctx.config.options.max_nesting
                && ctx.may_fire(&registry::DEEP_NESTING)
            {
                ctx.report(
                    &registry::DEEP_NESTING,
                    span,
                    format!(
                        "control-flow nesting depth {next_nesting} exceeds max {}",
                        ctx.config.options.max_nesting
                    ),
                );
            }
            if let Condition::Expr(c) = condition {
                check_redundant_parens_on(ctx, file_id, ast, src, *c, "while condition");
                walk_expr(ctx, file_id, ast, tokens, src, *c, nesting);
            } else if let Condition::Binding { value, .. } = condition {
                walk_expr(ctx, file_id, ast, tokens, src, *value, nesting);
            }
            walk_expr(ctx, file_id, ast, tokens, src, *body, next_nesting);
        }
        Expr::For { iterable, body, .. } => {
            let next_nesting = nesting + 1;
            if next_nesting > ctx.config.options.max_nesting
                && ctx.may_fire(&registry::DEEP_NESTING)
            {
                ctx.report(
                    &registry::DEEP_NESTING,
                    span,
                    format!(
                        "control-flow nesting depth {next_nesting} exceeds max {}",
                        ctx.config.options.max_nesting
                    ),
                );
            }
            walk_expr(ctx, file_id, ast, tokens, src, *iterable, nesting);
            walk_expr(ctx, file_id, ast, tokens, src, *body, next_nesting);
        }
        Expr::Match { value, arms, .. } => {
            let next_nesting = nesting + 1;
            if next_nesting > ctx.config.options.max_nesting
                && ctx.may_fire(&registry::DEEP_NESTING)
            {
                ctx.report(
                    &registry::DEEP_NESTING,
                    span,
                    format!(
                        "control-flow nesting depth {next_nesting} exceeds max {}",
                        ctx.config.options.max_nesting
                    ),
                );
            }
            check_redundant_parens_on(ctx, file_id, ast, src, *value, "match scrutinee");
            walk_expr(ctx, file_id, ast, tokens, src, *value, nesting);
            for arm in arms {
                walk_pattern(ctx, file_id, ast, src, arm.pattern);
                if let Some(g) = arm.guard {
                    walk_expr(ctx, file_id, ast, tokens, src, g, next_nesting);
                }
                walk_expr(ctx, file_id, ast, tokens, src, arm.body, next_nesting);
            }
        }
        Expr::Transfer { value: Some(v), .. } => {
            check_redundant_parens_on(ctx, file_id, ast, src, *v, "return expression");
            walk_expr(ctx, file_id, ast, tokens, src, *v, nesting);
        }
        Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(val_id) = f.value {
                    if let Expr::Path(path) = &ast.expr(val_id).value
                        && path.segments.len() == 1
                        && let Some(seg) = path.segments.first()
                        && seg.arguments.is_empty()
                        && seg.name.value == f.name.value
                        && ctx.may_fire(&registry::PREFER_SHORTHAND_RECORD)
                    {
                        let field_span = f.name.span.join(ast.expr(val_id).span);
                        let fix = Fix {
                            id: format!(
                                "prefer_shorthand_record:{}:{}",
                                file_id.0, field_span.start
                            ),
                            title: format!("Use shorthand field `{}`", f.name.value),
                            safety: FixSafety::Safe,
                            kind: FixKind::Lint,
                            is_preferred: true,
                            is_organize_imports: false,
                            edits: vec![TextEdit::new(field_span, f.name.value.clone())],
                            delta: None,
                        };
                        ctx.report(
                            &registry::PREFER_SHORTHAND_RECORD,
                            field_span,
                            format!(
                                "record field `{0}: {0}` can be shortened to `{0}`",
                                f.name.value
                            ),
                        )
                        .with_fix(fix);
                    }
                    walk_expr(ctx, file_id, ast, tokens, src, val_id, nesting);
                }
            }
        }
        Expr::Call { callee, args } => {
            // `redundant_trailing_parens`: `f() \x -> ...` → `f \x -> ...`
            if args.len() == 1
                && let Some(only) = args.first()
                && only.name.is_none()
                && matches!(
                    ast.expr(only.value).value,
                    Expr::Closure { .. } | Expr::Accessor(_)
                )
                && ctx.may_fire(&registry::REDUNDANT_TRAILING_PARENS)
            {
                let callee_end = ast.expr(*callee).span.end;
                let closure_start = ast.expr(only.value).span.start;
                if let Some(between) = src.get(callee_end..closure_start)
                    && between.trim() == "()"
                {
                    let parens_span = Span::new(file_id, callee_end, callee_end + 2);
                    if src.get(parens_span.start..parens_span.end) == Some("()") {
                        let fix = Fix {
                            id: format!(
                                "redundant_trailing_parens:{}:{}",
                                file_id.0, parens_span.start
                            ),
                            title: "Remove empty `()` before trailing closure".to_owned(),
                            safety: FixSafety::Safe,
                            kind: FixKind::Lint,
                            is_preferred: true,
                            is_organize_imports: false,
                            edits: vec![TextEdit::new(parens_span, "")],
                            delta: None,
                        };
                        ctx.report(
                            &registry::REDUNDANT_TRAILING_PARENS,
                            parens_span,
                            "empty `()` before trailing closure is unnecessary",
                        )
                        .with_fix(fix);
                    }
                }
            }
            walk_expr(ctx, file_id, ast, tokens, src, *callee, nesting);
            for arg in args {
                walk_expr(ctx, file_id, ast, tokens, src, arg.value, nesting);
            }
        }
        Expr::Closure { body, .. } => {
            // `unnecessary_closure_braces`: `\x -> { e }` → `\x -> e`
            // CRITICAL Ril grammar guard: NEVER fire when next token is `|>` or `?`!
            if ctx.may_fire(&registry::UNNECESSARY_CLOSURE_BRACES)
                && let Expr::Block {
                    statements,
                    helpers,
                } = &ast.expr(*body).value
                && helpers.is_empty()
                && statements.len() == 1
                && let Some(&only_stmt) = statements.first()
                && let StmtKind::Expr(inner_expr) = ast.stmt(only_stmt).value.kind
                && ast.stmt(only_stmt).value.attrs.is_empty()
            {
                let body_span = ast.expr(*body).span;
                let next_tok = next_non_newline_token_text(src, tokens, span.end);
                let followed_by_pipe_or_q = matches!(next_tok, Some("|>" | "?"));
                let body_src = src.get(body_span.start..body_span.end).unwrap_or("");
                if !followed_by_pipe_or_q
                    && !body_src.contains('\n')
                    && !body_src.contains("--")
                    && let Some(inner_src) =
                        src.get(ast.expr(inner_expr).span.start..ast.expr(inner_expr).span.end)
                {
                    let fix = Fix {
                        id: format!(
                            "unnecessary_closure_braces:{}:{}",
                            file_id.0, body_span.start
                        ),
                        title: "Remove unnecessary braces around closure body".to_owned(),
                        safety: FixSafety::Safe,
                        kind: FixKind::Lint,
                        is_preferred: true,
                        is_organize_imports: false,
                        edits: vec![TextEdit::new(body_span, inner_src.to_owned())],
                        delta: None,
                    };
                    ctx.report(
                        &registry::UNNECESSARY_CLOSURE_BRACES,
                        body_span,
                        "single-expression closure body does not need `{ ... }`",
                    )
                    .with_fix(fix);
                }
            }
            walk_expr(ctx, file_id, ast, tokens, src, *body, nesting);
        }
        Expr::Unary { value, .. } | Expr::Meta(value) | Expr::Cast { value, .. } => {
            walk_expr(ctx, file_id, ast, tokens, src, *value, nesting);
        }
        Expr::Binary { left, right, .. } => {
            walk_expr(ctx, file_id, ast, tokens, src, *left, nesting);
            walk_expr(ctx, file_id, ast, tokens, src, *right, nesting);
        }
        Expr::Pipeline { value, target, .. } => {
            walk_expr(ctx, file_id, ast, tokens, src, *value, nesting);
            walk_expr(ctx, file_id, ast, tokens, src, *target, nesting);
        }
        Expr::Member { base, .. } => {
            walk_expr(ctx, file_id, ast, tokens, src, *base, nesting);
        }
        Expr::Index { base, index, .. } => {
            walk_expr(ctx, file_id, ast, tokens, src, *base, nesting);
            walk_expr(ctx, file_id, ast, tokens, src, *index, nesting);
        }
        Expr::Range { start, end, .. } => {
            if let Some(s) = start {
                walk_expr(ctx, file_id, ast, tokens, src, *s, nesting);
            }
            if let Some(e) = end {
                walk_expr(ctx, file_id, ast, tokens, src, *e, nesting);
            }
        }
        Expr::Wrap { args, .. } => {
            for arg in args {
                walk_expr(ctx, file_id, ast, tokens, src, arg.value, nesting);
            }
        }
        Expr::Array(items) | Expr::Tuple(items) => {
            for &item in items {
                walk_expr(ctx, file_id, ast, tokens, src, item, nesting);
            }
        }
        Expr::Map(entries) => {
            for &(k, v) in entries {
                walk_expr(ctx, file_id, ast, tokens, src, k, nesting);
                walk_expr(ctx, file_id, ast, tokens, src, v, nesting);
            }
        }
        Expr::Interpolated(parts) => {
            for part in parts {
                if let ril_syntax::syntax::StringPart::Interpolation(e) = part {
                    walk_expr(ctx, file_id, ast, tokens, src, *e, nesting);
                }
            }
        }
        _ => {}
    }
}

fn check_redundant_parens_on(
    ctx: &mut LintContext<'_>,
    file_id: FileId,
    ast: &Ast,
    src: &str,
    expr_id: ExprId,
    where_label: &str,
) {
    if !ast.is_grouped(expr_id) || !ctx.may_fire(&registry::REDUNDANT_PARENS) {
        return;
    }
    let span = ast.expr(expr_id).span;
    let Some(raw) = src.get(span.start..span.end) else {
        return;
    };
    // Exclusion 4: never strip multi-line parens (needed for newline continuation).
    if raw.contains('\n') {
        return;
    }
    let Some(inner) = raw.strip_prefix('(').and_then(|s| s.strip_suffix(')')) else {
        return;
    };
    let trimmed = inner.trim();
    if trimmed.is_empty() {
        return;
    }
    let fix = Fix {
        id: format!("redundant_parens:{}:{}", file_id.0, span.start),
        title: "Remove unnecessary parentheses".to_owned(),
        safety: FixSafety::Safe,
        kind: FixKind::Lint,
        is_preferred: true,
        is_organize_imports: false,
        edits: vec![TextEdit::new(span, trimmed.to_owned())],
        delta: None,
    };
    ctx.report(
        &registry::REDUNDANT_PARENS,
        span,
        format!("unnecessary parentheses around {where_label}"),
    )
    .with_fix(fix);
}

fn next_non_newline_token_text<'a>(
    src: &'a str,
    tokens: &[ril_syntax::lexer::Token],
    after_byte: usize,
) -> Option<&'a str> {
    tokens
        .iter()
        .find(|t| t.span.start >= after_byte && !matches!(t.kind, Kind::Newline | Kind::Eof))
        .and_then(|t| src.get(t.span.start..t.span.end))
}

fn has_doc_comment_above(src: &str, decl_start: usize) -> bool {
    let prefix = src.get(..decl_start).unwrap_or("");
    let lines: Vec<&str> = prefix.lines().collect();
    // If decl_start is not at col 0, drop the partial line it sits on.
    let mut idx = if prefix.ends_with('\n') {
        lines.len()
    } else {
        lines.len().saturating_sub(1)
    };
    while idx > 0 {
        idx -= 1;
        let trimmed = lines.get(idx).map_or("", |l| l.trim());
        if trimmed.is_empty() {
            return false;
        }
        if is_lint_directive_comment(trimmed) || trimmed.starts_with("meta(") {
            continue;
        }
        return trimmed.starts_with("--");
    }
    false
}
