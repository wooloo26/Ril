use std::collections::{BTreeSet, HashMap, HashSet};

use ril_hir::{DefinitionId, Program, Resolution};
use ril_source::span::{FileId, Span};
use ril_syntax::syntax::{
    Ast, Condition, Expr, ExprId, Member, Pattern, PatternId, StmtId, StmtKind, StringPart,
};

/// Collects every mutable `var` binding captured by a closure or `&up(...)` clause
/// so MIR lowering allocates a shared cell for it.
pub(super) fn collect_boxed_var_captures(hir: &Program) -> BTreeSet<DefinitionId> {
    let mut boxed = BTreeSet::new();
    let mut all_var_defs = HashSet::new();

    for file in hir.files() {
        for stmt in file.ast.statements() {
            if let StmtKind::Binding {
                pattern, storage, ..
            } = &stmt.value.kind
            {
                collect_var_pattern_defs(
                    hir,
                    &file.ast,
                    *pattern,
                    storage.variable,
                    &mut all_var_defs,
                );
            }
        }
        for pat in file.ast.patterns() {
            match &pat.value {
                Pattern::Binding(storage, name) if storage.variable => {
                    if let Some(Resolution::Definition(id)) = hir.resolve(name.span) {
                        all_var_defs.insert(id);
                    }
                }
                Pattern::Record { fields, .. } => {
                    for field in fields {
                        if field.storage.variable {
                            if let Some(sub) = field.pattern {
                                collect_var_pattern_defs(
                                    hir,
                                    &file.ast,
                                    sub,
                                    true,
                                    &mut all_var_defs,
                                );
                            } else if let Some(Resolution::Definition(id)) =
                                hir.resolve(field.name.span)
                            {
                                all_var_defs.insert(id);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    let mut fn_up_captures: HashMap<DefinitionId, Vec<DefinitionId>> = HashMap::new();
    for (def_id, def) in hir.definitions() {
        let Some(stmt_id) = def.stmt else {
            continue;
        };
        if def.name.span.file == FileId::BUILTIN {
            continue;
        }
        let ast = &hir.file(def.name.span.file).ast;
        if let StmtKind::Function(fun) = &ast.stmt(stmt_id).value.kind {
            let mut ups = Vec::new();
            for (storage, path) in fun
                .signature
                .obligations
                .state
                .iter()
                .flat_map(|clause| &clause.bindings)
            {
                if let Some(Resolution::Definition(target)) = hir.resolve(path.span) {
                    ups.push(target);
                    if storage.variable {
                        boxed.insert(target);
                    }
                }
            }
            if !ups.is_empty() {
                fn_up_captures.insert(def_id, ups);
            }
        }
    }

    for file in hir.files() {
        for &stmt_id in &file.ast.items {
            walk_stmt(
                hir,
                &file.ast,
                stmt_id,
                &all_var_defs,
                &fn_up_captures,
                &mut boxed,
                None,
            );
        }
    }

    boxed
}

fn collect_var_pattern_defs(
    hir: &Program,
    ast: &Ast,
    pat: PatternId,
    inherited_var: bool,
    out: &mut HashSet<DefinitionId>,
) {
    match &ast.pattern(pat).value {
        Pattern::Binding(storage, name) => {
            if (inherited_var || storage.variable)
                && let Some(Resolution::Definition(id)) = hir.resolve(name.span)
            {
                out.insert(id);
            }
        }
        Pattern::Rest(Some(name)) => {
            if inherited_var && let Some(Resolution::Definition(id)) = hir.resolve(name.span) {
                out.insert(id);
            }
        }
        Pattern::Tuple(items)
        | Pattern::Or(items)
        | Pattern::Slice {
            elements: items, ..
        } => {
            for &item in items {
                collect_var_pattern_defs(hir, ast, item, inherited_var, out);
            }
        }
        Pattern::Constructor(_, Some(payload)) | Pattern::Wrap(_, payload) => {
            for &item in payload {
                collect_var_pattern_defs(hir, ast, item, inherited_var, out);
            }
        }
        Pattern::Record { fields, .. } => {
            for field in fields {
                let is_var = inherited_var || field.storage.variable;
                if let Some(sub) = field.pattern {
                    collect_var_pattern_defs(hir, ast, sub, is_var, out);
                } else if is_var
                    && let Some(Resolution::Definition(id)) = hir.resolve(field.name.span)
                {
                    out.insert(id);
                }
            }
        }
        Pattern::Subset { binding, .. } => {
            collect_var_pattern_defs(hir, ast, *binding, inherited_var, out);
        }
        Pattern::Wildcard
        | Pattern::Unit
        | Pattern::Literal(_)
        | Pattern::Range { .. }
        | Pattern::Rest(None)
        | Pattern::Constructor(_, None)
        | Pattern::Type(_)
        | Pattern::TypeBinding(_) => {}
    }
}

fn collect_pattern_defs(hir: &Program, ast: &Ast, pat: PatternId, out: &mut HashSet<DefinitionId>) {
    match &ast.pattern(pat).value {
        Pattern::Binding(_, name) | Pattern::TypeBinding(name) => {
            if let Some(Resolution::Definition(id)) = hir.resolve(name.span) {
                out.insert(id);
            }
        }
        Pattern::Rest(Some(name)) => {
            if let Some(Resolution::Definition(id)) = hir.resolve(name.span) {
                out.insert(id);
            }
        }
        Pattern::Tuple(items)
        | Pattern::Or(items)
        | Pattern::Slice {
            elements: items, ..
        } => {
            for &item in items {
                collect_pattern_defs(hir, ast, item, out);
            }
        }
        Pattern::Constructor(_, Some(payload)) | Pattern::Wrap(_, payload) => {
            for &item in payload {
                collect_pattern_defs(hir, ast, item, out);
            }
        }
        Pattern::Record { fields, .. } => {
            for field in fields {
                if let Some(sub) = field.pattern {
                    collect_pattern_defs(hir, ast, sub, out);
                } else if let Some(Resolution::Definition(id)) = hir.resolve(field.name.span) {
                    out.insert(id);
                }
            }
        }
        Pattern::Subset { binding, .. } => collect_pattern_defs(hir, ast, *binding, out),
        Pattern::Wildcard
        | Pattern::Unit
        | Pattern::Literal(_)
        | Pattern::Range { .. }
        | Pattern::Rest(None)
        | Pattern::Constructor(_, None)
        | Pattern::Type(_) => {}
    }
}

fn record_ref(
    target: DefinitionId,
    fn_up_captures: &HashMap<DefinitionId, Vec<DefinitionId>>,
    refs: &mut BTreeSet<DefinitionId>,
    visited: &mut HashSet<DefinitionId>,
) {
    if !visited.insert(target) {
        return;
    }
    refs.insert(target);
    if let Some(ups) = fn_up_captures.get(&target) {
        for &up in ups {
            record_ref(up, fn_up_captures, refs, visited);
        }
    }
}

fn walk_stmt(
    hir: &Program,
    ast: &Ast,
    stmt_id: StmtId,
    all_var_defs: &HashSet<DefinitionId>,
    fn_up_captures: &HashMap<DefinitionId, Vec<DefinitionId>>,
    boxed: &mut BTreeSet<DefinitionId>,
    mut refs: Option<&mut BTreeSet<DefinitionId>>,
) {
    match &ast.stmt(stmt_id).value.kind {
        StmtKind::Function(fun) => {
            for param in &fun.signature.params {
                if let Some(default) = param.default {
                    walk_expr(
                        hir,
                        ast,
                        default,
                        all_var_defs,
                        fn_up_captures,
                        boxed,
                        refs.as_deref_mut(),
                    );
                }
            }
            for &helper in &fun.helpers {
                walk_stmt(
                    hir,
                    ast,
                    helper,
                    all_var_defs,
                    fn_up_captures,
                    boxed,
                    refs.as_deref_mut(),
                );
            }
            if let Some(body) = fun.body {
                walk_expr(
                    hir,
                    ast,
                    body,
                    all_var_defs,
                    fn_up_captures,
                    boxed,
                    refs.as_deref_mut(),
                );
            }
        }
        StmtKind::Sub { items, .. } => {
            for &item in items {
                walk_stmt(
                    hir,
                    ast,
                    item,
                    all_var_defs,
                    fn_up_captures,
                    boxed,
                    refs.as_deref_mut(),
                );
            }
        }
        StmtKind::Binding {
            value, fallback, ..
        } => {
            if let Some(expr) = value {
                walk_expr(
                    hir,
                    ast,
                    *expr,
                    all_var_defs,
                    fn_up_captures,
                    boxed,
                    refs.as_deref_mut(),
                );
            }
            if let Some(expr) = fallback {
                walk_expr(
                    hir,
                    ast,
                    *expr,
                    all_var_defs,
                    fn_up_captures,
                    boxed,
                    refs.as_deref_mut(),
                );
            }
        }
        StmtKind::Defer(expr) => {
            let defer_span = ast.stmt(stmt_id).span;
            let mut inner_refs = BTreeSet::new();
            walk_expr(
                hir,
                ast,
                *expr,
                all_var_defs,
                fn_up_captures,
                boxed,
                Some(&mut inner_refs),
            );
            inner_refs.retain(|def| {
                let def_span = hir.definition(*def).name.span;
                !(def_span.file == defer_span.file
                    && def_span.start >= defer_span.start
                    && def_span.end <= defer_span.end)
            });
            for &captured in &inner_refs {
                if all_var_defs.contains(&captured) {
                    boxed.insert(captured);
                }
                if let Some(outer) = refs.as_deref_mut() {
                    outer.insert(captured);
                }
            }
        }
        StmtKind::With(handler) => {
            walk_expr(
                hir,
                ast,
                handler.value,
                all_var_defs,
                fn_up_captures,
                boxed,
                refs,
            );
        }
        StmtKind::Expr(expr) => {
            walk_expr(hir, ast, *expr, all_var_defs, fn_up_captures, boxed, refs);
        }
        StmtKind::Type(_) | StmtKind::Effect { .. } | StmtKind::Import(_) | StmtKind::Error => {}
    }
}

fn walk_condition(
    hir: &Program,
    ast: &Ast,
    condition: &Condition,
    all_var_defs: &HashSet<DefinitionId>,
    fn_up_captures: &HashMap<DefinitionId, Vec<DefinitionId>>,
    boxed: &mut BTreeSet<DefinitionId>,
    refs: Option<&mut BTreeSet<DefinitionId>>,
) {
    match condition {
        Condition::Expr(expr) | Condition::Binding { value: expr, .. } => {
            walk_expr(hir, ast, *expr, all_var_defs, fn_up_captures, boxed, refs);
        }
    }
}

fn walk_expr(
    hir: &Program,
    ast: &Ast,
    expr_id: ExprId,
    all_var_defs: &HashSet<DefinitionId>,
    fn_up_captures: &HashMap<DefinitionId, Vec<DefinitionId>>,
    boxed: &mut BTreeSet<DefinitionId>,
    mut refs: Option<&mut BTreeSet<DefinitionId>>,
) {
    let node = ast.expr(expr_id);
    let span: Span = node.span;
    match &node.value {
        Expr::Path(path) => {
            if let Some(refs) = refs.as_deref_mut()
                && let Some(Resolution::Definition(id)) = hir.resolve(path.span)
            {
                record_ref(id, fn_up_captures, refs, &mut HashSet::new());
            }
        }
        Expr::Closure { params, body, .. } => {
            let mut inner_refs = BTreeSet::new();
            let mut inner_params = HashSet::new();
            for param in params {
                if let Some(pattern) = param.pattern {
                    collect_pattern_defs(hir, ast, pattern, &mut inner_params);
                }
                if let Some(name) = &param.name
                    && let Some(Resolution::Definition(pid)) = hir.resolve(name.span)
                {
                    inner_params.insert(pid);
                }
            }
            walk_expr(
                hir,
                ast,
                *body,
                all_var_defs,
                fn_up_captures,
                boxed,
                Some(&mut inner_refs),
            );
            inner_refs.retain(|def| {
                if inner_params.contains(def) {
                    return false;
                }
                let def_span = hir.definition(*def).name.span;
                !(def_span.file == span.file
                    && def_span.start >= span.start
                    && def_span.end <= span.end)
            });
            for &captured in &inner_refs {
                if all_var_defs.contains(&captured) {
                    boxed.insert(captured);
                }
                if let Some(outer) = refs.as_deref_mut() {
                    outer.insert(captured);
                }
            }
        }
        Expr::Block {
            statements,
            helpers,
        } => {
            let mut ctl_tail_start = None;
            for (idx, &stmt) in statements.iter().enumerate() {
                if matches!(
                    &ast.stmt(stmt).value.kind,
                    StmtKind::With(h) if h.is_ctl
                ) {
                    ctl_tail_start = Some(idx);
                    break;
                }
            }
            if let Some(split) = ctl_tail_start {
                for &stmt in statements.iter().take(split + 1) {
                    walk_stmt(
                        hir,
                        ast,
                        stmt,
                        all_var_defs,
                        fn_up_captures,
                        boxed,
                        refs.as_deref_mut(),
                    );
                }
                let tail_start_offset = statements
                    .get(split)
                    .map_or(span.start, |&stmt| ast.stmt(stmt).span.end);
                let mut inner_refs = BTreeSet::new();
                for &stmt in statements.iter().skip(split + 1) {
                    walk_stmt(
                        hir,
                        ast,
                        stmt,
                        all_var_defs,
                        fn_up_captures,
                        boxed,
                        Some(&mut inner_refs),
                    );
                }
                for &helper in helpers {
                    walk_stmt(
                        hir,
                        ast,
                        helper,
                        all_var_defs,
                        fn_up_captures,
                        boxed,
                        Some(&mut inner_refs),
                    );
                }
                inner_refs.retain(|def| {
                    let def_span = hir.definition(*def).name.span;
                    !(def_span.file == span.file
                        && def_span.start >= tail_start_offset
                        && def_span.end <= span.end)
                });
                for &captured in &inner_refs {
                    if all_var_defs.contains(&captured) {
                        boxed.insert(captured);
                    }
                    if let Some(outer) = refs.as_deref_mut() {
                        outer.insert(captured);
                    }
                }
            } else {
                for &stmt in statements {
                    walk_stmt(
                        hir,
                        ast,
                        stmt,
                        all_var_defs,
                        fn_up_captures,
                        boxed,
                        refs.as_deref_mut(),
                    );
                }
                for &helper in helpers {
                    walk_stmt(
                        hir,
                        ast,
                        helper,
                        all_var_defs,
                        fn_up_captures,
                        boxed,
                        refs.as_deref_mut(),
                    );
                }
            }
        }
        Expr::With {
            handlers,
            statements,
            helpers,
        } => {
            let has_ctl = handlers.iter().any(|h| h.is_ctl);
            for handler in handlers {
                walk_expr(
                    hir,
                    ast,
                    handler.value,
                    all_var_defs,
                    fn_up_captures,
                    boxed,
                    refs.as_deref_mut(),
                );
            }
            if has_ctl {
                let body_start = statements
                    .first()
                    .map_or(span.start, |&s| ast.stmt(s).span.start);
                let mut inner_refs = BTreeSet::new();
                for &stmt in statements {
                    walk_stmt(
                        hir,
                        ast,
                        stmt,
                        all_var_defs,
                        fn_up_captures,
                        boxed,
                        Some(&mut inner_refs),
                    );
                }
                for &helper in helpers {
                    walk_stmt(
                        hir,
                        ast,
                        helper,
                        all_var_defs,
                        fn_up_captures,
                        boxed,
                        Some(&mut inner_refs),
                    );
                }
                inner_refs.retain(|def| {
                    let def_span = hir.definition(*def).name.span;
                    !(def_span.file == span.file
                        && def_span.start >= body_start
                        && def_span.end <= span.end)
                });
                for &captured in &inner_refs {
                    if all_var_defs.contains(&captured) {
                        boxed.insert(captured);
                    }
                    if let Some(outer) = refs.as_deref_mut() {
                        outer.insert(captured);
                    }
                }
            } else {
                for &stmt in statements {
                    walk_stmt(
                        hir,
                        ast,
                        stmt,
                        all_var_defs,
                        fn_up_captures,
                        boxed,
                        refs.as_deref_mut(),
                    );
                }
                for &helper in helpers {
                    walk_stmt(
                        hir,
                        ast,
                        helper,
                        all_var_defs,
                        fn_up_captures,
                        boxed,
                        refs.as_deref_mut(),
                    );
                }
            }
        }
        Expr::Interpolated(parts) => {
            for part in parts {
                if let StringPart::Interpolation(expr) = part {
                    walk_expr(
                        hir,
                        ast,
                        *expr,
                        all_var_defs,
                        fn_up_captures,
                        boxed,
                        refs.as_deref_mut(),
                    );
                }
            }
        }
        Expr::Unary { value, .. } | Expr::Cast { value, .. } => {
            walk_expr(hir, ast, *value, all_var_defs, fn_up_captures, boxed, refs);
        }
        Expr::Binary { left, right, .. } => {
            walk_expr(
                hir,
                ast,
                *left,
                all_var_defs,
                fn_up_captures,
                boxed,
                refs.as_deref_mut(),
            );
            walk_expr(hir, ast, *right, all_var_defs, fn_up_captures, boxed, refs);
        }
        Expr::Wrap { args, .. } => {
            for arg in args {
                walk_expr(
                    hir,
                    ast,
                    arg.value,
                    all_var_defs,
                    fn_up_captures,
                    boxed,
                    refs.as_deref_mut(),
                );
            }
        }
        Expr::Call { callee, args } => {
            walk_expr(
                hir,
                ast,
                *callee,
                all_var_defs,
                fn_up_captures,
                boxed,
                refs.as_deref_mut(),
            );
            for arg in args {
                walk_expr(
                    hir,
                    ast,
                    arg.value,
                    all_var_defs,
                    fn_up_captures,
                    boxed,
                    refs.as_deref_mut(),
                );
            }
        }
        Expr::Pipeline { value, target, .. } => {
            walk_expr(
                hir,
                ast,
                *value,
                all_var_defs,
                fn_up_captures,
                boxed,
                refs.as_deref_mut(),
            );
            walk_expr(hir, ast, *target, all_var_defs, fn_up_captures, boxed, refs);
        }
        Expr::Member { base, member, .. } => {
            walk_expr(
                hir,
                ast,
                *base,
                all_var_defs,
                fn_up_captures,
                boxed,
                refs.as_deref_mut(),
            );
            if let Member::Computed(expr) = member {
                walk_expr(hir, ast, *expr, all_var_defs, fn_up_captures, boxed, refs);
            }
        }
        Expr::Index { base, index, .. } => {
            walk_expr(
                hir,
                ast,
                *base,
                all_var_defs,
                fn_up_captures,
                boxed,
                refs.as_deref_mut(),
            );
            walk_expr(hir, ast, *index, all_var_defs, fn_up_captures, boxed, refs);
        }
        Expr::Tuple(items) | Expr::Array(items) => {
            for &item in items {
                walk_expr(
                    hir,
                    ast,
                    item,
                    all_var_defs,
                    fn_up_captures,
                    boxed,
                    refs.as_deref_mut(),
                );
            }
        }
        Expr::Record { fields, .. } => {
            for field in fields {
                if let Some(expr) = field.value {
                    walk_expr(
                        hir,
                        ast,
                        expr,
                        all_var_defs,
                        fn_up_captures,
                        boxed,
                        refs.as_deref_mut(),
                    );
                } else if let Some(refs) = refs.as_deref_mut()
                    && let Some(Resolution::Definition(id)) = hir.resolve(field.name.span)
                {
                    record_ref(id, fn_up_captures, refs, &mut HashSet::new());
                }
            }
        }
        Expr::Map(entries) => {
            for (k, v) in entries {
                walk_expr(
                    hir,
                    ast,
                    *k,
                    all_var_defs,
                    fn_up_captures,
                    boxed,
                    refs.as_deref_mut(),
                );
                walk_expr(
                    hir,
                    ast,
                    *v,
                    all_var_defs,
                    fn_up_captures,
                    boxed,
                    refs.as_deref_mut(),
                );
            }
        }
        Expr::Range { start, end, .. } => {
            if let Some(s) = start {
                walk_expr(
                    hir,
                    ast,
                    *s,
                    all_var_defs,
                    fn_up_captures,
                    boxed,
                    refs.as_deref_mut(),
                );
            }
            if let Some(e) = end {
                walk_expr(hir, ast, *e, all_var_defs, fn_up_captures, boxed, refs);
            }
        }
        Expr::If {
            condition, yes, no, ..
        } => {
            walk_condition(
                hir,
                ast,
                condition,
                all_var_defs,
                fn_up_captures,
                boxed,
                refs.as_deref_mut(),
            );
            walk_expr(
                hir,
                ast,
                *yes,
                all_var_defs,
                fn_up_captures,
                boxed,
                refs.as_deref_mut(),
            );
            if let Some(no) = no {
                walk_expr(hir, ast, *no, all_var_defs, fn_up_captures, boxed, refs);
            }
        }
        Expr::While { condition, body } => {
            walk_condition(
                hir,
                ast,
                condition,
                all_var_defs,
                fn_up_captures,
                boxed,
                refs.as_deref_mut(),
            );
            walk_expr(hir, ast, *body, all_var_defs, fn_up_captures, boxed, refs);
        }
        Expr::For { iterable, body, .. } => {
            walk_expr(
                hir,
                ast,
                *iterable,
                all_var_defs,
                fn_up_captures,
                boxed,
                refs.as_deref_mut(),
            );
            walk_expr(hir, ast, *body, all_var_defs, fn_up_captures, boxed, refs);
        }
        Expr::Match { value, arms, .. } => {
            walk_expr(
                hir,
                ast,
                *value,
                all_var_defs,
                fn_up_captures,
                boxed,
                refs.as_deref_mut(),
            );
            for arm in arms {
                if let Some(guard) = arm.guard {
                    walk_expr(
                        hir,
                        ast,
                        guard,
                        all_var_defs,
                        fn_up_captures,
                        boxed,
                        refs.as_deref_mut(),
                    );
                }
                walk_expr(
                    hir,
                    ast,
                    arm.body,
                    all_var_defs,
                    fn_up_captures,
                    boxed,
                    refs.as_deref_mut(),
                );
            }
        }
        Expr::Transfer { value: Some(v), .. } => {
            walk_expr(hir, ast, *v, all_var_defs, fn_up_captures, boxed, refs);
        }
        Expr::Literal(_)
        | Expr::Unit
        | Expr::Quote(_)
        | Expr::Meta(_)
        | Expr::Accessor(_)
        | Expr::Hole
        | Expr::Transfer { value: None, .. } => {}
    }
}
