//! Fallback transfers use the same callable and loop boundaries as ordinary
//! checking. Walk owned AST nodes, including dead branches; never source text.
use super::*;

enum Node<'a> {
    Expr(&'a Expr),
    Block(&'a Block),
    Stmt(&'a Stmt),
    Type(&'a TypeExpr),
    Pattern(&'a Pattern),
}

pub(super) fn validate(expression: &Expr, budget: &budget::Budget) -> Result<()> {
    let mut pending = vec![(Node::Expr(expression), 0usize, 0usize)];
    let mut nodes = 0usize;
    while let Some((node, loops, depth)) = pending.pop() {
        nodes += 1;
        budget.work(1)?;
        if nodes > 4096 || depth >= 64 || pending.len() > 4096 {
            return Err(Failure::Unsupported(
                "fallback control boundary exceeds its finite AST allowance".into(),
            ));
        }
        let mut push = |node, loops| pending.push((node, loops, depth + 1));
        match node {
            Node::Expr(expr) => match &expr.kind {
                ExprKind::Control { operation, value } => {
                    if *operation == ControlOperation::Return
                        || (matches!(operation, ControlOperation::Last | ControlOperation::Next)
                            && loops == 0)
                    {
                        return Err(Failure::Diagnostic(
                            "E0710",
                            "control transfer escapes an optional/Result fallback".into(),
                        ));
                    }
                    if let Some(value) = value {
                        push(Node::Expr(value), loops);
                    }
                }
                ExprKind::Lambda { .. } => {}
                ExprKind::Block(body) => push(Node::Block(body), loops),
                ExprKind::Loop(body) => push(Node::Block(body), loops + 1),
                ExprKind::While { condition, body } => {
                    push(Node::Expr(condition), loops);
                    push(Node::Block(body), loops + 1);
                }
                ExprKind::WhileLet {
                    pattern,
                    value,
                    body,
                } => {
                    push(Node::Expr(value), loops);
                    push(Node::Pattern(pattern), loops);
                    push(Node::Block(body), loops + 1);
                }
                ExprKind::For {
                    iterable,
                    pattern,
                    body,
                } => {
                    push(Node::Expr(iterable), loops);
                    push(Node::Pattern(pattern), loops + 1);
                    push(Node::Block(body), loops + 1);
                }
                ExprKind::Unary { operator, operand } => {
                    if operator == "?" {
                        return Err(Failure::Diagnostic(
                            "E0710",
                            "propagation escapes a fallback expression".into(),
                        ));
                    }
                    push(Node::Expr(operand), loops);
                }
                ExprKind::Tuple(values) | ExprKind::Array(values) => {
                    for value in values {
                        push(Node::Expr(value), loops);
                    }
                }
                ExprKind::Map(values) => {
                    for (key, value) in values {
                        push(Node::Expr(key), loops);
                        push(Node::Expr(value), loops);
                    }
                }
                ExprKind::Record { ty, members, .. } => {
                    if let Some(ty) = ty {
                        push(Node::Type(ty), loops);
                    }
                    for member in members {
                        push(
                            Node::Expr(match member {
                                RecordMember::Field(field) => &field.value,
                                RecordMember::Spread(value) => value,
                            }),
                            loops,
                        );
                    }
                }
                ExprKind::Interpolated(parts) => {
                    for part in parts {
                        if let StringPart::Interpolation { expression, .. } = part {
                            push(Node::Expr(expression), loops);
                        }
                    }
                }
                ExprKind::Binary { left, right, .. }
                | ExprKind::Index {
                    base: left,
                    index: right,
                    ..
                }
                | ExprKind::ComputedField {
                    base: left,
                    key: right,
                } => {
                    push(Node::Expr(left), loops);
                    push(Node::Expr(right), loops);
                }
                ExprKind::Field { base, .. } => push(Node::Expr(base), loops),
                ExprKind::Call { callee, arguments } => {
                    push(Node::Expr(callee), loops);
                    for argument in arguments {
                        push(Node::Expr(&argument.value), loops);
                    }
                }
                ExprKind::Generic { base, arguments } => {
                    push(Node::Expr(base), loops);
                    for argument in arguments {
                        push(Node::Type(argument), loops);
                    }
                }
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    push(Node::Expr(condition), loops);
                    push(Node::Expr(then_branch), loops);
                    if let Some(branch) = else_branch {
                        push(Node::Expr(branch), loops);
                    }
                }
                ExprKind::IfLet {
                    pattern,
                    value,
                    then_branch,
                    else_branch,
                } => {
                    push(Node::Expr(value), loops);
                    push(Node::Pattern(pattern), loops);
                    push(Node::Expr(then_branch), loops);
                    if let Some(branch) = else_branch {
                        push(Node::Expr(branch), loops);
                    }
                }
                ExprKind::Match { value, arms, .. } => {
                    push(Node::Expr(value), loops);
                    for arm in arms {
                        push(Node::Pattern(&arm.pattern), loops);
                        if let Some(guard) = &arm.guard {
                            push(Node::Expr(guard), loops);
                        }
                        push(Node::Expr(&arm.body), loops);
                    }
                }
                ExprKind::Is { value, pattern } => {
                    push(Node::Expr(value), loops);
                    push(Node::Pattern(pattern), loops);
                }
                ExprKind::TypeValue(ty) | ExprKind::KeyOf(ty) => push(Node::Type(ty), loops),
                ExprKind::Derive { base, recipe } => {
                    if let Some(base) = base {
                        push(Node::Expr(base), loops);
                    }
                    push(Node::Expr(recipe), loops);
                }
                ExprKind::Range { start, end, .. } => {
                    for value in start.iter().chain(end) {
                        push(Node::Expr(value), loops);
                    }
                }
                _ => {}
            },
            Node::Block(body) => {
                for statement in body.where_items.iter().chain(&body.statements) {
                    push(Node::Stmt(statement), loops);
                }
            }
            Node::Stmt(statement) => match &statement.kind {
                StmtKind::Function(_) | StmtKind::Use(_) => {}
                StmtKind::Binding(binding) => {
                    push(Node::Pattern(&binding.pattern), loops);
                    if let Some(ty) = &binding.ty {
                        push(Node::Type(ty), loops);
                    }
                    push(Node::Expr(&binding.value), loops);
                    if let Some(fallback) = &binding.fallback {
                        push(Node::Expr(fallback), loops);
                    }
                }
                StmtKind::Assignment { target, value, .. } => {
                    push(Node::Expr(target), loops);
                    push(Node::Expr(value), loops);
                }
                StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                    push(Node::Expr(expression), loops)
                }
                StmtKind::Type(declaration) => {
                    if let Some(ty) = &declaration.value {
                        push(Node::Type(ty), loops);
                    }
                }
                StmtKind::Effect(declaration) => {
                    for member in &declaration.members {
                        push(Node::Type(member), loops);
                    }
                }
                StmtKind::Handler(arms) => {
                    for arm in arms {
                        push(Node::Expr(&arm.operation), loops);
                    }
                }
            },
            Node::Type(ty) => match &ty.kind {
                TypeKind::Callable { .. } | TypeKind::TypeFunction { .. } => {}
                TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
                    for argument in arguments {
                        push(Node::Type(argument), loops);
                    }
                }
                TypeKind::Optional(value)
                | TypeKind::Rest(value)
                | TypeKind::KeyOf(value)
                | TypeKind::Projection { base: value, .. } => push(Node::Type(value), loops),
                TypeKind::Array { element, length } => {
                    push(Node::Type(element), loops);
                    if let Some(length) = length {
                        push(Node::Expr(length), loops);
                    }
                }
                TypeKind::Map { key, value }
                | TypeKind::KindArrow {
                    parameter: key,
                    result: value,
                } => {
                    push(Node::Type(key), loops);
                    push(Node::Type(value), loops);
                }
                TypeKind::Record { fields, row } => {
                    for field in fields {
                        push(Node::Type(&field.ty), loops);
                    }
                    if let Some(row) = row {
                        push(Node::Type(row), loops);
                    }
                }
                TypeKind::Computation(value) => push(Node::Expr(value), loops),
                TypeKind::ComputedProjection { base, key } => {
                    push(Node::Type(base), loops);
                    push(Node::Expr(key), loops);
                }
                TypeKind::Mapped { keys, value, .. } => {
                    push(Node::Expr(keys), loops);
                    push(Node::Type(value), loops);
                }
                TypeKind::Error => {}
            },
            Node::Pattern(pattern) => match &pattern.kind {
                PatternKind::Value(value) => push(Node::Expr(value), loops),
                PatternKind::Type { ty, .. } => push(Node::Type(ty), loops),
                PatternKind::Mode { pattern, .. } => push(Node::Pattern(pattern), loops),
                PatternKind::Tuple(values)
                | PatternKind::Array(values)
                | PatternKind::Alternative(values)
                | PatternKind::Constructor {
                    arguments: values, ..
                } => {
                    for value in values {
                        push(Node::Pattern(value), loops);
                    }
                }
                PatternKind::Record { ty, fields, .. } => {
                    if let Some(ty) = ty {
                        push(Node::Type(ty), loops);
                    }
                    for field in fields {
                        push(Node::Pattern(&field.pattern), loops);
                    }
                }
                _ => {}
            },
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(source: &str) -> Result<()> {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{source}: {:?}", parsed.diagnostics);
        let StmtKind::Expr { expression, .. } = &parsed.program.statements[0].kind else {
            panic!("expected expression source");
        };
        validate(expression, &budget::Budget::default())
    }

    #[test]
    fn actual_ast_boundaries_distinguish_outer_transfers_from_local_callables_and_loops() {
        for source in [
            "{return 9}",
            "{if false{return 9};7}",
            "{last 9}",
            "{next;9}",
            "Some(9)?",
            "helper({return 9})",
        ] {
            assert!(
                matches!(check(source), Err(Failure::Diagnostic("E0710", _))),
                "{source}"
            );
        }
        for source in [
            "(\\->{return 9})()",
            "{local() where fn local()->int{return 9}}",
            "loop{last 9}",
            "{for [1] as item{next};9}",
            "while false{next}",
        ] {
            check(source).unwrap_or_else(|_| panic!("local control must remain local: {source}"));
        }
    }
}
