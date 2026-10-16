//! Independent source-token walk for scoped formal identity. Nested named
//! functions and lambdas have their own owners and cannot lend a token.
use super::*;
use crate::sema::{copy_contract::CopyInvocation, model::Callable};

pub(super) fn source_expressions(function: &ril_syntax::ast::Function) -> Check<Vec<&Expr>> {
    enum Pending<'a> {
        Statement(&'a Stmt, usize),
        Expression(&'a Expr, usize),
    }
    let mut pending = Vec::new();
    if let Some(body) = &function.body {
        pending.extend(
            body.statements
                .iter()
                .chain(&body.where_items)
                .map(|statement| Pending::Statement(statement, 0)),
        );
    }
    let mut result = Vec::new();
    let mut work = LIMIT;
    while let Some(current) = pending.pop() {
        require(work > 0, "scoped source token walk exceeds replay budget")?;
        work -= 1;
        match current {
            Pending::Statement(statement, depth) => {
                require(
                    depth < 128,
                    "scoped source statement token walk is too deep",
                )?;
                let mut expression = |value| pending.push(Pending::Expression(value, depth + 1));
                match &statement.kind {
                    StmtKind::Binding(binding) => {
                        expression(&binding.value);
                        if let Some(fallback) = &binding.fallback {
                            expression(fallback)
                        }
                    }
                    StmtKind::Assignment { target, value, .. } => {
                        expression(target);
                        expression(value)
                    }
                    StmtKind::Expr {
                        expression: value, ..
                    }
                    | StmtKind::HandlerApplication(value) => expression(value),
                    StmtKind::Handler(arms) => {
                        for arm in arms {
                            expression(&arm.operation);
                            expression(&arm.body)
                        }
                    }
                    StmtKind::Function(_)
                    | StmtKind::Type(_)
                    | StmtKind::Effect(_)
                    | StmtKind::Use(_) => {}
                }
            }
            Pending::Expression(expression, depth) => {
                require(
                    depth < 128,
                    "scoped source expression token walk is too deep",
                )?;
                result.push(expression);
                let mut children = Vec::new();
                let mut blocks = Vec::new();
                match &expression.kind {
                    ExprKind::Field { base, .. } | ExprKind::Generic { base, .. } => {
                        children.push(base.as_ref())
                    }
                    ExprKind::ComputedField { base, key } => {
                        children.extend([base.as_ref(), key.as_ref()])
                    }
                    ExprKind::Index { base, index, .. } => {
                        children.extend([base.as_ref(), index.as_ref()])
                    }
                    ExprKind::Unary { operand, .. } => children.push(operand),
                    ExprKind::Binary { left, right, .. } => {
                        children.extend([left.as_ref(), right.as_ref()])
                    }
                    ExprKind::Call { callee, arguments } => {
                        children.push(callee);
                        children.extend(arguments.iter().map(|argument| &argument.value));
                    }
                    // An outer declaration cannot borrow a nested owner's Name.
                    ExprKind::Lambda { .. } => {}
                    ExprKind::Block(block) | ExprKind::Loop(block) => blocks.push(block),
                    ExprKind::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        children.extend([condition.as_ref(), then_branch.as_ref()]);
                        children.extend(else_branch.iter().map(Box::as_ref));
                    }
                    ExprKind::Match { value, arms, .. } => {
                        children.push(value);
                        for arm in arms {
                            children.push(&arm.body);
                            children.extend(arm.guard.iter());
                        }
                    }
                    ExprKind::Is { value, .. } => children.push(value),
                    ExprKind::While { condition, body } => {
                        children.push(condition);
                        blocks.push(body);
                    }
                    ExprKind::For { iterable, body, .. } => {
                        children.push(iterable);
                        blocks.push(body);
                    }
                    ExprKind::Control { value, .. } => {
                        children.extend(value.iter().map(Box::as_ref))
                    }
                    ExprKind::Derive { base, recipe } => {
                        children.extend(base.iter().map(Box::as_ref));
                        children.push(recipe);
                    }
                    ExprKind::Range { start, end, .. } => {
                        children.extend(start.iter().map(Box::as_ref));
                        children.extend(end.iter().map(Box::as_ref));
                    }
                    ExprKind::Tuple(items) | ExprKind::Array(items) => children.extend(items),
                    ExprKind::Map(items) => {
                        for (key, value) in items {
                            children.extend([key, value]);
                        }
                    }
                    ExprKind::Record { members, .. } => {
                        for member in members {
                            match member {
                                ril_syntax::ast::RecordMember::Field(field) => {
                                    children.push(&field.value)
                                }
                                ril_syntax::ast::RecordMember::Spread(value) => {
                                    children.push(value)
                                }
                            }
                        }
                    }
                    ExprKind::Interpolated(parts) => {
                        for part in parts {
                            if let StringPart::Interpolation { expression, .. } = part {
                                children.push(expression);
                            }
                        }
                    }
                    ExprKind::Name(_)
                    | ExprKind::Path(_)
                    | ExprKind::Literal(_)
                    | ExprKind::Accessor(_)
                    | ExprKind::TypeValue(_)
                    | ExprKind::KeyOf(_)
                    | ExprKind::Ambient
                    | ExprKind::Error => {}
                }
                pending.extend(
                    children
                        .into_iter()
                        .map(|child| Pending::Expression(child, depth + 1)),
                );
                for block in blocks {
                    pending.extend(
                        block
                            .statements
                            .iter()
                            .chain(&block.where_items)
                            .map(|statement| Pending::Statement(statement, depth + 1)),
                    );
                }
            }
        }
    }
    Ok(result)
}

impl Replay<'_> {
    pub(super) fn actual_parent_source_edge(
        &self,
        child: &CopyInvocation,
        parent: &CopyInvocation,
    ) -> Check {
        let owner = CallableOwner::Function(parent.target);
        require(
            child.parent == Some(parent.id)
                && child.caller == Some(parent.target)
                && child.caller_owner == Some(owner),
            "scoped caller edge does not belong to its actual parent declaration",
        )?;
        let event = child
            .source_event
            .and_then(|id| {
                self.facts
                    .copy_call_events
                    .get(id.0 as usize)
                    .filter(|event| event.id == id)
            })
            .ok_or_else(|| "scoped caller edge has no actual source application".to_owned())?;
        require(
            event.parent == Some(parent.id)
                && event.owner == Some(owner)
                && event.target == Some(child.target)
                && event.span == child.span,
            "scoped caller edge borrowed another actual source application",
        )?;
        let expression_index = event
            .callee_expression
            .ok_or_else(|| "scoped caller edge has no actual callee observation".to_owned())?;
        let observed = self
            .facts
            .expressions
            .get(expression_index)
            .ok_or_else(|| "scoped callee expression index is outside its arena".to_owned())?;
        let tokens = source_expressions(&self.function(parent.target)?.syntax)?;
        let matching: Vec<_> = tokens
            .iter()
            .filter_map(|token| {
                if token.span != event.span {
                    return None;
                }
                let ExprKind::Call { callee, arguments } = &token.kind else {
                    return None;
                };
                (callee.span == observed.span).then_some((callee, arguments))
            })
            .collect();
        require(
            matching.len() == 1,
            "scoped caller edge has no unique real Call/callee source token",
        )?;
        let (_, arguments) = matching[0];
        require(
            arguments.len() == self.function(child.target)?.syntax.parameters.len()
                && arguments.len() == child.arguments.len(),
            "scoped source application lacks a complete explicit argument table",
        )?;
        let observations: Vec<_> = self
            .facts
            .invocation_expressions
            .iter()
            .filter(|observation| {
                observation.expression == expression_index
                    && observation.context.invocation == Some(parent.id)
                    && observation.context.owner == Some(owner)
            })
            .collect();
        require(
            observations.len() == 1,
            "scoped callee token has no unique original invocation observation",
        )?;
        let [Callable::Named(function)] = observed.value.callables.as_slice() else {
            return Err("scoped caller callee is not its actual named target".into());
        };
        require(
            self.facts
                .functions
                .get(*function)
                .is_some_and(|function| function.definition == child.target),
            "scoped caller callee observation resolves another definition",
        )
    }
}
