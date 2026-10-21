//! Callable creation sites and the storage visible at their executable roots.
use super::*;

pub(super) enum Callable<'a> {
    Named(&'a core::Function),
    Lambda(&'a Expr),
}

pub(super) struct Creation<'a> {
    pub callable: Callable<'a>,
    pub bound: BTreeSet<String>,
}

pub(super) fn function<'a>(
    function: &'a core::Function,
    inherited: &BTreeSet<String>,
) -> Vec<Creation<'a>> {
    let mut found = Vec::new();
    let mut bound = inherited.clone();
    parameters(&function.parameters, &mut bound, &mut found);
    block(&function.body, &bound, &mut found);
    found
}

fn parameters<'a>(
    parameters: &'a [core::Parameter],
    bound: &mut BTreeSet<String>,
    found: &mut Vec<Creation<'a>>,
) {
    // A default sees captures and earlier parameters, before the body scope.
    for parameter in parameters {
        if let Some(default) = &parameter.default {
            expression(default, bound, found);
        }
        names(&parameter.pattern, bound);
    }
}

fn block<'a>(block: &'a core::Block, outer: &BTreeSet<String>, found: &mut Vec<Creation<'a>>) {
    let mut bound = outer.clone();
    // Where declarations are hoisted; their environments include later locals.
    for statement in &block.statements {
        match statement {
            Statement::Bind { pattern, .. } => names(pattern, &mut bound),
            Statement::Function(function) => {
                bound.insert(function.name.clone());
            }
            _ => {}
        }
    }
    for statement in &block.statements {
        match statement {
            Statement::Function(function) => found.push(Creation {
                callable: Callable::Named(function),
                bound: bound.clone(),
            }),
            Statement::Bind { value, .. } => expression(value, &bound, found),
            Statement::Assign { target, value, .. } => {
                expression(target, &bound, found);
                expression(value, &bound, found);
            }
            Statement::Expr {
                expression: value, ..
            } => expression(value, &bound, found),
            Statement::Handle { arms, .. } => {
                for arm in arms {
                    let mut own = bound.clone();
                    parameters(&arm.parameters, &mut own, found);
                    expression(&arm.body, &own, found);
                }
            }
        }
    }
}

fn expression<'a>(expr: &'a Expr, bound: &BTreeSet<String>, found: &mut Vec<Creation<'a>>) {
    visit_expr(expr, &mut |expr| match &expr.kind {
        ExprKind::Lambda { .. } => {
            found.push(Creation {
                callable: Callable::Lambda(expr),
                bound: bound.clone(),
            });
            // Defaults and the body belong to the lifted callable's own scope.
            false
        }
        ExprKind::Block(body) | ExprKind::Loop { body, .. } => {
            block(body, bound, found);
            false
        }
        ExprKind::While {
            condition, body, ..
        } => {
            expression(condition, bound, found);
            block(body, bound, found);
            false
        }
        ExprKind::For {
            iterable,
            pattern,
            body,
            ..
        } => {
            expression(iterable, bound, found);
            let mut own = bound.clone();
            names(pattern, &mut own);
            block(body, &own, found);
            false
        }
        ExprKind::Match { value, arms } => {
            expression(value, bound, found);
            for arm in arms {
                visit_pattern_values(&arm.pattern, &mut |value| {
                    expression(value, bound, found);
                    false
                });
                let mut own = bound.clone();
                names(&arm.pattern, &mut own);
                if let Some(guard) = &arm.guard {
                    expression(guard, &own, found);
                }
                expression(&arm.body, &own, found);
            }
            false
        }
        _ => true,
    });
}
