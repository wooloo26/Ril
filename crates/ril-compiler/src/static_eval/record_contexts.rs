//! Elaborate only newly constructed record slots at a written type boundary.
//! Names and calls retain their existing value types and cannot gain slot modes.
use super::*;
use std::borrow::Cow;

pub(super) fn expression<'a>(value: &'a Expr, expected: Option<&TypeExpr>) -> Cow<'a, Expr> {
    let Some(expected) = expected else {
        return Cow::Borrowed(value);
    };
    let mut contextual = value.clone();
    if apply(&mut contextual, expected) {
        Cow::Owned(contextual)
    } else {
        Cow::Borrowed(value)
    }
}

pub(super) fn block<'a>(body: &'a Block, expected: Option<&TypeExpr>) -> Cow<'a, Block> {
    let Some(expected) = expected else {
        return Cow::Borrowed(body);
    };
    let mut contextual = body.clone();
    if tail(&mut contextual, expected) {
        Cow::Owned(contextual)
    } else {
        Cow::Borrowed(body)
    }
}

fn tail(body: &mut Block, expected: &TypeExpr) -> bool {
    if let Some(Stmt {
        kind: StmtKind::Expr {
            expression,
            terminated: false,
        },
        ..
    }) = body.statements.last_mut()
    {
        apply(expression, expected)
    } else {
        false
    }
}

fn apply(value: &mut Expr, expected: &TypeExpr) -> bool {
    match &mut value.kind {
        ExprKind::Record { ty, .. } if ty.is_none() => {
            *ty = Some(expected.clone());
            true
        }
        ExprKind::Block(body) => tail(body, expected),
        ExprKind::If {
            then_branch,
            else_branch,
            ..
        } => {
            let changed = apply(then_branch, expected);
            // Do not short-circuit: both syntactic alternatives are checked.
            else_branch
                .as_mut()
                .is_some_and(|branch| apply(branch, expected))
                | changed
        }
        ExprKind::Match { arms, .. } => {
            let mut changed = false;
            for arm in arms {
                changed |= apply(&mut arm.body, expected);
            }
            changed
        }
        // Return expressions use the containing callable's result type, which
        // is not necessarily this binding's context. Nested callable bodies
        // also have their own contract and are never rewritten here.
        _ => false,
    }
}
