//! Canonical generated syntax is a reconstruction rule, not a source receipt.
//! Its caller must additionally prove the real creation event and capture roots.
use ril_compiler_core::source::{FileId, Span};
use ril_syntax::ast::*;

pub(crate) fn iterator_lambda(
    source: u32,
    identity: &str,
    state: &TypeExpr,
    item: &TypeExpr,
    captures: usize,
) -> Option<Expr> {
    if captures > 2 {
        return None;
    }
    crate::static_eval::effects::bounded_argument_key(state, &Default::default())?;
    crate::static_eval::effects::bounded_argument_key(item, &Default::default())?;
    let base = source.checked_mul(32)?;
    let span = |start: u32, end: u32| -> Option<Span> {
        Some(Span {
            file: FileId(u32::MAX - 1),
            start: base.checked_add(start)?,
            end: base.checked_add(end)?,
        })
    };
    let parameter = Parameter {
        pattern: Pattern {
            kind: PatternKind::Name("ril__iter_state".into()),
            span: span(1, 2)?,
        },
        mode: ParameterMode::Read,
        ty: Some(state.clone()),
        default: None,
        span: span(1, 2)?,
    };
    let mut arguments = Vec::new();
    for index in 0..=captures {
        let name = if index == 0 {
            "ril__iter_state".into()
        } else {
            format!("ril__iter_capture_{}", index - 1)
        };
        let ordinal = u32::try_from(index).ok()?;
        let actual_span = span(8 + ordinal, 9 + ordinal)?;
        arguments.push(Argument {
            label: None,
            mode: ParameterMode::Read,
            value: Expr {
                kind: ExprKind::Name(name),
                span: actual_span,
            },
            span: actual_span,
        });
    }
    Some(Expr {
        span: span(0, 32)?,
        kind: ExprKind::Lambda {
            parameters: vec![parameter],
            return_type: Some(TypeExpr {
                text: String::new(),
                span: span(2, 3)?,
                kind: TypeKind::Name {
                    path: vec!["Iter".into(), "Step".into()],
                    arguments: vec![state.clone(), item.clone()],
                },
            }),
            annotations: vec![],
            body: Box::new(Expr {
                span: span(4, 16)?,
                kind: ExprKind::Call {
                    callee: Box::new(Expr {
                        kind: ExprKind::Name(identity.into()),
                        span: span(5, 6)?,
                    }),
                    arguments,
                },
            }),
        },
    })
}
