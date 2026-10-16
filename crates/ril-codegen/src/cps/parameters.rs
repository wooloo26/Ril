//! Callee-side defaults run only for missing slots, in declaration order.
use super::*;

fn integer(value: usize, span: Span) -> Expr {
    expression(
        ExprKind::Literal(core::Literal::Integer {
            value: value as i128,
            bits: 64,
            signed: true,
        }),
        span,
    )
}
fn binary(operator: &str, left: Expr, right: Expr, span: Span) -> Expr {
    expression(
        ExprKind::Binary {
            operator: operator.into(),
            left: Box::new(left),
            right: Box::new(right),
        },
        span,
    )
}
impl Builder {
    pub(super) fn parameters(
        &mut self,
        parameters: &[core::Parameter],
        mut next: BlockId,
    ) -> Result<BlockId, NotImplemented> {
        self.locals.insert(cps::ARGUMENTS.into());
        // Graph construction runs backwards; execution binds left to right.
        for (index, parameter) in parameters.iter().enumerate().rev() {
            let supplied = expression(
                ExprKind::Index {
                    base: Box::new(name(cps::ARGUMENTS, self.span)),
                    index: Box::new(integer(index, self.span)),
                    safe: false,
                },
                self.span,
            );
            let value = if let Some(default) = &parameter.default {
                let span = default.span;
                let length = expression(
                    ExprKind::Call {
                        callback_entry: false,
                        callee: Box::new(name("Prelude::len", span)),
                        arguments: vec![core::Argument {
                            label: None,
                            value: name(cps::ARGUMENTS, span),
                        }],
                    },
                    span,
                );
                let missing = expression(
                    ExprKind::Is {
                        value: Box::new(supplied.clone()),
                        pattern: Pattern::Constructor {
                            tag: ril_ir::native::MISSING_ARGUMENT_TAG.into(),
                            arguments: vec![],
                        },
                    },
                    span,
                );
                let present = binary(
                    "&&",
                    binary(">", length, integer(index + 1, span), span),
                    expression(
                        ExprKind::Unary {
                            operator: "!".into(),
                            operand: Box::new(missing),
                        },
                        span,
                    ),
                    span,
                );
                expression(
                    ExprKind::If {
                        condition: Box::new(present),
                        then_branch: Box::new(supplied),
                        else_branch: Some(Box::new(default.clone())),
                    },
                    span,
                )
            } else {
                supplied
            };
            let temporary = self.temporary();
            let bound = self.block(
                Input::Continue(None),
                vec![Statement::Bind {
                    pattern: parameter.pattern.clone(),
                    value: name(&temporary, value.span),
                    scoped: false,
                }],
                Terminator::Jump(next),
            );
            next = self.expr(&value, &temporary, bound)?;
        }
        Ok(next)
    }
}
