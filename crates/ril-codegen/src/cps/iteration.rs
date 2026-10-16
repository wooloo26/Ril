//! Streaming native cursors handle ranges without representing their length.
use super::*;

fn call(target: &str, arguments: Vec<Expr>, span: Span) -> Expr {
    expression(
        ExprKind::Call {
            callback_entry: false,
            callee: Box::new(name(target, span)),
            arguments: arguments
                .into_iter()
                .map(|value| core::Argument { label: None, value })
                .collect(),
        },
        span,
    )
}
fn bind(target: &str, value: Expr) -> Statement {
    Statement::Bind {
        pattern: Pattern::Name(target.into()),
        value,
        scoped: false,
    }
}
impl Builder {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn for_loop(
        &mut self,
        iterable: &Expr,
        pattern: &Pattern,
        body: &core::Block,
        charge: Option<core::ChargeEvent>,
        destination: &str,
        next: BlockId,
        span: Span,
    ) -> Result<BlockId, NotImplemented> {
        let cursor = self.temporary();
        let item = self.temporary();
        // The cursor advances before user code. A `next` therefore never
        // repeats an item; `last` never forces another range increment.
        let mut statements = vec![
            bind(&item, call("__iter_next", vec![name(&cursor, span)], span)),
            Statement::Expr {
                expression: expression(
                    ExprKind::If {
                        condition: Box::new(expression(
                            ExprKind::Is {
                                value: Box::new(name(&item, span)),
                                pattern: Pattern::Constructor {
                                    tag: "Prelude::None".into(),
                                    arguments: vec![],
                                },
                            },
                            span,
                        )),
                        then_branch: Box::new(expression(
                            ExprKind::Control {
                                operation: core::ControlOperation::Last,
                                value: None,
                            },
                            span,
                        )),
                        else_branch: None,
                    },
                    span,
                ),
                terminated: true,
            },
            Statement::Bind {
                pattern: pattern.clone(),
                value: call("__variant_payload", vec![name(&item, span)], span),
                scoped: false,
            },
        ];
        statements.extend(body.statements.iter().cloned());
        let lowered = expression(
            ExprKind::Block(core::Block {
                statements: vec![
                    bind(&cursor, call("__iter_start", vec![iterable.clone()], span)),
                    Statement::Expr {
                        expression: expression(
                            ExprKind::Loop {
                                body: core::Block { statements },
                                charge,
                            },
                            span,
                        ),
                        terminated: false,
                    },
                ],
            }),
            span,
        );
        self.expr(&lowered, destination, next)
    }
}
