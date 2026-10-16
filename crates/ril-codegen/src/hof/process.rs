//! Internal Child scopes span the callback and terminate/reap on every exit.
use super::*;

fn is_error(value: &str, span: Span) -> Expr {
    expr(
        ExprKind::Is {
            value: Box::new(name(value, span)),
            pattern: Pattern::Constructor {
                tag: "Prelude::Err".into(),
                arguments: vec![],
            },
        },
        span,
    )
}
impl Lower {
    pub(super) fn process(&mut self, arguments: &[Expr], span: Span) -> Expr {
        let command = self.temporary("command");
        let action = self.temporary("action");
        let spawned = self.temporary("spawned");
        let child = self.temporary("child");
        let result = self.temporary("result");
        let terminated = self.temporary("terminated");
        let body = block(
            vec![
                Statement::Bind {
                    pattern: Pattern::Name(child.clone()),
                    value: call(
                        name("__variant_payload", span),
                        vec![name(&spawned, span)],
                        span,
                    ),
                    scoped: true,
                },
                bind(
                    &result,
                    callback_call(name(&action, span), vec![name(&child, span)], span),
                ),
                bind(
                    &terminated,
                    call(
                        name("Process::terminate", span),
                        vec![name(&child, span)],
                        span,
                    ),
                ),
            ],
            conditional(
                is_error(&result, span),
                name(&result, span),
                conditional(
                    is_error(&terminated, span),
                    name(&terminated, span),
                    name(&result, span),
                    span,
                ),
                span,
            ),
            span,
        );
        block(
            vec![
                bind(&command, arguments[0].clone()),
                bind(&action, arguments[1].clone()),
                bind(
                    &spawned,
                    call(
                        name("Process::spawn", span),
                        vec![name(&command, span)],
                        span,
                    ),
                ),
            ],
            conditional(is_error(&spawned, span), name(&spawned, span), body, span),
            span,
        )
    }
}
