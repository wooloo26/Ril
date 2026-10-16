//! Stream callbacks remain structured calls across each partial transfer.
use super::*;

fn field(base: &str, field: &str, span: Span) -> Expr {
    expr(
        ExprKind::Field {
            base: Box::new(name(base, span)),
            field: field.into(),
            safe: false,
        },
        span,
    )
}
fn is_tag(value: &str, tag: &str, span: Span) -> Expr {
    expr(
        ExprKind::Is {
            value: Box::new(name(value, span)),
            pattern: Pattern::Constructor {
                tag: format!("Prelude::{tag}"),
                arguments: vec![],
            },
        },
        span,
    )
}
fn payload(value: &str, span: Span) -> Expr {
    call(
        name("__variant_payload", span),
        vec![name(value, span)],
        span,
    )
}
fn last(value: Expr, span: Span) -> Expr {
    expr(
        ExprKind::Control {
            operation: core::ControlOperation::Last,
            value: Some(Box::new(value)),
        },
        span,
    )
}
impl Lower {
    pub(super) fn io(&mut self, operation: &str, arguments: &[Expr], span: Span) -> Expr {
        let receiver = self.temporary("stream");
        let ops = self.temporary("ops");
        let callback = self.temporary("transfer");
        let mut setup = vec![bind(&receiver, arguments[0].clone())];
        let body = if operation == "Io::read_all" {
            setup.extend([
                bind(&ops, arguments[1].clone()),
                bind(&callback, field(&ops, "read", span)),
            ]);
            self.read_all(&receiver, &callback, &mut setup, span)
        } else {
            let remaining = self.temporary("remaining");
            setup.extend([
                bind(&remaining, arguments[1].clone()),
                bind(&ops, arguments[2].clone()),
                bind(&callback, field(&ops, "write", span)),
            ]);
            self.write_all(&receiver, &callback, &remaining, span)
        };
        block(
            setup,
            expr(
                ExprKind::Loop {
                    body: core::Block { statements: body },
                    charge: None,
                },
                span,
            ),
            span,
        )
    }
    fn read_all(
        &mut self,
        receiver: &str,
        callback: &str,
        setup: &mut Vec<Statement>,
        span: Span,
    ) -> Vec<Statement> {
        let accumulator = self.temporary("accumulator");
        let reply = self.temporary("reply");
        let chunk = self.temporary("chunk");
        setup.push(bind(
            &accumulator,
            call(name("__io_acc_new", span), vec![], span),
        ));
        // A positive request distinguishes EOF from a zero-request validation.
        let maximum = integer(65_536, span);
        vec![
            bind(
                &reply,
                call(
                    name("__io_read_validate", span),
                    vec![
                        callback_call(
                            name(callback, span),
                            vec![name(receiver, span), maximum.clone()],
                            span,
                        ),
                        maximum,
                    ],
                    span,
                ),
            ),
            statement(conditional(
                is_tag(&reply, "Err", span),
                last(name(&reply, span), span),
                unit(span),
                span,
            )),
            bind(&chunk, payload(&reply, span)),
            statement(call(
                name("__io_acc_push", span),
                vec![name(&accumulator, span), field(&chunk, "data", span)],
                span,
            )),
            statement(conditional(
                field(&chunk, "end", span),
                last(
                    call(
                        name("Prelude::Ok", span),
                        vec![call(
                            name("__io_acc_finish", span),
                            vec![name(&accumulator, span)],
                            span,
                        )],
                        span,
                    ),
                    span,
                ),
                unit(span),
                span,
            )),
        ]
    }
    fn write_all(
        &mut self,
        receiver: &str,
        callback: &str,
        remaining: &str,
        span: Span,
    ) -> Vec<Statement> {
        let progress = self.temporary("progress");
        let error = self.temporary("error");
        vec![
            bind(
                &progress,
                call(
                    name("__io_write_validate", span),
                    vec![
                        callback_call(
                            name(callback, span),
                            vec![name(receiver, span), name(remaining, span)],
                            span,
                        ),
                        name(remaining, span),
                    ],
                    span,
                ),
            ),
            bind(&error, field(&progress, "error", span)),
            statement(conditional(
                is_tag(&error, "Some", span),
                last(
                    call(
                        name("Prelude::Err", span),
                        vec![payload(&error, span)],
                        span,
                    ),
                    span,
                ),
                unit(span),
                span,
            )),
            assign(
                remaining,
                call(
                    name("__io_bytes_suffix", span),
                    vec![name(remaining, span), field(&progress, "written", span)],
                    span,
                ),
                span,
            ),
            statement(conditional(
                expr(
                    ExprKind::Binary {
                        operator: "==".into(),
                        left: Box::new(call(
                            name("Prelude::len", span),
                            vec![name(remaining, span)],
                            span,
                        )),
                        right: Box::new(integer(0, span)),
                    },
                    span,
                ),
                last(call(name("Prelude::Ok", span), vec![], span), span),
                unit(span),
                span,
            )),
        ]
    }
}
