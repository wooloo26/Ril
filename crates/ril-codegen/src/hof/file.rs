//! Scoped native file authority spans callback suspension and abnormal exits.
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
    pub(super) fn file(&mut self, arguments: &[Expr], span: Span) -> Expr {
        let path = self.temporary("path");
        let mode = self.temporary("mode");
        let action = self.temporary("action");
        let opened = self.temporary("opened");
        let file = self.temporary("file");
        let result = self.temporary("result");
        let closed = self.temporary("closed");
        let body = block(
            vec![
                Statement::Bind {
                    pattern: Pattern::Name(file.clone()),
                    value: call(
                        name("__variant_payload", span),
                        vec![name(&opened, span)],
                        span,
                    ),
                    scoped: true,
                },
                bind(
                    &result,
                    callback_call(name(&action, span), vec![name(&file, span)], span),
                ),
                // Explicit close reports its Result on normal completion. Scoped
                // implicit release handles panic/abort and becomes a no-op here.
                bind(
                    &closed,
                    call(name("File::close", span), vec![name(&file, span)], span),
                ),
            ],
            conditional(
                is_error(&result, span),
                name(&result, span),
                conditional(
                    is_error(&closed, span),
                    name(&closed, span),
                    name(&result, span),
                    span,
                ),
                span,
            ),
            span,
        );
        block(
            vec![
                bind(&path, arguments[0].clone()),
                bind(&mode, arguments[1].clone()),
                bind(&action, arguments[2].clone()),
                bind(
                    &opened,
                    call(
                        name("File::open_path", span),
                        vec![name(&path, span), name(&mode, span)],
                        span,
                    ),
                ),
            ],
            conditional(is_error(&opened, span), name(&opened, span), body, span),
            span,
        )
    }
}
