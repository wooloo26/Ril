//! Heap comparisons are real Core callback calls. The private transaction keeps
//! native heap storage opaque and commits only after every comparison succeeds.
use super::*;

fn internal(operation: &str, arguments: Vec<Expr>, span: Span) -> Expr {
    call(
        name(&format!("\0ril.heap.{operation}"), span),
        arguments,
        span,
    )
}
fn tuple_field(value: &str, field: &str, span: Span) -> Expr {
    expr(
        ExprKind::Field {
            base: Box::new(name(value, span)),
            field: field.into(),
            safe: false,
        },
        span,
    )
}
impl Lower {
    pub(super) fn heap(&mut self, operation: &str, arguments: &[Expr], span: Span) -> Expr {
        if operation == "Heap::new" {
            return internal("new", arguments.to_vec(), span);
        }
        let transaction = self.temporary("heap_transaction");
        let pending = self.temporary("heap_pending");
        let comparison = self.temporary("heap_comparison");
        let answer = self.temporary("heap_answer");
        let request = || internal("next", vec![name(&transaction, span)], span);
        let body = core::Block {
            statements: vec![
                bind(
                    &comparison,
                    call(
                        name("__variant_payload", span),
                        vec![name(&pending, span)],
                        span,
                    ),
                ),
                bind(
                    &answer,
                    callback_call(
                        tuple_field(&comparison, "0", span),
                        vec![
                            tuple_field(&comparison, "1", span),
                            tuple_field(&comparison, "2", span),
                        ],
                        span,
                    ),
                ),
                statement(internal(
                    "accept",
                    vec![name(&transaction, span), name(&answer, span)],
                    span,
                )),
                assign(&pending, request(), span),
            ],
        };
        block(
            vec![
                bind(
                    &transaction,
                    internal(
                        if operation == "Heap::push" {
                            "begin_push"
                        } else {
                            "begin_pop"
                        },
                        arguments.to_vec(),
                        span,
                    ),
                ),
                bind(&pending, request()),
                statement(expr(
                    ExprKind::While {
                        charge: None,
                        condition: Box::new(expr(
                            ExprKind::Is {
                                value: Box::new(name(&pending, span)),
                                pattern: Pattern::Constructor {
                                    tag: "Prelude::Some".into(),
                                    arguments: vec![],
                                },
                            },
                            span,
                        )),
                        body,
                    },
                    span,
                )),
            ],
            internal("commit", vec![name(&transaction, span)], span),
            span,
        )
    }
}
