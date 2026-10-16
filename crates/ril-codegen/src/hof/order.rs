//! Stable iterative merge sort and lower-bound search. Comparisons remain Core
//! calls so selective CPS can suspend without entering a nested trampoline.
use super::*;

fn binary(operator: &str, left: Expr, right: Expr, span: Span) -> Expr {
    expr(
        ExprKind::Binary {
            operator: operator.into(),
            left: Box::new(left),
            right: Box::new(right),
        },
        span,
    )
}
fn index(array: &str, at: &str, span: Span) -> Expr {
    expr(
        ExprKind::Index {
            base: Box::new(name(array, span)),
            index: Box::new(name(at, span)),
            safe: false,
        },
        span,
    )
}
fn loop_while(condition: Expr, statements: Vec<Statement>, span: Span) -> Statement {
    statement(expr(
        ExprKind::While {
            charge: None,
            condition: Box::new(condition),
            body: core::Block { statements },
        },
        span,
    ))
}
fn increment(target: &str, span: Span) -> Statement {
    assign(
        target,
        binary("+", name(target, span), integer(1, span), span),
        span,
    )
}
fn push(array: &str, value: Expr, span: Span) -> Statement {
    statement(call(
        name("Array::push", span),
        vec![name(array, span), value],
        span,
    ))
}
fn less(left: &str, right: &str, span: Span) -> Expr {
    binary("<", name(left, span), name(right, span), span)
}
fn order_is(value: Expr, ordering: &str, span: Span) -> Expr {
    binary(
        "==",
        value,
        name(&format!("Order::Ordering::{ordering}"), span),
        span,
    )
}
impl Lower {
    pub(super) fn order(&mut self, operation: &str, arguments: &[Expr], span: Span) -> Expr {
        let source = self.temporary("source");
        let target = self.temporary("target");
        let ops = self.temporary("ops");
        let compare = self.temporary("compare");
        let count = self.temporary("count");
        let items = self.temporary("items");
        let cursor = self.temporary("cursor");
        let mut statements = vec![bind(&source, arguments[0].clone())];
        if operation == "Order::binary_search" {
            statements.push(bind(&target, arguments[1].clone()));
        }
        statements.extend([
            bind(&ops, arguments.last().unwrap().clone()),
            bind(
                &compare,
                expr(
                    ExprKind::Field {
                        base: Box::new(name(&ops, span)),
                        field: "compare".into(),
                        safe: false,
                    },
                    span,
                ),
            ),
            bind(
                &count,
                call(name("Prelude::len", span), vec![name(&source, span)], span),
            ),
            bind(&items, expr(ExprKind::Array(vec![]), span)),
            bind(&cursor, integer(0, span)),
            // The runtime contract snapshots element handles before invoking
            // the comparator, preserving aliases without cloning their data.
            loop_while(
                less(&cursor, &count, span),
                vec![
                    push(&items, index(&source, &cursor, span), span),
                    increment(&cursor, span),
                ],
                span,
            ),
        ]);
        let tail = if operation == "Order::sorted" {
            self.merge_sort(&items, &count, &compare, &mut statements, span)
        } else {
            self.search(&items, &count, &target, &compare, &mut statements, span)
        };
        block(statements, tail, span)
    }
    fn merge_sort(
        &mut self,
        items: &str,
        count: &str,
        compare: &str,
        statements: &mut Vec<Statement>,
        span: Span,
    ) -> Expr {
        let width = self.temporary("width");
        let buffer = self.temporary("buffer");
        let start = self.temporary("start");
        let middle = self.temporary("middle");
        let end = self.temporary("end");
        let left = self.temporary("left");
        let right = self.temporary("right");
        statements.push(bind(&width, integer(1, span)));
        let bounded = |from: &str| {
            let sum = binary("+", name(from, span), name(&width, span), span);
            conditional(
                binary(
                    "<",
                    name(&width, span),
                    binary("-", name(count, span), name(from, span), span),
                    span,
                ),
                sum,
                name(count, span),
                span,
            )
        };
        let choose_left = conditional(
            binary("==", name(&left, span), name(&middle, span), span),
            boolean(false, span),
            conditional(
                binary("==", name(&right, span), name(&end, span), span),
                boolean(true, span),
                binary(
                    "!=",
                    callback_call(
                        name(compare, span),
                        vec![index(items, &left, span), index(items, &right, span)],
                        span,
                    ),
                    name("Order::Ordering::Greater", span),
                    span,
                ),
                span,
            ),
            span,
        );
        let merge = loop_while(
            binary(
                "||",
                less(&left, &middle, span),
                less(&right, &end, span),
                span,
            ),
            vec![statement(conditional(
                choose_left,
                block(
                    vec![
                        push(&buffer, index(items, &left, span), span),
                        increment(&left, span),
                    ],
                    unit(span),
                    span,
                ),
                block(
                    vec![
                        push(&buffer, index(items, &right, span), span),
                        increment(&right, span),
                    ],
                    unit(span),
                    span,
                ),
                span,
            ))],
            span,
        );
        let merge_runs = loop_while(
            less(&start, count, span),
            vec![
                bind(&middle, bounded(&start)),
                bind(&end, bounded(&middle)),
                bind(&left, name(&start, span)),
                bind(&right, name(&middle, span)),
                merge,
                assign(&start, name(&end, span), span),
            ],
            span,
        );
        let next_width = conditional(
            binary(
                ">",
                name(&width, span),
                binary("/", name(count, span), integer(2, span), span),
                span,
            ),
            name(count, span),
            binary("*", name(&width, span), integer(2, span), span),
            span,
        );
        statements.push(loop_while(
            less(&width, count, span),
            vec![
                bind(&buffer, expr(ExprKind::Array(vec![]), span)),
                bind(&start, integer(0, span)),
                merge_runs,
                assign(items, name(&buffer, span), span),
                assign(&width, next_width, span),
            ],
            span,
        ));
        name(items, span)
    }
    fn search(
        &mut self,
        items: &str,
        count: &str,
        target: &str,
        compare: &str,
        statements: &mut Vec<Statement>,
        span: Span,
    ) -> Expr {
        let low = self.temporary("low");
        let high = self.temporary("high");
        let middle = self.temporary("middle");
        statements.extend([bind(&low, integer(0, span)), bind(&high, name(count, span))]);
        let at_middle = binary(
            "+",
            name(&low, span),
            binary(
                "/",
                binary("-", name(&high, span), name(&low, span), span),
                integer(2, span),
                span,
            ),
            span,
        );
        let comparison = callback_call(
            name(compare, span),
            vec![index(items, &middle, span), name(target, span)],
            span,
        );
        statements.push(loop_while(
            less(&low, &high, span),
            vec![
                bind(&middle, at_middle),
                statement(conditional(
                    order_is(comparison, "Less", span),
                    block(
                        vec![assign(
                            &low,
                            binary("+", name(&middle, span), integer(1, span), span),
                            span,
                        )],
                        unit(span),
                        span,
                    ),
                    block(
                        vec![assign(&high, name(&middle, span), span)],
                        unit(span),
                        span,
                    ),
                    span,
                )),
            ],
            span,
        ));
        let found = binary(
            "&&",
            less(&low, count, span),
            order_is(
                callback_call(
                    name(compare, span),
                    vec![index(items, &low, span), name(target, span)],
                    span,
                ),
                "Equal",
                span,
            ),
            span,
        );
        conditional(
            found,
            call(name("Prelude::Ok", span), vec![name(&low, span)], span),
            call(name("Prelude::Err", span), vec![name(&low, span)], span),
            span,
        )
    }
}
