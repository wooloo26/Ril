//! Explicit state transitions are ordinary callable values. No suspended
//! continuation is stored in a Source, and successor writes follow a real call.
use super::*;

const DONE: &str = "Iter::Step::Done";
const YIELDED: &str = "Iter::Step::Yielded";
const DONE_VALUE: &str = "\0ril.iter.Done";
const YIELDED_VALUE: &str = "\0ril.iter.Yielded";

fn field(base: Expr, label: &str, span: Span) -> Expr {
    expr(
        ExprKind::Field {
            base: Box::new(base),
            field: label.into(),
            safe: false,
        },
        span,
    )
}
fn tuple(items: Vec<Expr>, span: Span) -> Expr {
    expr(ExprKind::Tuple(items), span)
}
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
fn record(fields: Vec<(&str, Expr)>, span: Span) -> Expr {
    expr(
        ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|(label, value)| (label.into(), value))
                .collect(),
            spread: None,
            members: vec![],
        },
        span,
    )
}
fn is_done(value: &str, span: Span) -> Expr {
    expr(
        ExprKind::Is {
            value: Box::new(name(value, span)),
            pattern: Pattern::Constructor {
                tag: DONE.into(),
                arguments: vec![],
            },
        },
        span,
    )
}
fn yielded(item: Expr, state: Expr, span: Span) -> Expr {
    call(name(YIELDED_VALUE, span), vec![item, state], span)
}
fn unpack(value: &str, item: &str, successor: &str, span: Span) -> Statement {
    Statement::Bind {
        pattern: Pattern::Constructor {
            tag: YIELDED.into(),
            arguments: vec![Pattern::Tuple(vec![
                Pattern::Name(item.into()),
                Pattern::Name(successor.into()),
            ])],
        },
        value: name(value, span),
        scoped: false,
    }
}
fn panic(message: &str, span: Span) -> Expr {
    call(
        name("Prelude::panic", span),
        vec![expr(
            ExprKind::Literal(core::Literal::String(message.into())),
            span,
        )],
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
fn transition(source: &str, state: Expr, span: Span) -> Expr {
    callback_call(field(name(source, span), "step", span), vec![state], span)
}
fn iteration(statements: Vec<Statement>, span: Span) -> Expr {
    let mut body = vec![statement(expr(
        ExprKind::Charge(core::ChargeEvent::LoopIteration),
        span,
    ))];
    body.extend(statements);
    expr(
        ExprKind::Loop {
            body: core::Block { statements: body },
            charge: None,
        },
        span,
    )
}
fn source(parameter: &str, body: Expr, span: Span) -> Expr {
    record(
        vec![(
            "step",
            expr(
                ExprKind::Lambda {
                    parameters: vec![core::Parameter {
                        pattern: Pattern::Name(parameter.into()),
                        default: None,
                    }],
                    body: Box::new(body),
                },
                span,
            ),
        )],
        span,
    )
}

impl Lower {
    pub(super) fn iter(&mut self, operation: &str, arguments: &[Expr], span: Span) -> Expr {
        for (name, tag, has_payload) in [(DONE_VALUE, DONE, false), (YIELDED_VALUE, YIELDED, true)]
        {
            self.constructors
                .entry(name.into())
                .or_insert_with(|| core::Constructor {
                    name: name.into(),
                    tag: tag.into(),
                    nominal: false,
                    has_payload,
                    span,
                });
        }
        match operation {
            "Iter::cursor" => record(
                vec![
                    ("state", arguments[0].clone()),
                    ("ended", boolean(false, span)),
                ],
                span,
            ),
            "Iter::indexed" => self.indexed(&arguments[0], span),
            "Iter::pull" => self.pull(arguments, span),
            "Iter::collect" | "Iter::fold" => self.traverse(operation, arguments, span),
            "Iter::take" => self.take(arguments, span),
            "Iter::map" | "Iter::filter" => self.adapt(operation, arguments, span),
            _ => unreachable!("exact Iter operation registry"),
        }
    }
    fn indexed(&mut self, items: &Expr, span: Span) -> Expr {
        let retained = self.temporary("items");
        let state = self.temporary("state");
        let element = expr(
            ExprKind::Index {
                base: Box::new(name(&retained, span)),
                index: Box::new(name(&state, span)),
                safe: false,
            },
            span,
        );
        let body = conditional(
            binary("<", name(&state, span), integer(0, span), span),
            panic("negative index", span),
            conditional(
                binary(
                    "<",
                    name(&state, span),
                    call(
                        name("Prelude::len", span),
                        vec![name(&retained, span)],
                        span,
                    ),
                    span,
                ),
                yielded(
                    element,
                    binary("+", name(&state, span), integer(1, span), span),
                    span,
                ),
                name(DONE_VALUE, span),
                span,
            ),
            span,
        );
        block(
            vec![bind(&retained, items.clone())],
            source(&state, body, span),
            span,
        )
    }
    fn pull(&mut self, arguments: &[Expr], span: Span) -> Expr {
        let cursor = self.temporary("cursor");
        let retained = self.temporary("source");
        let result = self.temporary("transition");
        let item = self.temporary("item");
        let successor = self.temporary("successor");
        let assign_field = |label: &str, value| Statement::Assign {
            target: field(name(&cursor, span), label, span),
            operator: "=".into(),
            value,
        };
        let body = block(
            vec![bind(
                &result,
                transition(&retained, field(name(&cursor, span), "state", span), span),
            )],
            conditional(
                is_done(&result, span),
                block(
                    vec![assign_field("ended", boolean(true, span))],
                    name("Prelude::None", span),
                    span,
                ),
                block(
                    vec![
                        unpack(&result, &item, &successor, span),
                        assign_field("state", name(&successor, span)),
                    ],
                    call(name("Prelude::Some", span), vec![name(&item, span)], span),
                    span,
                ),
                span,
            ),
            span,
        );
        block(
            vec![
                bind(&cursor, arguments[0].clone()),
                bind(&retained, arguments[1].clone()),
            ],
            conditional(
                field(name(&cursor, span), "ended", span),
                name("Prelude::None", span),
                body,
                span,
            ),
            span,
        )
    }
    fn traverse(&mut self, operation: &str, arguments: &[Expr], span: Span) -> Expr {
        let state = self.temporary("state");
        let retained = self.temporary("source");
        let output = self.temporary("output");
        let callback = self.temporary("callback");
        let result = self.temporary("transition");
        let item = self.temporary("item");
        let successor = self.temporary("successor");
        let fold = operation == "Iter::fold";
        let mut setup = vec![
            bind(&state, arguments[0].clone()),
            bind(&retained, arguments[1].clone()),
        ];
        if fold {
            setup.extend([
                bind(&output, arguments[2].clone()),
                bind(&callback, arguments[3].clone()),
            ]);
        } else {
            setup.push(bind(&output, expr(ExprKind::Array(vec![]), span)));
        }
        let consume = if fold {
            assign(
                &output,
                callback_call(
                    name(&callback, span),
                    vec![name(&output, span), name(&item, span)],
                    span,
                ),
                span,
            )
        } else {
            statement(call(
                name("Array::push", span),
                vec![name(&output, span), name(&item, span)],
                span,
            ))
        };
        block(
            setup,
            iteration(
                vec![
                    bind(&result, transition(&retained, name(&state, span), span)),
                    statement(conditional(
                        is_done(&result, span),
                        last(name(&output, span), span),
                        unit(span),
                        span,
                    )),
                    unpack(&result, &item, &successor, span),
                    consume,
                    assign(&state, name(&successor, span), span),
                ],
                span,
            ),
            span,
        )
    }
    fn adapt(&mut self, operation: &str, arguments: &[Expr], span: Span) -> Expr {
        let retained = self.temporary("source");
        let callback = self.temporary("callback");
        let state = self.temporary("state");
        let result = self.temporary("transition");
        let item = self.temporary("item");
        let successor = self.temporary("successor");
        let body = if operation == "Iter::map" {
            block(
                vec![bind(
                    &result,
                    transition(&retained, name(&state, span), span),
                )],
                conditional(
                    is_done(&result, span),
                    name(DONE_VALUE, span),
                    block(
                        vec![unpack(&result, &item, &successor, span)],
                        yielded(
                            callback_call(name(&callback, span), vec![name(&item, span)], span),
                            name(&successor, span),
                            span,
                        ),
                        span,
                    ),
                    span,
                ),
                span,
            )
        } else {
            let current = self.temporary("current");
            block(
                vec![bind(&current, name(&state, span))],
                iteration(
                    vec![
                        bind(&result, transition(&retained, name(&current, span), span)),
                        statement(conditional(
                            is_done(&result, span),
                            last(name(DONE_VALUE, span), span),
                            unit(span),
                            span,
                        )),
                        unpack(&result, &item, &successor, span),
                        statement(conditional(
                            callback_call(name(&callback, span), vec![name(&item, span)], span),
                            last(
                                yielded(name(&item, span), name(&successor, span), span),
                                span,
                            ),
                            unit(span),
                            span,
                        )),
                        assign(&current, name(&successor, span), span),
                    ],
                    span,
                ),
                span,
            )
        };
        block(
            vec![
                bind(&retained, arguments[0].clone()),
                bind(&callback, arguments[1].clone()),
            ],
            source(&state, body, span),
            span,
        )
    }
    fn take(&mut self, arguments: &[Expr], span: Span) -> Expr {
        let retained = self.temporary("source");
        let count = self.temporary("count");
        let state = self.temporary("state");
        let source_state = self.temporary("source-state");
        let consumed = self.temporary("consumed");
        let result = self.temporary("transition");
        let item = self.temporary("item");
        let successor = self.temporary("successor");
        let body = block(
            vec![Statement::Bind {
                pattern: Pattern::Tuple(vec![
                    Pattern::Name(source_state.clone()),
                    Pattern::Name(consumed.clone()),
                ]),
                value: name(&state, span),
                scoped: false,
            }],
            conditional(
                binary(
                    "||",
                    binary("<", name(&consumed, span), integer(0, span), span),
                    binary(">", name(&consumed, span), name(&count, span), span),
                    span,
                ),
                panic("take consumed count is outside its valid range", span),
                conditional(
                    binary("==", name(&consumed, span), name(&count, span), span),
                    name(DONE_VALUE, span),
                    block(
                        vec![bind(
                            &result,
                            transition(&retained, name(&source_state, span), span),
                        )],
                        conditional(
                            is_done(&result, span),
                            name(DONE_VALUE, span),
                            block(
                                vec![unpack(&result, &item, &successor, span)],
                                yielded(
                                    name(&item, span),
                                    tuple(
                                        vec![
                                            name(&successor, span),
                                            binary(
                                                "+",
                                                name(&consumed, span),
                                                integer(1, span),
                                                span,
                                            ),
                                        ],
                                        span,
                                    ),
                                    span,
                                ),
                                span,
                            ),
                            span,
                        ),
                        span,
                    ),
                    span,
                ),
                span,
            ),
            span,
        );
        block(
            vec![
                bind(&retained, arguments[0].clone()),
                bind(&count, arguments[1].clone()),
                statement(conditional(
                    binary("<", name(&count, span), integer(0, span), span),
                    panic("negative take count", span),
                    unit(span),
                    span,
                )),
            ],
            source(&state, body, span),
            span,
        )
    }
}
