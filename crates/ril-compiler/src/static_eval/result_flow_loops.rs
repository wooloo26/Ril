//! Universal loop exits over immutable, exact collections. Repeated complete
//! abstract states close a control-flow cycle; actual evaluation never supplies
//! a Result inspection or an assumption about an unused function's arguments.
use super::*;
use std::collections::VecDeque;

const MAX_LOOP_STATES: usize = 512;
type Sources = (Vec<(State, Cursor)>, Vec<Path>);

pub(super) fn invalid_transfer(span: Span) -> Problem {
    Problem {
        failure: Box::new(Failure::Diagnostic(
            "E0707",
            "loop control cannot leave its enclosing static callable".into(),
        )),
        span,
        producer: None,
    }
}

pub(super) fn integer_value(value: &StaticValue) -> Option<i128> {
    match value {
        StaticValue::Integer(value) | StaticValue::TypedInteger(value, ..) => Some(*value),
        StaticValue::BigInteger(value) => num_traits::ToPrimitive::to_i128(value),
        _ => None,
    }
}

enum Cursor {
    Items(std::vec::IntoIter<Value>),
    Range {
        current: i128,
        end: i128,
        inclusive: bool,
        ty: Ty,
        done: bool,
    },
}
impl Cursor {
    fn next(&mut self, span: Span) -> std::result::Result<Option<Value>, Problem> {
        match self {
            Self::Items(items) => Ok(items.next()),
            Self::Range {
                current,
                end,
                inclusive,
                ty,
                done,
            } => {
                if *done || *current > *end || (!*inclusive && *current == *end) {
                    return Ok(None);
                }
                let value = Value {
                    source_type: None,
                    ty: ty.clone(),
                    shape: Shape::Integer(*current),
                };
                if *current == *end || current.checked_add(1) == Some(*end) && !*inclusive {
                    *done = true;
                } else {
                    *current = current.checked_add(1).ok_or_else(|| {
                        incomplete(
                            span,
                            "static Result range exceeds its exact integer proof carrier",
                        )
                    })?;
                }
                Ok(Some(value))
            }
        }
    }
}

impl Engine<'_> {
    pub(super) fn integer_literal(
        &self,
        text: &str,
        negative: bool,
        span: Span,
    ) -> std::result::Result<Value, Problem> {
        use crate::numeric_literals::{ExactLiteral, ParseLimit};
        let exact = at(
            ExactLiteral::integer(
                text,
                negative,
                ParseLimit {
                    max_bytes: 1_048_576,
                },
            )
            .map_err(numeric_contexts::failure),
            span,
        )?;
        if exact.written_type().is_some() {
            let selected = at(
                numeric_contexts::selected(text, false, negative, None, self.evaluator.layout),
                span,
            )?;
            return Ok(Value {
                source_type: None,
                ty: value_ty(&selected),
                shape: integer_value(&selected).map_or(Shape::Plain, Shape::Integer),
            });
        }
        // This is a mathematical value fact, not a semantic selection. A peer,
        // annotation or return context may still select a wider integer or IEEE
        // type. Ordinary typing owns range checks; this proof may not default
        // the hole to target int before that context is available.
        let value = exact.magnitude().and_then(|magnitude| {
            let sign = if negative {
                num_bigint::Sign::Minus
            } else {
                num_bigint::Sign::Plus
            };
            num_traits::ToPrimitive::to_i128(&num_bigint::BigInt::from_biguint(
                sign,
                magnitude.clone(),
            ))
        });
        Ok(Value {
            source_type: None,
            ty: value.map_or(Ty::Infer, Ty::IntegerConstant),
            shape: value.map_or(Shape::Plain, Shape::Integer),
        })
    }

    pub(super) fn without_loop_targets<T>(
        &mut self,
        action: impl FnOnce(&mut Self) -> std::result::Result<T, Problem>,
    ) -> std::result::Result<T, Problem> {
        let saved = std::mem::take(&mut self.loop_targets);
        let result = action(self);
        self.loop_targets = saved;
        result
    }

    fn loop_target(&mut self, span: Span) -> std::result::Result<u32, Problem> {
        let target = self.next_loop;
        self.next_loop = target
            .checked_add(1)
            .ok_or_else(|| incomplete(span, "static Result loop identity limit"))?;
        Ok(target)
    }

    pub(super) fn loop_transfer(
        &mut self,
        operation: ControlOperation,
        value: Option<&Expr>,
        state: State,
        span: Span,
    ) -> Paths {
        let (target, context) = self
            .loop_targets
            .last()
            .cloned()
            .ok_or_else(|| invalid_transfer(span))?;
        let mut paths = if let Some(value) = value {
            self.expr_expected(
                value,
                state,
                if operation == ControlOperation::Last {
                    context.as_ref()
                } else {
                    None
                },
            )?
        } else {
            vec![Path::normal(state, Value::unit())]
        };
        for path in &mut paths {
            if path.exit == Exit::Normal {
                path.exit = if operation == ControlOperation::Next {
                    Exit::Next(target)
                } else {
                    Exit::Last(target)
                };
            }
        }
        Ok(paths)
    }

    fn loop_body(
        &mut self,
        body: &Block,
        mut state: State,
        target: u32,
        element: Option<(&Pattern, &Value)>,
        context: Option<&ResultContext>,
    ) -> Paths {
        let env = state.env.clone();
        let scope = state.bound_scope.clone();
        if let Some((pattern, value)) = element {
            self.bind_simple(pattern, value.clone(), &mut state)?;
        }
        // A while condition and a for source belong to the surrounding scope;
        // only this body's transfers select this loop's target.
        self.loop_targets.push((target, context.cloned()));
        let result = self.block(body, state);
        self.loop_targets.pop();
        let mut paths = result?;
        for path in &mut paths {
            path.state.env = env.clone();
            path.state.bound_scope = scope.clone();
        }
        Ok(paths)
    }

    pub(super) fn loop_flow(
        &mut self,
        condition: Option<&Expr>,
        pattern: Option<&Pattern>,
        body: &Block,
        state: State,
        span: Span,
        context: Option<&ResultContext>,
    ) -> Paths {
        let target = self.loop_target(span)?;
        let mut pending = VecDeque::from([state]);
        let mut seen = vec![];
        let mut output = vec![];
        while let Some(state) = pending.pop_front() {
            self.step(span)?;
            if seen.contains(&state) {
                // Every successor and normal exit of this complete state was
                // already visited. An infinite cycle contributes no new exit.
                continue;
            }
            if seen.len() == MAX_LOOP_STATES {
                return Err(incomplete(
                    span,
                    "static Result loop requires a quantified producer invariant",
                ));
            }
            seen.push(state.clone());
            let conditions = if let Some(condition) = condition {
                self.expr(condition, state)?
            } else {
                vec![Path::normal(state, Value::boolean(true))]
            };
            for path in conditions {
                if path.exit != Exit::Normal {
                    output.push(path);
                    continue;
                }
                let env = path.state.env.clone();
                let scope = path.state.bound_scope.clone();
                let decisions = if let Some(pattern) = pattern {
                    self.pattern(pattern, &path.value, path.state)?
                } else {
                    truth_paths(path)
                };
                for (mut state, truth) in decisions {
                    if !truth {
                        if pattern.is_some() {
                            state.env = env.clone();
                            state.bound_scope = scope.clone();
                        }
                        output.push(Path::normal(state, Value::unit()));
                        continue;
                    }
                    for mut path in self.loop_body(body, state, target, None, context)? {
                        if pattern.is_some() {
                            path.state.env = env.clone();
                            path.state.bound_scope = scope.clone();
                        }
                        match path.exit {
                            Exit::Normal => pending.push_back(path.state),
                            Exit::Next(id) if id == target => pending.push_back(path.state),
                            Exit::Last(id) if id == target => {
                                path.exit = Exit::Normal;
                                output.push(path);
                            }
                            _ => output.push(path),
                        }
                    }
                }
            }
        }
        Ok(output)
    }

    pub(super) fn for_flow(
        &mut self,
        iterable: &Expr,
        pattern: &Pattern,
        body: &Block,
        state: State,
        span: Span,
    ) -> Paths {
        let target = self.loop_target(span)?;
        let (sources, mut output) = self.loop_sources(iterable, state)?;
        for (state, mut cursor) in sources {
            let mut continuing = vec![state];
            loop {
                self.step(span)?;
                if continuing.is_empty() {
                    break;
                }
                let Some(element) = cursor.next(iterable.span)? else {
                    output.extend(
                        continuing
                            .into_iter()
                            .map(|state| Path::normal(state, Value::unit())),
                    );
                    break;
                };
                let mut next = vec![];
                for state in continuing {
                    for mut path in
                        self.loop_body(body, state, target, Some((pattern, &element)), None)?
                    {
                        match path.exit {
                            Exit::Normal => next.push(path.state),
                            Exit::Next(id) if id == target => next.push(path.state),
                            Exit::Last(id) if id == target => {
                                path.exit = Exit::Normal;
                                path.value = Value::unit();
                                output.push(path);
                            }
                            _ => output.push(path),
                        }
                    }
                }
                continuing = next;
            }
        }
        Ok(output)
    }

    fn loop_sources(
        &mut self,
        iterable: &Expr,
        state: State,
    ) -> std::result::Result<Sources, Problem> {
        let mut sources = vec![];
        let mut exits = vec![];
        if let ExprKind::Range {
            start: Some(start),
            end: Some(end),
            inclusive,
        } = &iterable.kind
        {
            let (normal, output) = self.operands(vec![start, end], state)?;
            exits.extend(output);
            for (state, values) in normal {
                let [start, end] = values.as_slice() else {
                    unreachable!()
                };
                let (Shape::Integer(current), Shape::Integer(end)) = (&start.shape, &end.shape)
                else {
                    return Err(incomplete(
                        iterable.span,
                        "static Result range requires exact endpoint values",
                    ));
                };
                sources.push((
                    state,
                    Cursor::Range {
                        current: *current,
                        end: *end,
                        inclusive: *inclusive,
                        ty: start.ty.clone(),
                        done: false,
                    },
                ));
            }
        } else {
            for path in self.expr(iterable, state)? {
                if path.exit != Exit::Normal {
                    exits.push(path);
                    continue;
                }
                let values = match path.value.shape {
                    Shape::Array(values) => values,
                    Shape::Map(values) => values
                        .into_iter()
                        .map(|(key, value)| Value {
                            source_type: None,
                            ty: Ty::Tuple(vec![key.ty.clone(), value.ty.clone()]),
                            shape: Shape::Tuple(vec![key, value]),
                        })
                        .collect(),
                    _ => {
                        return Err(incomplete(
                            iterable.span,
                            "static Result for source requires quantified collection coverage",
                        ));
                    }
                };
                sources.push((path.state, Cursor::Items(values.into_iter())));
            }
        }
        Ok((sources, exits))
    }

    pub(super) fn map_expression(
        &mut self,
        items: &[(Expr, Expr)],
        state: State,
        span: Span,
        context: Option<&ResultContext>,
    ) -> Paths {
        let key_context = self.project_context(
            context,
            applications::ResultProjection::MapKey,
            &state,
            span,
        )?;
        let value_context = self.project_context(
            context,
            applications::ResultProjection::MapValue,
            &state,
            span,
        )?;
        let contexts = items
            .iter()
            .flat_map(|_| [key_context.clone(), value_context.clone()])
            .collect::<Vec<_>>();
        let operands = items.iter().flat_map(|(key, value)| [key, value]).collect();
        let (normal, mut output) = self.operands_expected(operands, state, &contexts)?;
        for (state, values) in normal {
            let mut entries: Vec<(Value, Value)> = vec![];
            for pair in values.as_chunks::<2>().0 {
                let mut duplicate = None;
                for (index, (key, _)) in entries.iter().enumerate() {
                    match equal_values(key, &pair[0]) {
                        Some(true) => {
                            duplicate = Some(index);
                            break;
                        }
                        Some(false) => {}
                        None => {
                            return Err(incomplete(
                                span,
                                "static Result map key equality is not established",
                            ));
                        }
                    }
                }
                if let Some(index) = duplicate {
                    // Overwriting does not inspect the displaced producer.
                    entries[index].1 = pair[1].clone();
                } else {
                    entries.push((pair[0].clone(), pair[1].clone()));
                }
            }
            let (key, value) = entries
                .first()
                .map_or((Ty::Infer, Ty::Infer), |(key, value)| {
                    (key.ty.clone(), value.ty.clone())
                });
            output.push(Path::normal(
                state,
                Value {
                    source_type: None,
                    ty: Ty::Map(Box::new(key), Box::new(value)),
                    shape: Shape::Map(entries),
                },
            ));
        }
        Ok(output)
    }
}
