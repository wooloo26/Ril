//! Loop result typing is lexical to this Typer/callable, never borrowed from a
//! caller. All source branches are typed; only reachable last values join.
use super::*;

pub(super) struct Frame {
    expected: Option<Ty>,
    context: Option<applications::ResultContext>,
    unit: bool,
    lasts: Vec<Ty>,
}

struct Iteration {
    element: Ty,
    empty: bool,
    diverged: bool,
    source_type: Option<std::sync::Arc<crate::sema::model::SourceTypeWitness>>,
}

impl Typer<'_> {
    pub(super) fn bind_sequence(
        &self,
        patterns: &[Pattern],
        ty: Ty,
        array: bool,
        env: &mut Env,
    ) -> Result<()> {
        let positions = patterns
            .iter()
            .enumerate()
            .filter(|(_, pattern)| matches!(pattern.kind, PatternKind::Rest(_)))
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        if positions.len() > 1 {
            return Err(Failure::Diagnostic(
                "E0347",
                "one sequence permits at most one rest".into(),
            ));
        }
        let rest = positions.first().copied();
        let minimum = patterns.len() - usize::from(rest.is_some());
        let (items, element, length) = match (array, ty) {
            (false, Ty::Tuple(items)) => {
                let length = items.len();
                (items, None, Some(length))
            }
            (false, Ty::Unit) => (vec![], None, Some(0)),
            (true, Ty::Array(element, length)) => (vec![], Some(*element), length),
            (_, Ty::Never) => return Ok(()),
            _ => {
                return Err(Failure::Diagnostic(
                    "E0301",
                    "sequence pattern has an incompatible subject".into(),
                ));
            }
        };
        if length.is_some_and(|length| length < minimum || (rest.is_none() && length != minimum)) {
            return Err(Failure::Diagnostic(
                "E0301",
                "sequence pattern length differs".into(),
            ));
        }
        for (index, pattern) in patterns.iter().enumerate() {
            if let PatternKind::Rest(name) = &pattern.kind {
                if let Some(name) = name {
                    let element = element.clone().ok_or_else(|| {
                        Failure::Diagnostic("E0120", "tuple rest cannot bind a name".into())
                    })?;
                    if name != "_" {
                        self.const_shadows.borrow_mut().insert(name.clone());
                        self.schema_bindings.borrow_mut().insert(name.clone(), None);
                        env.insert(
                            name.clone(),
                            Ty::Array(Box::new(element), length.map(|length| length - minimum)),
                        );
                    }
                }
                continue;
            }
            let selected = if let Some(element) = &element {
                element.clone()
            } else {
                let index = if rest.is_some_and(|rest| index > rest) {
                    items.len() - (patterns.len() - index)
                } else {
                    index
                };
                items[index].clone()
            };
            self.bind(pattern, selected, env)?;
        }
        Ok(())
    }
    pub(super) fn while_let_type(
        &self,
        pattern: &Pattern,
        value: &Expr,
        body: &Block,
        env: &mut Env,
    ) -> Result<Ty> {
        let actual = self.expr(value, env)?;
        let default_scope = bounds::BoundEnvironment::default();
        let schema = self.expression_source_schema(
            value,
            &actual,
            env,
            self.bound_environment.as_deref().unwrap_or(&default_scope),
            0,
        )?;
        self.with_const_shadow_scope(|| {
            let mut child = env.clone();
            self.bind(pattern, actual.clone(), &mut child)?;
            self.bind_source_schema(pattern, schema)?;
            self.loop_body_type(
                body,
                &mut child,
                Some(&Ty::Unit),
                None,
                true,
                self.reachable.get() && actual != Ty::Never,
            )
        })?;
        Ok(if actual == Ty::Never {
            Ty::Never
        } else {
            Ty::Unit
        })
    }
    pub(super) fn with_reachability(
        &self,
        reachable: bool,
        action: impl FnOnce() -> Result<Ty>,
    ) -> Result<Ty> {
        let saved = self.reachable.replace(reachable);
        let result = action();
        self.reachable.set(saved);
        result
    }
    pub(super) fn loop_transfer_type(
        &self,
        operation: ControlOperation,
        value: Option<&Expr>,
        env: &mut Env,
    ) -> Result<Ty> {
        let (unit, expected, context) = self
            .loops
            .borrow()
            .last()
            .map(|frame| (frame.unit, frame.expected.clone(), frame.context.clone()))
            .ok_or_else(|| {
                Failure::Diagnostic(
                    "E0707",
                    "loop control has no enclosing static loop body".into(),
                )
            })?;
        if operation == ControlOperation::Next {
            return Ok(Ty::Never);
        }
        let actual = value.map_or(Ok(Ty::Unit), |value| {
            self.expr_result_expected(value, env, expected.as_ref(), context.as_ref())
        })?;
        if unit {
            require(&actual, &Ty::Unit)?;
        }
        if self.reachable.get() && actual != Ty::Never {
            self.loops
                .borrow_mut()
                .last_mut()
                .expect("lexical loop frame")
                .lasts
                .push(actual);
        }
        Ok(Ty::Never)
    }
    fn loop_body_type(
        &self,
        body: &Block,
        env: &mut Env,
        expected: Option<&Ty>,
        context: Option<&applications::ResultContext>,
        unit: bool,
        reachable: bool,
    ) -> Result<Ty> {
        self.loops.borrow_mut().push(Frame {
            expected: expected.cloned(),
            context: context.cloned(),
            unit,
            lasts: vec![],
        });
        let result = self.with_reachability(reachable, || {
            self.block_expected(body, &mut env.clone(), None)
        });
        let frame = self
            .loops
            .borrow_mut()
            .pop()
            .expect("static loop typing frame");
        result?;
        if unit {
            return Ok(Ty::Unit);
        }
        frame
            .lasts
            .into_iter()
            .try_fold(Ty::Never, |common, ty| join_types(&common, &ty))
    }
    pub(super) fn loop_type(
        &self,
        body: &Block,
        env: &mut Env,
        expected: Option<&Ty>,
        context: Option<&applications::ResultContext>,
    ) -> Result<Ty> {
        self.loop_body_type(body, env, expected, context, false, self.reachable.get())
    }
    pub(super) fn while_type(&self, condition: &Expr, body: &Block, env: &mut Env) -> Result<Ty> {
        let condition_ty = self.expr(condition, env)?;
        require(&condition_ty, &Ty::Bool).map_err(|failure| match failure {
            Failure::Diagnostic(_, why) => Failure::Diagnostic("E0350", why),
            other => other,
        })?;
        self.loop_body_type(
            body,
            env,
            Some(&Ty::Unit),
            None,
            true,
            self.reachable.get()
                && condition_ty != Ty::Never
                && known_bool(condition) != Some(false),
        )?;
        Ok(if condition_ty == Ty::Never {
            Ty::Never
        } else {
            Ty::Unit
        })
    }
    pub(super) fn iteration_type(
        &self,
        iterable: &Expr,
        env: &mut Env,
    ) -> Result<(Ty, bool, bool)> {
        let iteration = self.iteration(iterable, env)?;
        Ok((iteration.element, iteration.empty, iteration.diverged))
    }
    fn iteration(&self, iterable: &Expr, env: &mut Env) -> Result<Iteration> {
        let mut source_type = None;
        let (element, empty, diverged) = if let ExprKind::Range { start, end, .. } = &iterable.kind
        {
            let context = start
                .as_deref()
                .and_then(|start| self.rigid_numeric_peer(start, env))
                .or_else(|| {
                    end.as_deref()
                        .and_then(|end| self.rigid_numeric_peer(end, env))
                });
            let types = start
                .iter()
                .chain(end)
                .map(|value| self.expr_expected(value, env, context.as_ref()))
                .collect::<Result<Vec<_>>>()?;
            let diverged = types.contains(&Ty::Never);
            for ty in &types {
                if !matches!(ty, Ty::Never | Ty::IntegerConstant(_))
                    && !matches!(ty, Ty::Number(name) if matches!(name.as_str(), "int"|"bigint"|"i8"|"i16"|"i32"|"i64"|"u8"|"u16"|"u32"|"u64"))
                {
                    return Err(Failure::Diagnostic(
                        "E0327",
                        "static range endpoints require integers".into(),
                    ));
                }
            }
            let element = types
                .iter()
                .find(|ty| matches!(ty, Ty::Number(_)))
                .cloned()
                .unwrap_or(Ty::Number("int".into()));
            for ty in types {
                require(&ty, &element)?;
            }
            (element, false, diverged)
        } else {
            let actual = self.expr(iterable, env)?;
            if matches!(actual, Ty::Array(..)) {
                let default_scope = bounds::BoundEnvironment::default();
                if let Some(source) = self.expression_source_schema(
                    iterable,
                    &actual,
                    env,
                    self.bound_environment.as_deref().unwrap_or(&default_scope),
                    0,
                )? {
                    source_type = self.evaluator.project_source_schema(
                        &source,
                        &[ril_compiler_core::projection::TypeProjection::Element],
                        iterable.span,
                    )?;
                }
            }
            match actual {
                Ty::Array(element, length) => (*element, length == Some(0), false),
                Ty::Map(key, value) => (Ty::Tuple(vec![*key, *value]), false, false),
                Ty::Never => (Ty::Infer, false, true),
                Ty::Unknown | Ty::Generic(_) => {
                    return Err(Failure::Unsupported(
                        "static for source type is not established".into(),
                    ));
                }
                _ => {
                    return Err(Failure::Diagnostic(
                        "E0355",
                        "static for requires an array, map or integer range".into(),
                    ));
                }
            }
        };
        Ok(Iteration {
            element,
            empty,
            diverged,
            source_type,
        })
    }
    pub(super) fn for_type(
        &self,
        iterable: &Expr,
        pattern: &Pattern,
        body: &Block,
        env: &mut Env,
    ) -> Result<Ty> {
        let Iteration {
            element,
            empty,
            diverged,
            source_type,
        } = self.iteration(iterable, env)?;
        if !irrefutable(pattern, &element) {
            return Err(Failure::Diagnostic(
                "E0345",
                "static for pattern must be irrefutable".into(),
            ));
        }
        let mut child = env.clone();
        self.with_const_shadow_scope(|| {
            self.bind(pattern, element, &mut child)?;
            self.bind_source_schema(pattern, source_type)?;
            self.loop_body_type(
                body,
                &mut child,
                Some(&Ty::Unit),
                None,
                true,
                self.reachable.get() && !empty && !diverged,
            )
        })?;
        Ok(if diverged { Ty::Never } else { Ty::Unit })
    }
}

pub(super) fn known_bool(expr: &Expr) -> Option<bool> {
    match &expr.kind {
        ExprKind::Literal(Literal::Bool(value)) => Some(*value),
        ExprKind::Unary { operator, operand } if operator == "!" => {
            known_bool(operand).map(|value| !value)
        }
        _ => None,
    }
}
fn irrefutable(pattern: &Pattern, ty: &Ty) -> bool {
    match (&pattern.kind, ty) {
        (PatternKind::Name(_) | PatternKind::Wildcard, _) => true,
        (PatternKind::Tuple(patterns), Ty::Tuple(types)) => tuple_irrefutable(patterns, types),
        (PatternKind::Tuple(patterns), Ty::Unit) => tuple_irrefutable(patterns, &[]),
        (PatternKind::Array(patterns), Ty::Array(element, length)) => {
            let Some(rest) = sequence_rest(patterns) else {
                return false;
            };
            let minimum = patterns.len() - usize::from(rest.is_some());
            let enough = match length {
                Some(length) => *length >= minimum && (rest.is_some() || *length == minimum),
                None => rest.is_some() && minimum == 0,
            };
            enough
                && patterns.iter().all(|pattern| {
                    matches!(pattern.kind, PatternKind::Rest(_)) || irrefutable(pattern, element)
                })
        }
        (PatternKind::Record { fields, .. }, Ty::Record(types)) => fields.iter().all(|field| {
            types
                .get(&field.name)
                .is_some_and(|(_, ty)| irrefutable(&field.pattern, ty))
        }),
        (PatternKind::Alternative(patterns), ty) => {
            patterns.iter().any(|pattern| irrefutable(pattern, ty))
        }
        _ => false,
    }
}

/// A rest belongs only to this sequence layer. Nested sequence checks have
/// their own count, while two rests in this layer never prove irrefutability.
fn sequence_rest(patterns: &[Pattern]) -> Option<Option<usize>> {
    let mut rest = None;
    for (index, pattern) in patterns.iter().enumerate() {
        if matches!(pattern.kind, PatternKind::Rest(_)) {
            if rest.is_some() {
                return None;
            }
            rest = Some(index);
        }
    }
    Some(rest)
}

fn tuple_irrefutable(patterns: &[Pattern], types: &[Ty]) -> bool {
    let Some(rest) = sequence_rest(patterns) else {
        return false;
    };
    let minimum = patterns.len() - usize::from(rest.is_some());
    if types.len() < minimum || (rest.is_none() && types.len() != minimum) {
        return false;
    }
    patterns
        .iter()
        .enumerate()
        .all(|(index, pattern)| match &pattern.kind {
            PatternKind::Rest(None) => true,
            PatternKind::Rest(Some(_)) => false,
            _ => {
                let selected = if rest.is_some_and(|rest| index > rest) {
                    types.len() - (patterns.len() - index)
                } else {
                    index
                };
                irrefutable(pattern, &types[selected])
            }
        })
}
