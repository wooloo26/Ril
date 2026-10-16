//! Loop result typing is lexical to this Typer/callable, never borrowed from a
//! caller. All source branches are typed; only reachable last values join.
use super::*;

pub(super) struct Frame {
    expected: Option<Ty>,
    context: Option<applications::ResultContext>,
    unit: bool,
    lasts: Vec<Ty>,
}

impl Typer<'_> {
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
            match self.expr(iterable, env)? {
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
        Ok((element, empty, diverged))
    }
    pub(super) fn for_type(
        &self,
        iterable: &Expr,
        pattern: &Pattern,
        body: &Block,
        env: &mut Env,
    ) -> Result<Ty> {
        let (element, empty, diverged) = self.iteration_type(iterable, env)?;
        if !irrefutable(pattern, &element) {
            return Err(Failure::Diagnostic(
                "E0345",
                "static for pattern must be irrefutable".into(),
            ));
        }
        let mut child = env.clone();
        self.with_const_shadow_scope(|| {
            self.bind(pattern, element, &mut child)?;
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
        (PatternKind::Tuple(patterns), Ty::Tuple(types)) => {
            patterns.len() == types.len()
                && patterns
                    .iter()
                    .zip(types)
                    .all(|(pattern, ty)| irrefutable(pattern, ty))
        }
        (PatternKind::Record { fields, .. }, Ty::Record(types)) => fields.iter().all(|field| {
            types
                .get(&field.name)
                .is_some_and(|(_, ty)| irrefutable(&field.pattern, ty))
        }),
        _ => false,
    }
}
