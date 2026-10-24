//! Actual callable termination queries preserve lexical targets and certified budgets.
use super::*;
fn operation_name(expression: &Expr) -> Option<String> {
    match &expression.kind {
        ExprKind::Name(name) => Some(name.clone()),
        ExprKind::Path(path) => Some(path.join("::")),
        ExprKind::Generic { base, .. } => operation_name(base),
        _ => None,
    }
}
impl Checker {
    pub(super) fn selected_handler_termination(
        &self,
        selected: &BTreeSet<usize>,
        span: Span,
    ) -> (
        crate::termination::Judgment,
        BTreeMap<String, crate::termination::Judgment>,
    ) {
        let mut handlers = BTreeMap::new();
        let mut result = crate::termination::Judgment::default();
        for (lexical, arms) in self.selected_handler_arms(selected) {
            let mut group = BTreeMap::new();
            for arm in arms {
                let expression = Expr {
                    hir_id: None,
                    span: arm.body.span,
                    kind: ExprKind::Lambda {
                        parameters: arm.parameters,
                        return_type: None,
                        annotations: vec![],
                        body: Box::new(arm.body),
                    },
                };
                let judgment = self.expression_termination(&expression, &lexical, span, &handlers);
                result.may_diverge |= judgment.may_diverge;
                result.unresolved |= judgment.unresolved;
                result
                    .callable_parameters
                    .extend(&judgment.callable_parameters);
                if let Some(name) = operation_name(&arm.operation) {
                    group.insert(name, judgment);
                } else {
                    result.unresolved = true;
                }
            }
            handlers.extend(group);
        }
        (result, handlers)
    }
    fn callable_expression(&self, value: &Value, span: Span) -> Option<Expr> {
        if value.callables.len() != 1 {
            return None;
        }
        Some(Expr {
            hir_id: None,
            span,
            kind: match &value.callables[0] {
                Callable::Named(id, _) => ExprKind::Name(self.functions[*id].syntax.name.clone()),
                Callable::Builtin(name) => {
                    ExprKind::Path(name.split("::").map(str::to_owned).collect())
                }
                Callable::Closure(id) => {
                    let closure = &self.closures[*id];
                    ExprKind::Lambda {
                        parameters: closure.parameters.clone(),
                        return_type: None,
                        annotations: vec![],
                        body: Box::new(closure.body.clone()),
                    }
                }
                _ => return None,
            },
        })
    }

    pub(super) fn callable_termination(
        &self,
        callback: &Value,
        span: Span,
        handlers: &BTreeMap<String, crate::termination::Judgment>,
    ) -> crate::termination::Judgment {
        let mut result = crate::termination::Judgment::default();
        if callback.callables.is_empty() {
            result.unresolved = true;
        }
        for target in &callback.callables {
            let mut singleton = callback.clone();
            singleton.callables = vec![target.clone()];
            let Some(mut expression) = self.callable_expression(&singleton, span) else {
                result.unresolved = true;
                continue;
            };
            let lexical = match target {
                Callable::Closure(id) => Some(&self.closures[*id].lexical),
                Callable::Named(id, _) => Some(&self.functions[*id].lexical),
                _ => None,
            };
            if let Callable::Named(id, _) = target
                && let Some(body) = &self.functions[*id].syntax.body
            {
                // Recheck the selected body in its own creation environment;
                // a context-free summary can still contain handled operations.
                expression.kind = ExprKind::Lambda {
                    parameters: self.functions[*id].syntax.parameters.clone(),
                    return_type: self.functions[*id].syntax.return_type.clone(),
                    annotations: vec![],
                    body: Box::new(Expr {
                        hir_id: None,
                        kind: ExprKind::Block(body.clone()),
                        span: body.span,
                    }),
                };
            }
            let judgment = self.expression_termination(
                &expression,
                lexical.unwrap_or(&Env::new()),
                span,
                handlers,
            );
            result.may_diverge |= judgment.may_diverge;
            result.unresolved |= judgment.unresolved;
            result
                .callable_parameters
                .extend(judgment.callable_parameters);
        }
        result
    }

    pub(super) fn expression_termination(
        &self,
        expression: &Expr,
        lexical: &Env,
        span: Span,
        handlers: &BTreeMap<String, crate::termination::Judgment>,
    ) -> crate::termination::Judgment {
        let program = Program {
            statements: self
                .functions
                .iter()
                .map(|info| Stmt {
                    hir_id: None,
                    kind: StmtKind::Function(info.syntax.clone()),
                    span: info.syntax.span,
                })
                .collect(),
        };
        let aliases = lexical
            .iter()
            .filter_map(|(name, binding)| {
                let value = &self.bindings[*binding].value;
                if matches!(value.callables.as_slice(), [Callable::Named(id, _)] if self.functions[*id].syntax.name==*name)
                {
                    return None;
                }
                let compatible_capture=match value.callables.as_slice() {
                    [Callable::Closure(id)]=>self.closures[*id].captures.iter().all(|binding|lexical.get(&self.bindings[*binding].name)==Some(binding)),
                    _=>true,
                };
                let expression=compatible_capture.then(||self.callable_expression(value,span)).flatten().unwrap_or(Expr{ hir_id: None,kind:ExprKind::Error,span});
                Some((name.clone(),expression))
            })
            .collect();
        crate::termination::analyze_expression_with_handlers(
            &program,
            expression,
            &self.budget_proofs,
            aliases,
            handlers.clone(),
        )
    }
}
