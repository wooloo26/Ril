//! Type-producing tail applications retain their caller environment explicitly.
use super::*;

pub(super) struct TailType {
    pub syntax: TypeExpr,
    pub environment: environments::Environment,
}

impl Evaluator {
    pub(super) fn invoke_type(
        &mut self,
        syntax: &TypeExpr,
        seen: &mut Vec<String>,
    ) -> Result<TypeExpr> {
        let saved = self.capture_environment()?;
        let saved_returns = self.tail_returns;
        let saved_types = self.tail_types;
        let saved_numeric_return = self.numeric_return.take();
        // Written arguments still evaluate in their caller's lexical loop.
        // Parameter defaults and the selected type body install no caller loop.
        let saved_loops = self.loop_frames.clone();
        let mut entered = Vec::new();
        let result = self.invoke_type_loop(syntax.clone(), seen, &mut entered);
        for key in entered {
            self.type_calls.remove(&key);
        }
        self.install_environment(saved);
        self.tail_returns = saved_returns;
        self.tail_types = saved_types;
        self.numeric_return = saved_numeric_return;
        self.loop_frames = saved_loops;
        match result {
            Err(Failure::Loop(transfer))
                if self
                    .loop_frames
                    .iter()
                    .any(|frame| frame.target == transfer.target) =>
            {
                Err(Failure::Loop(transfer))
            }
            Err(Failure::Loop(_)) => Err(Failure::Diagnostic(
                "E0707",
                "loop control cannot cross a type callable boundary".into(),
            )),
            other => other,
        }
    }

    fn invoke_type_loop(
        &mut self,
        mut syntax: TypeExpr,
        seen: &mut Vec<String>,
        entered: &mut Vec<types::TypeInstanceKey>,
    ) -> Result<TypeExpr> {
        loop {
            self.charge()?;
            let Some((declaration, arguments)) = self.type_tail_target(&syntax) else {
                return self.resolve_type(&syntax, seen);
            };
            let Some(TypeExpr {
                kind: TypeKind::TypeFunction { parameters, body },
                ..
            }) = &declaration.value
            else {
                return Err(Failure::Unsupported(
                    "static type callable body is unavailable".into(),
                ));
            };
            let environment = self.function_environments.get(&declaration.name).copied();
            let actual = self.bind_type_arguments(parameters, &arguments, &declaration.name)?;
            self.loop_frames.clear();
            self.budget.event(budget::Event::TypeFunctionEntry)?;
            let key = types::TypeInstanceKey::new(declaration.name, environment, &actual);
            if !self.type_calls.insert(key.clone()) {
                return Err(Failure::Diagnostic(
                    "E0811",
                    "type evaluation revisited an identical pure application".into(),
                ));
            }
            entered.push(key);
            self.tail_returns = true;
            self.tail_types = true;
            let result = match self.expression_mode(body, true) {
                Err(Failure::TailCall(next)) => {
                    self.result_site = Some(next.site);
                    self.invoke_static(next.callable, next.arguments)
                }
                other => other,
            };
            let result = match result {
                Err(Failure::Return(value)) => Ok(*value),
                other => other,
            };
            match result {
                Err(Failure::TailType(next)) => {
                    self.install_environment(next.environment);
                    syntax = next.syntax;
                }
                Ok(StaticValue::Type(ty)) => {
                    return Ok(ty);
                }
                Ok(_) => {
                    return Err(Failure::Diagnostic(
                        "E0812",
                        "type function must return a type value".into(),
                    ));
                }
                Err(failure) => return Err(failure),
            }
        }
    }

    fn type_tail_target(&self, syntax: &TypeExpr) -> Option<(TypeDeclaration, Vec<TypeExpr>)> {
        let TypeKind::Name { path, arguments } = &syntax.kind else {
            return None;
        };
        let full = path.join("::");
        let name = full.strip_prefix("Prelude::").unwrap_or(&full);
        if self.values.contains_key(&full) {
            return None;
        }
        let declaration = self.declarations.get(&full).or_else(|| {
            (full == name)
                .then(|| self.declarations.get(name))
                .flatten()
        })?;
        matches!(
            declaration.value.as_ref().map(|value| &value.kind),
            Some(TypeKind::TypeFunction { .. })
        )
        .then(|| (declaration.clone(), arguments.clone()))
    }
}
