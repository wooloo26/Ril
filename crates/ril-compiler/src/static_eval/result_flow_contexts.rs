//! Written receiving contexts select types before evaluating an argument.
//! They contain no Result producer, object, tag or permission evidence.
use super::*;

pub(super) struct PreparedInvocation {
    pub(super) name: String,
    pub(super) owner: u32,
    pub(super) caller: BoundScope,
    pub(super) scope: BoundScope,
    pub(super) contextual_types: Vec<Ty>,
}

#[derive(Clone, Copy, Default)]
pub(super) struct CallContext<'a> {
    pub(super) result: Option<&'a ResultContext>,
    pub(super) prepared: Option<&'a PreparedInvocation>,
}

impl Engine<'_> {
    pub(super) fn annotation_context(
        &self,
        syntax: Option<&TypeExpr>,
        state: &State,
    ) -> std::result::Result<Option<ResultContext>, Problem> {
        let mut lexical = state.bound_scope.as_ref().clone();
        lexical.values = Self::types(state);
        syntax
            .map(|syntax| {
                at(
                    self.metadata_typer(state).result_context(syntax, &lexical),
                    syntax.span,
                )
            })
            .transpose()
    }

    pub(super) fn callable_return_context(
        &self,
        syntax: Option<&TypeExpr>,
        parameters: &[Parameter],
        state: &State,
    ) -> std::result::Result<Option<ResultContext>, Problem> {
        let Some(syntax) = syntax else {
            return Ok(None);
        };
        let lexical = self.formal_context_scope(parameters, state)?;
        at(
            self.metadata_typer(state).result_context(syntax, &lexical),
            syntax.span,
        )
        .map(Some)
    }

    fn formal_context_scope(
        &self,
        parameters: &[Parameter],
        state: &State,
    ) -> std::result::Result<bounds::BoundEnvironment, Problem> {
        let mut lexical = state.bound_scope.as_ref().clone();
        lexical.values = Self::types(state);
        // Signature annotations belong to the formal namespace even before the
        // values are bound. A captured same-spelled constant supplies no fact
        // about this parameter, and actual arguments cannot prove the body.
        for parameter in parameters {
            let mut names = BTreeSet::new();
            application::binding_names(&parameter.pattern, &mut names);
            at(
                self.metadata_typer(state)
                    .mask_const_values(&mut lexical, &names),
                parameter.span,
            )?;
            for name in names {
                lexical.values.insert(name, Ty::Unknown);
            }
        }
        let typer = self.metadata_typer(state);
        for parameter in parameters {
            let ty = parameter
                .ty
                .as_ref()
                .map_or(Ok(Ty::Unknown), |syntax| typer.bound_type(syntax, &lexical));
            let ty = at(ty, parameter.span)?;
            at(
                typer.bind(&parameter.pattern, ty, &mut lexical.values),
                parameter.span,
            )?;
        }
        Ok(lexical)
    }

    pub(super) fn project_context(
        &self,
        context: Option<&ResultContext>,
        projection: applications::ResultProjection,
        state: &State,
        span: Span,
    ) -> std::result::Result<Option<ResultContext>, Problem> {
        context
            .map(|context| {
                at(
                    self.metadata_typer(state)
                        .project_result_context(context, projection),
                    span,
                )
            })
            .transpose()
            .map(Option::flatten)
    }

    pub(super) fn with_return_context<T>(
        &mut self,
        context: Option<ResultContext>,
        action: impl FnOnce(&mut Self) -> std::result::Result<T, Problem>,
    ) -> std::result::Result<T, Problem> {
        let saved = std::mem::replace(&mut self.return_context, context);
        let result = action(self);
        self.return_context = saved;
        result
    }

    /// Reserve the actual activation before argument evaluation. Both its
    /// formal contexts and invocation use this one selected scope, rather
    /// than independently inventing binder identities from the source span.
    pub(super) fn prepare_contextual_call(
        &mut self,
        callable: &Callable,
        syntax: &[Argument],
        state: &State,
        context: Option<&ResultContext>,
        span: Span,
    ) -> std::result::Result<Option<PreparedInvocation>, Problem> {
        let Callable::Named {
            name,
            explicit,
            explicit_scope,
        } = callable
        else {
            return Ok(None);
        };
        if !self.global_functions.contains(name) {
            return Err(incomplete(
                span,
                "static Result local named capture requires its lexical group transfer proof",
            ));
        }
        if explicit_scope
            .as_ref()
            .is_some_and(|scope| !Arc::ptr_eq(scope, &state.bound_scope))
        {
            return Err(incomplete(
                span,
                "escaping symbolic static type arguments require their captured binder substitution",
            ));
        }
        let function = self
            .evaluator
            .functions
            .get(name)
            .cloned()
            .ok_or_else(|| incomplete(span, "static Result named declaration absent"))?;
        let owner = self.owner(span)?;
        let (scope, contextual_types) = at(
            self.metadata_typer(state).named_application_scope_at(
                &function,
                explicit,
                syntax,
                &mut Self::types(state),
                applications::ExpectedResult {
                    ordinary: context.map(ResultContext::ordinary),
                    source: context,
                },
                u64::from(owner),
            ),
            span,
        )?;
        Ok(Some(PreparedInvocation {
            name: name.clone(),
            owner,
            caller: state.bound_scope.clone(),
            scope: Arc::new(scope),
            contextual_types,
        }))
    }

    pub(super) fn argument_contexts(
        &self,
        callable: &Callable,
        syntax: &[Argument],
        state: &State,
        prepared: Option<&PreparedInvocation>,
        context: Option<&ResultContext>,
        span: Span,
    ) -> std::result::Result<Vec<Option<ResultContext>>, Problem> {
        let mut contexts = vec![None; syntax.len()];
        if let (Callable::Named { name, .. }, Some(prepared)) = (callable, prepared) {
            let function = self
                .evaluator
                .functions
                .get(name)
                .ok_or_else(|| incomplete(span, "static Result named declaration absent"))?;
            let mut callee_state = state.clone();
            callee_state.bound_scope = prepared.scope.clone();
            callee_state.env = state.globals.clone();
            let formal_scope = self.formal_context_scope(&function.parameters, &callee_state)?;
            let specs = function
                .parameters
                .iter()
                .map(application::ParameterSpec::from)
                .collect::<Vec<_>>();
            let plan = at(
                application::StaticApplicationPlan::new(
                    &specs,
                    syntax.iter().map(|argument| argument.label.clone()),
                ),
                span,
            )?;
            for (parameter, slot) in function.parameters.iter().zip(plan.slots) {
                if let (Some(written), application::ArgumentSlot::Explicit(index)) =
                    (&parameter.ty, slot)
                {
                    contexts[index] = Some(at(
                        self.metadata_typer(&callee_state)
                            .result_context(written, &formal_scope),
                        parameter.span,
                    )?);
                }
            }
        } else if let Callable::Builtin(name) = callable {
            let projection = match name.as_str() {
                "Some" => Some(applications::ResultProjection::OptionalPayload),
                "Ok" => Some(applications::ResultProjection::ResultOk),
                "Err" => Some(applications::ResultProjection::ResultError),
                _ => None,
            };
            if let Some(projection) = projection {
                let payload = self.project_context(context, projection, state, span)?;
                if syntax.len() == 1 {
                    contexts[0] = payload;
                } else {
                    for (index, context) in contexts.iter_mut().enumerate() {
                        *context = self.project_context(
                            payload.as_ref(),
                            applications::ResultProjection::Tuple(index),
                            state,
                            span,
                        )?;
                    }
                }
            }
        }
        Ok(contexts)
    }
}
