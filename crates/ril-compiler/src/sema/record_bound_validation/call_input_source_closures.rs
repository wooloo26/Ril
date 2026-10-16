//! Rebuild lambda types from real lexical headers and completed body entries.
//! Neither a private cache nor Ty::Callable supplies a missing source schema.
use super::*;
use crate::sema::model::Callable;

impl Replay<'_> {
    pub(super) fn lambda_formal_source_key(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
    ) -> Check<ArgumentKey> {
        let ExprKind::Name(name) = &expression.kind else {
            return Err("lambda formal Source is not a real Name".into());
        };
        require(
            value.sources.len() == 1,
            "lambda formal Source has ambiguous binding roots",
        )?;
        let binding = self
            .facts
            .bindings
            .get(*value.sources.first().unwrap())
            .ok_or_else(|| "lambda formal Source binding is absent".to_owned())?;
        let id = context
            .closure_invocation
            .ok_or_else(|| "lambda formal Source has no actual body entry".to_owned())?;
        let invocation = self
            .facts
            .closure_invocations
            .get(id.0 as usize)
            .filter(|invocation| invocation.id == id)
            .ok_or_else(|| "lambda formal Source entry is absent".to_owned())?;
        let closure = self
            .facts
            .closures
            .get(invocation.closure)
            .ok_or_else(|| "lambda formal Source object is absent".to_owned())?;
        require(
            invocation.activation == Some(binding.owner)
                && binding.parameter
                && binding.name == *name
                && context.closure == Some(invocation.closure)
                && closure.site.map(CallableOwner::Lambda) == context.owner
                && invocation.status == CopyInvocationStatus::Completed,
            "lambda formal Source borrowed another activation or lexical object",
        )?;
        let site = self
            .facts
            .closure_sites
            .iter()
            .find(|site| Some(site.id) == closure.site)
            .ok_or_else(|| "lambda formal Source lost its lexical site".to_owned())?;
        let headers: Vec<_> = sites
            .lambdas
            .iter()
            .filter(|header| header.owner == site.owner && header.expression.span == site.span)
            .collect();
        let [header] = headers.as_slice() else {
            return Err("lambda formal Source header is not unique".into());
        };
        let ExprKind::Lambda { parameters, .. } = &header.expression.kind else {
            unreachable!()
        };
        let parameters:Vec<_>=parameters.iter().filter(|parameter|parameter.pattern.span==binding.span
            &&matches!(&parameter.pattern.kind,ril_syntax::ast::PatternKind::Name(actual) if actual==name)).collect();
        let [parameter] = parameters.as_slice() else {
            return Err("lambda formal Source differs from its actual header".into());
        };
        let key = self.input_callable_source_key(
            parameter.ty.as_ref().ok_or_else(|| {
                "inferred lambda formal needs its actual receiving Source context".to_owned()
            })?,
            &self.lambda_input_scope(site.owner)?,
        )?;
        let selected = closure
            .creation_invocation
            .map(|id| {
                self.facts
                    .copy_invocations
                    .get(id.0 as usize)
                    .ok_or_else(|| "lambda formal creation instance is absent".to_owned())
                    .and_then(|call| self.input_selected_keys(call))
            })
            .transpose()?
            .unwrap_or_default();
        input_select_key(&key, &selected, 0)
    }

    pub(super) fn inferred_lambda_source_key(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
    ) -> Check<Option<ArgumentKey>> {
        let [Callable::Closure(index)] = value.callables.as_slice() else {
            return Ok(None);
        };
        let closure = self
            .facts
            .closures
            .get(*index)
            .ok_or_else(|| "inferred lambda Source object is absent".to_owned())?;
        let site = self
            .facts
            .closure_sites
            .iter()
            .find(|site| Some(site.id) == closure.site)
            .ok_or_else(|| "inferred lambda Source site is absent".to_owned())?;
        let headers: Vec<_> = sites
            .lambdas
            .iter()
            .filter(|header| header.owner == site.owner && header.expression.span == site.span)
            .collect();
        let [header] = headers.as_slice() else {
            return Err("inferred lambda Source header is not unique".into());
        };
        match &expression.kind {
            ExprKind::Lambda { .. } => require(
                expression.span == site.span
                    && context.owner == Some(site.owner)
                    && context.invocation == closure.creation_invocation
                    && context.closure_invocation == closure.creation_closure
                    && context.default_use == closure.creation_default,
                "inferred lambda literal belongs to another creation",
            )?,
            ExprKind::Name(name) => {
                if value.sources.len() != 1 {
                    return Ok(None);
                }
                let id = *value.sources.first().unwrap();
                let binding = self
                    .facts
                    .bindings
                    .get(id)
                    .ok_or_else(|| "inferred lambda Name binding is absent".to_owned())?;
                let declarations: Vec<_> = sites
                    .bindings
                    .iter()
                    .filter(|declaration| {
                        declaration.owner == site.owner
                            && declaration.binding.pattern.span == binding.span
                            && declaration.binding.value.span == site.span
                            && matches!(declaration.binding.value.kind, ExprKind::Lambda { .. })
                    })
                    .collect();
                if declarations.len() != 1
                    || binding.parameter
                    || binding.name != *name
                    || binding.owner != closure.owner
                {
                    return Ok(None);
                }
                if context.owner != Some(site.owner) {
                    let caller = context
                        .closure
                        .and_then(|index| self.facts.closures.get(index))
                        .ok_or_else(|| {
                            "captured lambda Source has no actual capturing object".to_owned()
                        })?;
                    require(
                        caller.lexical.get(name) == Some(&id) && caller.captures.contains(&id),
                        "captured lambda Source borrowed an independent ambient binding",
                    )?;
                }
            }
            _ => return Ok(None),
        }
        let ExprKind::Lambda {
            parameters,
            annotations,
            body,
            ..
        } = &header.expression.kind
        else {
            unreachable!()
        };
        if parameters.iter().any(|parameter| parameter.ty.is_none()) {
            return Ok(None);
        }
        let scope = self.lambda_input_scope(site.owner)?;
        let selected = closure
            .creation_invocation
            .map(|id| {
                self.facts
                    .copy_invocations
                    .get(id.0 as usize)
                    .ok_or_else(|| "inferred lambda creation instance is absent".to_owned())
                    .and_then(|call| self.input_selected_keys(call))
            })
            .transpose()?
            .unwrap_or_default();
        let parameter_headers = parameters;
        let parameters = parameter_headers
            .iter()
            .map(|parameter| {
                Ok((
                    parameter.mode,
                    input_select_key(
                        &self.input_callable_source_key(parameter.ty.as_ref().unwrap(), &scope)?,
                        &selected,
                        0,
                    )?,
                ))
            })
            .collect::<Check<Vec<_>>>()?;
        let mut keys = Vec::new();
        for invocation in self.facts.closure_invocations.iter().filter(|invocation| {
            invocation.closure == *index
                && invocation.probe
                && invocation.site == site.span
                && invocation.parent_named == closure.creation_invocation
                && invocation.parent_closure == closure.creation_closure
                && invocation.source_event.is_none()
                && invocation.status == CopyInvocationStatus::Completed
                && invocation.activation.is_some()
        }) {
            for parameter in parameter_headers {
                let mut names = Vec::new();
                parameter_names(&parameter.pattern, &mut names, &mut 4096)?;
                for (span, name) in names {
                    require(
                        self.facts
                            .bindings
                            .iter()
                            .filter(|binding| {
                                binding.parameter
                                    && Some(binding.owner) == invocation.activation
                                    && binding.span == span
                                    && binding.name == name
                            })
                            .count()
                            == 1,
                        "inferred lambda formal bindings belong to another activation",
                    )?;
                }
            }
            let roots: Vec<_> = self
                .facts
                .invocation_expressions
                .iter()
                .filter_map(|row| {
                    if row.context.owner != Some(CallableOwner::Lambda(site.id))
                        || row.context.closure != Some(*index)
                        || row.context.closure_invocation != Some(invocation.id)
                        || row.context.invocation != invocation.parent_named
                        || row.context.default_use != closure.creation_default
                        || row.context.budget_validation != invocation.budget_validation
                    {
                        return None;
                    }
                    self.facts
                        .expressions
                        .get(row.expression)
                        .filter(|fact| fact.span == body.span)
                        .map(|fact| (row.context, &fact.value))
                })
                .collect();
            let [(body_context, result)] = roots.as_slice() else {
                continue;
            };
            if result.ty == Ty::Never {
                continue;
            }
            let result = self.original_source_key(body, result, *body_context, sites)?;
            let key = ArgumentKey::Callable {
                parameters: parameters.clone(),
                result: Box::new(result),
                annotations: annotations
                    .iter()
                    .map(|annotation| annotation.text.replace(' ', ""))
                    .collect(),
            };
            require(
                source_reception::complete(&key, &mut 4096).is_some(),
                "inferred lambda Source is incomplete",
            )?;
            keys.push(key);
        }
        let Some(first) = keys.first() else {
            return Ok(None);
        };
        require(
            keys.iter().all(|key| key == first),
            "inferred lambda bodies disagree about their Source type",
        )?;
        require(
            self.lambda_public_view_agrees(value, first)?,
            "inferred lambda Source would restore a changed public view",
        )?;
        Ok(Some(first.clone()))
    }

    fn lambda_public_view_agrees(&self, value: &Value, key: &ArgumentKey) -> Check<bool> {
        let ArgumentKey::Callable { annotations, .. } = key else {
            unreachable!()
        };
        if value.callable_bounds.iter().any(|bound| {
            bound
                .annotations
                .iter()
                .map(|annotation| annotation.text.replace(' ', ""))
                .collect::<Vec<_>>()
                != *annotations
        }) {
            return Ok(false);
        }
        for bound in value.callable_returns.iter().filter(|bound| !bound.raw) {
            let mut parameters = value
                .signature
                .clone()
                .ok_or_else(|| "lambda public view has no actual parameters".to_owned())?;
            for parameter in &mut parameters {
                parameter.default = None;
            }
            let syntax = TypeExpr {
                text: String::new(),
                span: bound.span,
                kind: TypeKind::Callable {
                    parameters,
                    result: Some(Box::new(bound.syntax.clone())),
                    annotations: vec![],
                },
            };
            let mut original =
                crate::static_eval::effects::bounded_argument_key(&syntax, &bound.generic_context)
                    .ok_or_else(|| "lambda public view exceeds its source budget".to_owned())?;
            let ArgumentKey::Callable {
                annotations: actual,
                ..
            } = &mut original
            else {
                unreachable!()
            };
            *actual = annotations.clone();
            let mut selected = BTreeMap::new();
            for (identity, witness) in &bound.generic_type_witnesses {
                self.type_binder(identity)?;
                require(
                    witness.validate_closed(),
                    "lambda public view has an invalid complete Type witness",
                )?;
                selected.insert(
                    identity.clone(),
                    crate::static_eval::effects::bounded_argument_key(
                        &witness.syntax,
                        &BTreeMap::new(),
                    )
                    .ok_or_else(|| "lambda public witness exceeds its source budget".to_owned())?,
                );
            }
            for (identity, ty) in &bound.generic_substitutions {
                if selected.contains_key(identity) {
                    continue;
                }
                let key = match ty {
                    Ty::Generic(identity) => {
                        self.type_binder(identity)?;
                        ArgumentKey::Binder {
                            identity: identity.clone(),
                            sort: StaticBinderSort::Type,
                        }
                    }
                    Ty::Unit => ArgumentKey::Tuple(vec![]),
                    Ty::Bool => ArgumentKey::Name {
                        name: "bool".into(),
                        arguments: vec![],
                    },
                    Ty::Str => ArgumentKey::Name {
                        name: "str".into(),
                        arguments: vec![],
                    },
                    Ty::Bytes => ArgumentKey::Name {
                        name: "bytes".into(),
                        arguments: vec![],
                    },
                    Ty::Int(name) | Ty::Float(name) => ArgumentKey::Name {
                        name: name.clone(),
                        arguments: vec![],
                    },
                    _ => return Ok(false),
                };
                selected.insert(identity.clone(), key);
            }
            if input_select_key(&original, &selected, 0)? != *key {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub(in crate::sema::record_bound_validation) fn binding_source_selections(
        &self,
        binding: &crate::sema::model::BindingInfo,
        owner: CallableOwner,
    ) -> Check<BTreeMap<String, ArgumentKey>> {
        let invocation = match owner {
            CallableOwner::Global => return Ok(BTreeMap::new()),
            CallableOwner::Function(definition) => {
                let summaries: Vec<_> = self
                    .facts
                    .invocations
                    .iter()
                    .filter(|summary| {
                        summary.activation == Some(binding.owner)
                            && summary
                                .context
                                .is_some_and(|context| context.owner == Some(owner))
                    })
                    .collect();
                let [summary] = summaries.as_slice() else {
                    return Err(
                        "local Source declaration has no unique actual named activation".into(),
                    );
                };
                let id = summary
                    .context
                    .and_then(|context| context.invocation)
                    .ok_or_else(|| "local Source declaration has no named instance".to_owned())?;
                require(
                    self.facts
                        .copy_invocations
                        .get(id.0 as usize)
                        .is_some_and(|call| call.id == id && call.target == definition),
                    "local Source declaration borrowed another function's activation",
                )?;
                Some(id)
            }
            CallableOwner::Lambda(site) => {
                let calls: Vec<_> = self
                    .facts
                    .closure_invocations
                    .iter()
                    .filter(|call| {
                        call.activation == Some(binding.owner)
                            && self
                                .facts
                                .closures
                                .get(call.closure)
                                .is_some_and(|closure| closure.site == Some(site))
                            && call.status == CopyInvocationStatus::Completed
                    })
                    .collect();
                let [call] = calls.as_slice() else {
                    return Err(
                        "local Source declaration has no unique actual lambda activation".into(),
                    );
                };
                self.facts.closures[call.closure].creation_invocation
            }
        };
        invocation
            .map(|id| {
                self.facts
                    .copy_invocations
                    .get(id.0 as usize)
                    .ok_or_else(|| "local Source declaration instance is absent".to_owned())
                    .and_then(|call| self.input_selected_keys(call))
            })
            .transpose()
            .map(|keys| keys.unwrap_or_default())
    }
}

fn parameter_names(
    pattern: &ril_syntax::ast::Pattern,
    out: &mut Vec<(Span, String)>,
    work: &mut usize,
) -> Check {
    *work = work
        .checked_sub(1)
        .ok_or_else(|| "lambda Source parameter walk exceeds its budget".to_owned())?;
    use ril_syntax::ast::PatternKind;
    match &pattern.kind {
        PatternKind::Name(name) => out.push((pattern.span, name.clone())),
        PatternKind::Mode { pattern, .. } => parameter_names(pattern, out, work)?,
        PatternKind::Tuple(items) => {
            for item in items {
                parameter_names(item, out, work)?;
            }
        }
        PatternKind::Record { fields, .. } => {
            for field in fields {
                parameter_names(&field.pattern, out, work)?;
            }
        }
        PatternKind::Wildcard => {}
        _ => return Err("lambda Source formal pattern has no complete binder proof".into()),
    }
    Ok(())
}
