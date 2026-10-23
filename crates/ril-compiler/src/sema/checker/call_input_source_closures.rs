//! Source views for formal declarations and completed lambda bodies.
//! These type coordinates do not grant publication, loans or callable rows.
use super::*;

impl Checker {
    pub(super) fn formal_source_declaration(
        &self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
    ) -> Option<(TypeExpr, crate::sema::context::FrozenEnvironment)> {
        let ExprKind::Name(name) = &syntax.kind else {
            return None;
        };
        let id = *frame.env.get(name)?;
        if value.sources != BTreeSet::from([id]) {
            return None;
        }
        self.formal_binding_declaration(id, name)
    }

    pub(in crate::sema::checker) fn formal_binding_declaration(
        &self,
        id: BindingId,
        name: &str,
    ) -> Option<(TypeExpr, crate::sema::context::FrozenEnvironment)> {
        let binding = self.bindings.get(id)?;
        if !binding.parameter || binding.name != name {
            return None;
        }
        let pattern = binding.pattern?;
        if let Some(crate::sema::scopes::ScopeRecord {
            origin: crate::sema::scopes::ScopeOrigin::Operation(entry),
            ..
        }) = self.scopes.get(&binding.owner)
        {
            let handler = self.handler_definitions.get(entry.handler)?;
            let arm = handler
                .arms
                .values()
                .find(|arm| arm.body.hir_id == entry.body)?;
            let slot = arm
                .parameters
                .iter()
                .position(|parameter| parameter.pattern.hir_id == Some(pattern))?;
            let operation = self
                .operations
                .values()
                .find(|operation| operation.identity == entry.operation)?;
            let source = operation.source.as_ref()?;
            let syntax = self
                .effects
                .get(&operation.effect)?
                .operations
                .get(source.index as usize)?
                .parameters
                .get(slot)?
                .ty
                .as_ref()?;
            crate::static_eval::effects::bounded_argument_key(syntax, &BTreeMap::new())?;
            return Some((syntax.clone(), binding.typing_environment.clone()));
        }
        let parameters = match binding.context.owner? {
            CallableOwner::Function(definition) => {
                &self
                    .functions
                    .iter()
                    .find(|info| info.definition == definition)?
                    .syntax
                    .parameters
            }
            CallableOwner::Lambda(site) => {
                let invocation = self
                    .closure_invocations
                    .get(binding.context.closure_invocation?.0 as usize)?;
                let closure = self.closures.get(invocation.closure)?;
                if invocation.activation != Some(binding.owner) || closure.site != Some(site) {
                    return None;
                }
                &closure.parameters
            }
            CallableOwner::Global => return None,
        };
        let parameter = parameters.iter().find(|parameter| {
            parameter.pattern.hir_id == Some(pattern)
                && matches!(&parameter.pattern.kind,PatternKind::Name(actual) if actual==name)
        })?;
        let syntax = parameter.ty.as_ref()?;
        // Bound the original header before retaining an owned syntax copy.
        // Its names are interpreted only after entering the captured environment.
        crate::static_eval::effects::bounded_argument_key(syntax, &BTreeMap::new())?;
        Some((syntax.clone(), binding.typing_environment.clone()))
    }

    pub(in crate::sema::checker) fn remember_closure_source(
        &mut self,
        index: usize,
        result: &Value,
        frame: &Frame,
    ) {
        let Some(id) = self.closure_invocation_stack.last().copied() else {
            return;
        };
        let invocation = &self.closure_invocations[id.0 as usize];
        let closure = self.closures[index].clone();
        if !invocation.probe
            || invocation.closure != index
            || invocation.activation != Some(frame.owner)
            || invocation.parent_named != closure.creation_invocation
            || invocation.parent_closure != closure.creation_closure
            || !frame.return_source_valid
        {
            return;
        }
        let context = self.invocation_context(frame.callable_owner);
        let mut work = WorkLimit::new(16384);
        if work.charge(self.application_effect.contexts.len()).is_err() {
            return;
        }
        let mut observations = self
            .application_effect
            .contexts
            .iter()
            .filter(|row| {
                row.context == context
                    && self
                        .application_effect
                        .expressions
                        .get(row.expression)
                        .is_some_and(|fact| {
                            fact.source_id.is_some()
                                && fact.source_id == closure.body.hir_id
                                && self
                                    .application_effect
                                    .evaluations
                                    .get(row.expression)
                                    .is_some_and(|record| record.scope == frame.owner)
                                && fact.value.cause == result.cause
                                && fact.value.ty == result.ty
                        })
            })
            .map(|row| row.expression);
        let Some(observation) = observations.next() else {
            return;
        };
        if observations.next().is_some() {
            return;
        }
        let declaration_environment = closure.contract.typing_environment.clone();
        let composed = (|| -> Result<Option<SourceRef>, SourceTypesError> {
            let Some((result, result_environment)) = self.raw_original_source_schema(
                result,
                &closure.body,
                frame,
                &mut work,
                0,
                Some(observation),
            )?
            else {
                return Ok(None);
            };
            let mut environment = if result.requires_environment(&mut work)? {
                Some(result_environment)
            } else {
                None
            };
            let mut parameters = Vec::new();
            for parameter in &closure.parameters {
                let (schema, parameter_environment) = if let Some(syntax) = parameter.ty.as_ref() {
                    let target = self
                        .with_typing_environment(&declaration_environment, |checker| {
                            checker.freeze_source_receiving_target(syntax)
                        });
                    let Some(schema) = target.schema else {
                        return Ok(None);
                    };
                    (schema, declaration_environment.clone())
                } else {
                    work.charge(frame.locals.len())?;
                    let mut bindings = frame.locals.iter().filter(|&&binding| {
                        self.bindings.get(binding).is_some_and(|info| {
                            info.parameter
                                && info.owner == frame.owner
                                && info.pattern.is_some()
                                && info.pattern == parameter.pattern.hir_id
                        })
                    });
                    let binding = *bindings.next().ok_or(SourceTypesError::MissingNode)?;
                    if bindings.next().is_some() {
                        return Err(SourceTypesError::Unresolved);
                    }
                    let Some(source) =
                        self.parameter_source_schema_if_known(binding, None, &mut work)?
                    else {
                        return Ok(None);
                    };
                    source
                };
                if schema.requires_environment(&mut work)? {
                    if environment
                        .as_ref()
                        .is_some_and(|original| original.id() != parameter_environment.id())
                    {
                        return Err(SourceTypesError::Unresolved);
                    }
                    environment = Some(parameter_environment);
                }
                parameters.push((parameter.mode, schema));
            }
            let contract = self
                .lambda_contract(index)
                .ok_or(SourceTypesError::MissingNode)?;
            work.charge(contract.annotations.len())?;
            let mut annotations = Vec::new();
            for annotation in &contract.annotations {
                work.text(&annotation.text)?;
                annotations.push(annotation.text.replace(' ', ""));
            }
            let schema =
                SourceSchema::callable(&parameters, &result, &annotations, None, &mut work)?;
            if schema.callable_contract_requires_environment(&mut work)?
                && environment
                    .as_ref()
                    .is_some_and(|original| original.id() != contract.typing_environment.id())
            {
                return Err(SourceTypesError::Unresolved);
            }
            let environment = environment.unwrap_or_else(|| contract.typing_environment.clone());
            if environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            Ok(Some(SourceRef::intern(
                &schema,
                environment,
                self.type_source.storage.live_types_mut(),
                &mut work,
            )?))
        })();
        match composed {
            Ok(Some(source)) => {
                self.call_input_source
                    .closure_views
                    .insert(index, (id.0, source));
            }
            Ok(None) => {}
            Err(error) => self.unsupported(
                closure.body.span,
                format!("lambda Source graph composition failed: {error}"),
            ),
        }
    }
    pub(super) fn original_closure_source_schema(
        &mut self,
        value: &Value,
        work: &mut WorkLimit,
    ) -> InputSource {
        let [Callable::Closure(index)] = value.callables.as_slice() else {
            return Ok(None);
        };
        work.charge(
            2 + self
                .call_input_source
                .closure_views
                .len()
                .checked_ilog2()
                .unwrap_or(0) as usize,
        )?;
        let Some((id, source)) = self.call_input_source.closure_views.get(index).copied() else {
            return Ok(None);
        };
        let invocation = self
            .closure_invocations
            .get(id as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        let closure = self
            .closures
            .get(*index)
            .ok_or(SourceTypesError::MissingNode)?;
        if invocation.id.0 != id
            || invocation.closure != *index
            || !invocation.probe
            || invocation.status != crate::sema::copy_contract::CopyInvocationStatus::Completed
            || invocation.parent_named != closure.creation_invocation
            || invocation.parent_closure != closure.creation_closure
        {
            return Err(SourceTypesError::Unresolved);
        }
        let (schema, environment) = self.type_source.storage.live_types().view_schema(
            source.view,
            source.original,
            work,
        )?;
        if self.closure_public_view_agrees(value, &schema, work)? {
            Ok(Some((schema, environment)))
        } else {
            Ok(None)
        }
    }

    fn closure_public_view_agrees(
        &mut self,
        value: &Value,
        schema: &SourceSchema,
        work: &mut WorkLimit,
    ) -> Result<bool, SourceTypesError> {
        let annotations = schema
            .callable_annotations(work)?
            .ok_or(SourceTypesError::Unresolved)?;
        work.charge(value.callable_bounds.len() + value.callable_returns.len())?;
        for bound in &value.callable_bounds {
            work.charge(bound.annotations.len())?;
            let mut actual = Vec::new();
            for annotation in &bound.annotations {
                work.text(&annotation.text)?;
                actual.push(annotation.text.replace(' ', ""));
            }
            if actual != annotations {
                return Ok(false);
            }
        }
        for bound in value.callable_returns.iter().filter(|bound| !bound.raw) {
            if bound.syntax.hir_id.is_none() {
                // A contextual return projection is not another written type.
                // Its actual probe retains the complete original header and
                // exact receiver, so select its result directly from that graph.
                let [Callable::Closure(closure)] = value.callables.as_slice() else {
                    return Err(SourceTypesError::Unresolved);
                };
                let (id, _) = self
                    .call_input_source
                    .closure_views
                    .get(closure)
                    .ok_or(SourceTypesError::MissingNode)?;
                let call = self
                    .closure_invocations
                    .get(*id as usize)
                    .ok_or(SourceTypesError::MissingNode)?;
                let crate::sema::application_effect::EntryOrigin::SignatureProbe(source) =
                    &call.entry.origin
                else {
                    return Err(SourceTypesError::Unresolved);
                };
                if call.closure != *closure
                    || source.environment.id() != bound.typing_environment.id()
                    || !bound.callables.contains(&Callable::Closure(*closure))
                {
                    return Err(SourceTypesError::Unresolved);
                }
                let source = source.clone();
                let root = self.with_typing_environment(&source.environment, |checker| {
                    checker.original_header_source_schema(&source.header, work)
                })?;
                let callable = root.project_steps(&source.path, work)?;
                let (_, expected) = callable
                    .callable_parts(work)?
                    .ok_or(SourceTypesError::MissingProjection)?;
                let (expected, _) =
                    self.selected_input_schema(expected, source.environment.clone(), work)?;
                let (_, actual) = schema
                    .callable_parts(work)?
                    .ok_or(SourceTypesError::MissingProjection)?;
                if !actual.equivalent(&expected, work)? {
                    return Ok(false);
                }
                continue;
            }
            let parameters = schema.callable_parameters(work)?;
            let result = self.with_typing_environment(&bound.typing_environment, |checker| {
                checker.original_header_source_schema(&bound.syntax, work)
            })?;
            let (result, _) =
                self.selected_input_schema(result, bound.typing_environment.clone(), work)?;
            let original = SourceSchema::callable(&parameters, &result, &annotations, None, work)?;
            if !original.equivalent(schema, work)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}
