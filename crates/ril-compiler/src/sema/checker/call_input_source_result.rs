//! Result Type selection keeps the original declaration's source coordinates.
use super::*;
use crate::hir::application::AstApplication;
use crate::sema::{
    effect_identity::StaticBinderSort,
    record_bounds::BoundScope,
    source_types::{SourceContainer, SourcePath},
};
impl Checker {
    /// Resolve only the actual producing result's flexible leaves before the
    /// immutable observation is recorded. This grants no array shape or mode.
    pub(in crate::sema::checker) fn prepare_producing_result_context(
        &mut self,
        syntax: &Expr,
        value: &mut Value,
        expected: Option<&Ty>,
        source: Option<&source_reception::Target>,
        frame: &Frame,
    ) {
        let Some(expected) = expected else { return };
        self.prepare_original_carrier_context(syntax, value, expected, source, frame);
        if AstApplication::from_ast(syntax).is_none()
            || self.pending_result_binders(value).is_empty()
        {
            return;
        }
        let context = self.invocation_context(frame.callable_owner);
        let calls: Vec<_> = self
            .copy_invocations
            .iter()
            .filter(|call| {
                call.source_event
                    .and_then(|id| self.copy_call_events.get(id.0 as usize))
                    .is_some_and(|event| event.matches_source(syntax))
                    && call.parent == context.invocation
                    && call.caller_owner == context.owner
                    && call.source_event.is_some()
                    && call.result.as_ref().is_some_and(|result| {
                        result.value.cause == value.cause
                            && result.value.ty == value.ty
                            && result.value.pending_inference == value.pending_inference
                    })
            })
            .collect();
        if calls.len() == 1 {
            self.contextual_result_inference(value, expected, syntax.span);
            match self.original_called_result_schema(
                value,
                syntax,
                frame,
                &mut WorkLimit::new(16384),
            ) {
                Ok(Some((schema, _))) => {
                    self.attach_result_graph_witness(&schema, value, syntax.span);
                }
                Ok(None) => {}
                Err(error) => self.unsupported(
                    syntax.span,
                    format!("producing result Source graph is unavailable: {error}"),
                ),
            }
        }
    }

    fn prepare_original_carrier_context(
        &mut self,
        syntax: &Expr,
        value: &mut Value,
        expected: &Ty,
        source: Option<&source_reception::Target>,
        frame: &Frame,
    ) {
        let Some(application) = AstApplication::from_ast(syntax) else {
            return;
        };
        let (callee, arguments) = (application.callee, &application.operands);
        let Some(&(event, context)) = self.call_input_source.carriers.get(&value.cause.0) else {
            return;
        };
        if context != self.invocation_context(frame.callable_owner) || arguments.len() != 1 {
            return;
        }
        let Some(event) = self.copy_call_events.get(event.0 as usize) else {
            return;
        };
        let Some(token) = event.callee_expression else {
            return;
        };
        let Some(callee_fact) = self.application_effect.expressions.get(token) else {
            return;
        };
        if !event.matches_source(syntax)
            || callee_fact.source_id.is_none()
            || callee_fact.source_id != callee.hir_id
            || !callee_fact.value.sources.is_empty()
        {
            return;
        }
        let [Callable::Builtin(name)] = callee_fact.value.callables.as_slice() else {
            return;
        };
        let Some(success) = value.result_tag else {
            return;
        };
        if name.strip_prefix("Prelude::").unwrap_or(name) != if success { "Ok" } else { "Err" } {
            return;
        }
        let (Ty::Result(ok, error), Ty::Result(expected_ok, expected_error)) =
            (&value.ty, expected)
        else {
            return;
        };
        let (active, inactive, expected_inactive) = if success {
            (ok, error, expected_error)
        } else {
            (error, ok, expected_ok)
        };
        if **inactive != Ty::Unknown {
            return;
        }
        let payload = if success {
            value.result_success.as_deref()
        } else {
            value.result_error.as_deref()
        };
        let Some(payload) = payload else { return };
        // The actual physical argument owns the active branch's source graph.
        // A receiving context may select only the branch which did not occur.
        let result = (|| -> InputSource {
            let mut work = WorkLimit::new(16384);
            let input = self
                .call_input_source
                .supplied
                .get(&event.id)
                .and_then(|inputs| inputs.get(&0))
                .ok_or(SourceTypesError::MissingNode)?;
            let token = input.observation.ok_or(SourceTypesError::MissingNode)?;
            let actual = self
                .application_effect
                .expressions
                .get(token)
                .ok_or(SourceTypesError::MissingNode)?;
            if input.context != context
                || actual.source_id.is_none()
                || actual.source_id != arguments[0].expression.hir_id
                || actual.value.cause != payload.cause
                || !self
                    .application_effect
                    .contexts
                    .get(token)
                    .is_some_and(|row| {
                        row.expression == token
                            && row.context == context
                            && row.argument_of == Some((event.id, 0))
                    })
            {
                return Err(SourceTypesError::Unresolved);
            }
            let Some((active_schema, active_environment)) = input.input_source().cloned()? else {
                return Ok(None);
            };
            let inactive = if let Some(target) = source {
                let Some(schema) = &target.schema else {
                    return Ok(None);
                };
                let projection = if success {
                    SourcePath::ResultError
                } else {
                    SourcePath::ResultSuccess
                };
                Some((
                    schema.project_steps(&[projection], &mut work)?,
                    target.environment.clone(),
                ))
            } else {
                match expected_inactive.as_ref() {
                    Ty::Unit | Ty::Bool | Ty::Str | Ty::Bytes | Ty::Int(_) | Ty::Float(_) => {
                        let syntax = io_types::data_type(expected_inactive, syntax.span)
                            .ok_or(SourceTypesError::Unresolved)?;
                        let key = crate::static_eval::effects::bounded_argument_key(
                            &syntax,
                            &BTreeMap::new(),
                        )
                        .ok_or(SourceTypesError::BudgetExceeded)?;
                        Some((
                            SourceSchema::import(&key, None, &mut work)?,
                            self.capture_typing_environment(),
                        ))
                    }
                    _ => None,
                }
            };
            let Some((inactive_schema, inactive_environment)) = inactive else {
                return Ok(None);
            };
            let environment = result_environment(
                [
                    (&active_schema, &active_environment),
                    (&inactive_schema, &inactive_environment),
                ],
                &active_environment,
                &mut work,
            )?;
            let arguments = if success {
                [active_schema, inactive_schema]
            } else {
                [inactive_schema, active_schema]
            };
            Ok(Some((
                SourceSchema::container(SourceContainer::Result, &arguments, None, &mut work)?,
                environment,
            )))
        })();
        let (schema, environment) = match result {
            Ok(Some(source)) => source,
            Ok(None) => return,
            Err(error) => {
                self.unsupported(
                    syntax.span,
                    format!("Result creation lost its actual operand Source: {error}"),
                );
                return;
            }
        };
        value.ty = if success {
            Ty::Result(active.clone(), expected_inactive.clone())
        } else {
            Ty::Result(expected_inactive.clone(), active.clone())
        };
        self.call_input_source
            .carrier_sources
            .insert(value.cause.0, (schema.clone(), environment));
        self.attach_result_graph_witness(&schema, value, syntax.span);
    }

    pub(super) fn original_carrier_source_schema(
        &self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
    ) -> Option<(SourceSchema, FrozenEnvironment)> {
        let application = AstApplication::from_ast(syntax)?;
        if application.operands.len() != 1 {
            return None;
        }
        let (event, context) = self.call_input_source.carriers.get(&value.cause.0)?;
        if *context != self.invocation_context(frame.callable_owner) {
            return None;
        }
        let event = self.copy_call_events.get(event.0 as usize)?;
        let root = event.result_expression?;
        if !event.matches_source(syntax)
            || !self
                .application_effect
                .expressions
                .get(root)
                .is_some_and(|fact| {
                    fact.source_id.is_some()
                        && fact.source_id == syntax.hir_id
                        && fact.value.cause == value.cause
                })
            || !self
                .application_effect
                .contexts
                .get(root)
                .is_some_and(|row| row.expression == root && row.context == *context)
        {
            return None;
        }
        self.call_input_source
            .carrier_sources
            .get(&value.cause.0)
            .cloned()
    }

    fn attach_result_graph_witness(
        &mut self,
        schema: &SourceSchema,
        value: &mut Value,
        span: Span,
    ) {
        // This is a compatibility projection for unmigrated type consumers.
        // Source proof continues to use the complete graph even when a rigid
        // or recursive view has no finite closed syntax representation.
        match schema.syntax_projection(span, &mut WorkLimit::new(16384), &mut |_, _, _| {
            Err(SourceTypesError::Unresolved)
        }) {
            Ok(syntax) => value.source_type_witness = self.source_type_from_frozen_syntax(&syntax),
            Err(SourceTypesError::BudgetExceeded) => {
                self.unsupported(span, "Result compatibility syntax exceeds its work bound")
            }
            Err(_) => value.source_type_witness = None,
        }
    }

    fn producing_source_selection(
        &self,
        call: &crate::sema::copy_contract::CopyInvocation,
        binder: &str,
        key: ArgumentKey,
        value: &Value,
    ) -> Option<ArgumentKey> {
        if !matches!(&key, ArgumentKey::Binder { identity, .. } if identity == binder) {
            return Some(key);
        }
        let result = &call.result.as_ref()?.value;
        let summaries: Vec<_> = self
            .invocations
            .iter()
            .filter(|summary| {
                summary.context.is_some_and(|context| {
                    context.invocation == Some(call.id)
                        && context.owner == Some(CallableOwner::Function(call.target))
                })
            })
            .collect();
        let [summary] = summaries.as_slice() else {
            return Some(key);
        };
        let meta = format!("{binder}:invocation:{}", summary.activation?.0);
        let before = result_causes(self, result.cause)?;
        if self
            .inference_resolutions
            .iter()
            .filter(|row| {
                row.binder == binder
                    && row.selected == Ty::Generic(meta.clone())
                    && before.contains(&row.cause.0)
            })
            .count()
            != 1
        {
            return Some(key);
        }
        let after = result_causes(self, value.cause)?;
        let selections: Vec<_> = self
            .inference_resolutions
            .iter()
            .filter(|row| {
                row.binder == meta && after.contains(&row.cause.0) && after.contains(&row.origin.0)
            })
            .collect();
        let [selection] = selections.as_slice() else {
            return Some(key);
        };
        match &selection.selected {
            Ty::Generic(identity) => {
                let actual = self.generic_binders.get(identity)?;
                let function = self
                    .functions
                    .iter()
                    .find(|info| info.definition == actual.definition)?;
                crate::sema::record_bounds::certifies_type_sort(
                    identity,
                    actual,
                    function.syntax.generics.get(actual.index as usize)?,
                    &self.record_bounds,
                )
                .then(|| ArgumentKey::Binder {
                    identity: identity.clone(),
                    sort: StaticBinderSort::Type,
                })
            }
            ty @ (Ty::Unit | Ty::Bool | Ty::Str | Ty::Bytes | Ty::Int(_) | Ty::Float(_)) => {
                let syntax = io_types::data_type(ty, selection.site)?;
                crate::static_eval::effects::bounded_argument_key(&syntax, &BTreeMap::new())
            }
            _ => None,
        }
    }

    pub(super) fn original_called_result_schema(
        &self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
        work: &mut WorkLimit,
    ) -> InputSource {
        work.charge(1)?;
        if AstApplication::from_ast(syntax).is_none() {
            return Ok(None);
        }
        work.charge(self.copy_invocations.len() + self.explanations.causes.len())?;
        let causes = result_causes(self, value.cause).ok_or(SourceTypesError::Unresolved)?;
        let caller = self.invocation_context(frame.callable_owner);
        let calls: Vec<_> = self
            .copy_invocations
            .iter()
            .filter(|call| {
                call.source_event
                    .and_then(|id| self.copy_call_events.get(id.0 as usize))
                    .is_some_and(|event| event.matches_source(syntax))
                    && call.parent == caller.invocation
                    && call.caller_owner == caller.owner
                    && call
                        .result
                        .as_ref()
                        .is_some_and(|result| causes.contains(&result.value.cause.0))
            })
            .collect();
        let [actual_call] = calls.as_slice() else {
            return if calls.is_empty() {
                Ok(None)
            } else {
                Err(SourceTypesError::Unresolved)
            };
        };
        work.charge(self.functions.len())?;
        let target = self
            .functions
            .iter()
            .find(|target| target.definition == actual_call.target)
            .ok_or(SourceTypesError::MissingNode)?;
        if target.syntax.return_type.is_none() {
            return Ok(None);
        }
        // This query owns a direct reference to the original declaration.
        // A published alias has its own callable Source view and is handled
        // by the actual-callee graph query, even when it executes this body.
        let application = AstApplication::from_ast(syntax).ok_or(SourceTypesError::Unresolved)?;
        let event = self
            .copy_call_events
            .get(
                actual_call
                    .source_event
                    .ok_or(SourceTypesError::MissingNode)?
                    .0 as usize,
            )
            .ok_or(SourceTypesError::MissingNode)?;
        let callee_index = event
            .callee_expression
            .ok_or(SourceTypesError::MissingNode)?;
        let callee = self
            .application_effect
            .expressions
            .get(callee_index)
            .ok_or(SourceTypesError::MissingNode)?;
        if event.id != actual_call.source_event.unwrap()
            || event.target != Some(actual_call.target)
            || event.owner != caller.owner
            || event.parent != caller.invocation
            || application.callee.hir_id.is_none()
            || callee.source_id != application.callee.hir_id
            || self
                .application_effect
                .contexts
                .get(callee_index)
                .is_none_or(|row| row.expression != callee_index || row.context != caller)
            || !matches!(callee.value.callables.as_slice(),[Callable::Named(index)] if self.functions.get(*index).is_some_and(|function|function.definition==target.definition))
            || callee.value.sources.len() != 1
        {
            return Err(SourceTypesError::Unresolved);
        }
        let binding = self
            .bindings
            .get(
                *callee
                    .value
                    .sources
                    .first()
                    .ok_or(SourceTypesError::MissingNode)?,
            )
            .ok_or(SourceTypesError::MissingNode)?;
        if binding.parameter
            || binding.span != target.syntax.span
            || binding.name != target.syntax.name
        {
            return Ok(None);
        }
        let generic_work = target
            .syntax
            .generics
            .len()
            .checked_mul(self.generic_binders.len())
            .ok_or(SourceTypesError::BudgetExceeded)?;
        work.charge(
            generic_work
                + self.copy_invocations.len()
                + self.explanations.causes.len()
                + self.functions.len()
                + self.application_effect.contexts.len()
                + self.bound_rows.len()
                + self.effect_invocations.len()
                + target.typing_environment.generic_context.len()
                + target.typing_environment.bound_row_context.len(),
        )?;
        let admission = (|| {
            let application = AstApplication::from_ast(syntax)?;
            let callee = application.callee;
            let context = self.invocation_context(frame.callable_owner);
            let causes = result_causes(self, value.cause)?;
            let calls: Vec<_> = self
                .copy_invocations
                .iter()
                .filter(|call| {
                    call.source_event
                        .and_then(|id| self.copy_call_events.get(id.0 as usize))
                        .is_some_and(|event| event.matches_source(syntax))
                        && call.parent == context.invocation
                        && call.caller_owner == context.owner
                        && call
                            .result
                            .as_ref()
                            .is_some_and(|result| causes.contains(&result.value.cause.0))
                })
                .collect();
            let [call] = calls.as_slice() else {
                return None;
            };
            let event = self.copy_call_events.get(call.source_event?.0 as usize)?;
            let expression = self
                .application_effect
                .expressions
                .get(event.callee_expression?)?;
            if Some(event.id) != call.source_event
                || event.target != Some(call.target)
                || !event.matches_source(syntax)
                || expression.source_id.is_none()
                || expression.source_id != callee.hir_id
                || event.parent != context.invocation
                || event.owner != context.owner
            {
                return None;
            }
            if self
                .application_effect
                .contexts
                .iter()
                .filter(|row| {
                    row.expression == event.callee_expression.unwrap() && row.context == context
                })
                .count()
                != 1
            {
                return None;
            }
            let [Callable::Named(index)] = expression.value.callables.as_slice() else {
                return None;
            };
            if self.functions.get(*index)?.definition != call.target
                || expression.value.sources.len() != 1
            {
                return None;
            }
            let binding = self.bindings.get(*expression.value.sources.first()?)?;
            if binding.parameter
                || binding.span != self.functions[*index].syntax.span
                || binding.name != self.functions[*index].syntax.name
            {
                return None;
            }
            let target = self
                .functions
                .iter()
                .find(|function| function.definition == call.target)?;
            let mut scope = BoundScope {
                types: target.typing_environment.generic_context.clone(),
                rows: target.typing_environment.bound_row_context.clone(),
            };
            for (index, parameter) in target.syntax.generics.iter().enumerate() {
                let binder = self.generic_binders.values().find(|binder| {
                    binder.definition == target.definition
                        && binder.index as usize == index
                        && binder.name == parameter.name
                })?;
                scope
                    .types
                    .insert(parameter.name.clone(), binder.identity.clone());
            }
            for row in self
                .bound_rows
                .iter()
                .filter(|row| row.definition == target.definition)
            {
                if scope
                    .rows
                    .insert(row.name.clone(), row.id)
                    .is_some_and(|old| old != row.id)
                {
                    return None;
                }
            }
            let key = self.record_bound_key(target.syntax.return_type.as_ref()?, &scope)?;
            let rows: Vec<_> = self
                .effect_invocations
                .iter()
                .filter(|row| row.invocation == Some(call.id) && row.function == call.target)
                .collect();
            let [row] = rows.as_slice() else {
                return None;
            };
            if row.site != call.span || row.arguments.len() != target.syntax.generics.len() {
                return None;
            }
            Some((*call, target, scope, key, *row, context))
        })()
        .ok_or(SourceTypesError::Unresolved)?;
        let (call, target, scope, key, row, context) = admission;
        let original = target
            .syntax
            .return_type
            .as_ref()
            .ok_or(SourceTypesError::MissingNode)?;
        let environment = target.typing_environment.clone();
        if environment.is_poisoned() {
            return Err(SourceTypesError::Unresolved);
        }
        work.charge(scope.types.len() + scope.rows.len() + environment.generic_context.len())?;
        let mut names = environment.generic_context.clone();
        names.extend(scope.types.clone());
        for (name, id) in &scope.rows {
            let row = self
                .bound_rows
                .get(id.0 as usize)
                .ok_or(SourceTypesError::MissingNode)?;
            let crate::sema::model::rows::RowIdentity::Binder(identity) = &row.identity else {
                return Err(SourceTypesError::Unresolved);
            };
            if names
                .insert(name.clone(), identity.clone())
                .is_some_and(|old| old != *identity)
            {
                return Err(SourceTypesError::Unresolved);
            }
        }
        let schema = self.original_header_source_schema_in(original, &names, work)?;
        let mut selected = BTreeMap::new();
        work.charge(row.arguments.len() + row.captured_arguments.len())?;
        for (index, argument) in row.arguments.iter().enumerate() {
            let parameter = target
                .syntax
                .generics
                .get(index)
                .ok_or(SourceTypesError::MissingNode)?;
            if argument.definition != call.target
                || argument.index as usize != index
                || scope.types.get(&parameter.name) != Some(&argument.binder)
            {
                return Err(SourceTypesError::Unresolved);
            }
            let binder = self
                .generic_binders
                .get(&argument.binder)
                .ok_or(SourceTypesError::MissingNode)?;
            if !crate::sema::record_bounds::certifies_type_sort(
                &argument.binder,
                binder,
                parameter,
                &self.record_bounds,
            ) {
                continue;
            }
            let source = if let Some(source) =
                self.actual_result_selection(call, &argument.binder, work)?
            {
                source
            } else {
                // No retained graph exists. This ingress is the original owned
                // static argument or the old independently registered row UID.
                let key = if let Some(key) = &argument.key {
                    key
                } else {
                    work.charge(self.record_bounds.len() + self.scoped_source_identities.len())?;
                    let bound = self
                        .record_bounds
                        .iter()
                        .find(|bound| {
                            bound.definition == call.target
                                && bound.binder == argument.binder
                                && bound.generic_index as usize == index
                        })
                        .ok_or(SourceTypesError::MissingNode)?;
                    let expected = InvocationContext {
                        owner: Some(CallableOwner::Function(call.target)),
                        invocation: Some(call.id),
                        ..context
                    };
                    let identities: Vec<_> = self
                        .scoped_source_identities
                        .iter()
                        .enumerate()
                        .filter(|(ordinal, source)| {
                            source.id.0 as usize == *ordinal
                                && source.required == bound.id
                                && source.binder == argument.binder
                                && source.context == expected
                                && !source.occurrences.is_empty()
                        })
                        .collect();
                    let [(_, source)] = identities.as_slice() else {
                        return Err(SourceTypesError::Unresolved);
                    };
                    &source.key
                };
                if let ArgumentKey::Binder { identity, .. } = key
                    && let Some(source) = self.actual_input_binder_source(call, identity, work)?
                {
                    source
                } else {
                    let fallback = if matches!(key, ArgumentKey::Binder { identity, .. } if identity == &argument.binder)
                    {
                        environment.clone()
                    } else {
                        self.capture_typing_environment()
                    };
                    self.input_header_schema(
                        key,
                        argument.syntax.as_ref().and_then(|syntax| syntax.hir_id),
                        fallback,
                        work,
                    )?
                    .ok_or(SourceTypesError::Unresolved)?
                }
            };
            let source =
                self.refine_result_selection(call, &argument.binder, source, value, work)?;
            selected.insert(argument.binder.clone(), source);
        }
        for argument in &row.captured_arguments {
            let binder = self
                .generic_binders
                .get(&argument.binder)
                .ok_or(SourceTypesError::MissingNode)?;
            if selected.contains_key(&argument.binder)
                || binder.definition != argument.definition
                || binder.index != argument.index
                || !target
                    .typing_environment
                    .generic_context
                    .values()
                    .any(|identity| identity == &argument.binder)
            {
                return Err(SourceTypesError::Unresolved);
            }
            let declaration = self
                .functions
                .iter()
                .find(|function| function.definition == binder.definition)
                .ok_or(SourceTypesError::MissingNode)?;
            let parameter = declaration
                .syntax
                .generics
                .get(binder.index as usize)
                .ok_or(SourceTypesError::MissingNode)?;
            if !crate::sema::record_bounds::certifies_type_sort(
                &argument.binder,
                binder,
                parameter,
                &self.record_bounds,
            ) {
                continue;
            }
            let source =
                if let Some(source) = self.actual_result_selection(call, &argument.binder, work)? {
                    source
                } else if let Some(source) = target
                    .typing_environment
                    .generic_sources
                    .get(&argument.binder)
                {
                    if source.environment.is_poisoned() {
                        return Err(SourceTypesError::Unresolved);
                    }
                    (source.schema.clone(), source.environment.clone())
                } else {
                    self.input_header_schema(
                        argument.key.as_ref().ok_or(SourceTypesError::Unresolved)?,
                        argument.syntax.as_ref().and_then(|syntax| syntax.hir_id),
                        environment.clone(),
                        work,
                    )?
                    .ok_or(SourceTypesError::Unresolved)?
                };
            selected.insert(argument.binder.clone(), source);
        }
        if let ArgumentKey::Binder {
            identity,
            sort: StaticBinderSort::Type,
        } = &key
            && let Some(source) = selected.get(identity)
        {
            return Ok(Some(source.clone()));
        }
        work.charge(selected.len())?;
        let replacements = selected
            .iter()
            .map(|(identity, (schema, _))| (identity.clone(), schema.clone()))
            .collect();
        let result = schema.substitute(&replacements, work)?;
        if !result.requires_environment(work)? {
            return Ok(Some((result, environment)));
        }
        let required = schema.binder_identities(work)?;
        let dependencies = selected
            .iter()
            .filter(|(identity, _)| required.contains(*identity))
            .map(|(_, (source, environment))| (source, environment));
        let result_environment = if schema.requires_declaration_environment(work)? {
            result_environment(
                dependencies.chain([(&schema, &environment)]),
                &environment,
                work,
            )?
        } else {
            result_environment(dependencies, &environment, work)?
        };
        Ok(Some((result, result_environment)))
    }

    /// A selected graph is read from the actual callee activation, never from
    /// an effect key which may already have erased recursion or sharing.
    fn actual_result_selection(
        &self,
        call: &crate::sema::copy_contract::CopyInvocation,
        binder: &str,
        work: &mut WorkLimit,
    ) -> InputSource {
        let mut selected: Option<(SourceSchema, FrozenEnvironment)> = None;
        for parameter in [true, false] {
            work.charge(self.bindings.len())?;
            for binding in &self.bindings {
                if binding.parameter != parameter || binding.context.owner != Some(CallableOwner::Function(call.target))
                    || binding.context.invocation != Some(call.id)
                    || !self.scopes.get(&binding.owner).is_some_and(|scope| matches!(scope.origin, crate::sema::scopes::ScopeOrigin::Named(id) if id == call.id)) {
                    continue;
                }
                let Some(source) = binding.typing_environment.generic_sources.get(binder) else {
                    continue;
                };
                work.charge(1)?;
                if binding.typing_environment.is_poisoned() || source.environment.is_poisoned() {
                    return Err(SourceTypesError::Unresolved);
                }
                if let Some((original, environment)) = &selected {
                    if environment.id() != source.environment.id()
                        || !original.equivalent(&source.schema, work)?
                    {
                        return Err(SourceTypesError::Unresolved);
                    }
                } else {
                    selected = Some((source.schema.clone(), source.environment.clone()));
                }
            }
            if selected.is_some() {
                break;
            }
        }
        Ok(selected)
    }

    fn actual_input_binder_source(
        &self,
        call: &crate::sema::copy_contract::CopyInvocation,
        identity: &str,
        work: &mut WorkLimit,
    ) -> InputSource {
        let Some(event) = call.source_event else {
            return Ok(None);
        };
        work.text(identity)?;
        let supplied = self
            .call_input_source
            .supplied
            .get(&event)
            .into_iter()
            .flat_map(|inputs| inputs.values());
        let defaults = self
            .call_input_source
            .defaults
            .iter()
            .filter_map(|((actual, _), input)| (*actual == event).then_some(input));
        let mut selected: Option<(SourceSchema, FrozenEnvironment)> = None;
        for input in supplied.chain(defaults) {
            work.charge(1)?;
            if input.context != call.entry.caller_context {
                return Err(SourceTypesError::Unresolved);
            }
            let Some((schema, environment)) = input.input_source()? else {
                continue;
            };
            if environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            let Some(source) = schema.binder_view(identity, work)? else {
                continue;
            };
            if let Some((previous, original)) = &selected {
                if original.id() != environment.id() || !previous.equivalent(&source, work)? {
                    return Err(SourceTypesError::Unresolved);
                }
            } else {
                selected = Some((source, environment.clone()));
            }
        }
        Ok(selected)
    }

    fn refine_result_selection(
        &self,
        call: &crate::sema::copy_contract::CopyInvocation,
        binder: &str,
        source: (SourceSchema, FrozenEnvironment),
        value: &Value,
        work: &mut WorkLimit,
    ) -> Result<(SourceSchema, FrozenEnvironment), SourceTypesError> {
        if source.0.bare_binder_identity(work)?.as_deref() != Some(binder) {
            return Ok(source);
        }
        work.charge(binder.len().div_ceil(32))?;
        let identity = ArgumentKey::Binder {
            identity: binder.into(),
            sort: StaticBinderSort::Type,
        };
        work.charge(
            self.invocations.len()
                + self.inference_resolutions.len().saturating_mul(2)
                + self.explanations.causes.len().saturating_mul(2),
        )?;
        let selected = self
            .producing_source_selection(call, binder, identity.clone(), value)
            .ok_or(SourceTypesError::Unresolved)?;
        if selected == identity {
            return Ok(source);
        }
        if let ArgumentKey::Binder { identity, .. } = &selected
            && let Some(original) = self.type_source.environment.generic_sources.get(identity)
        {
            if original.environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            return Ok((original.schema.clone(), original.environment.clone()));
        }
        let environment = if let ArgumentKey::Binder { identity, .. } = &selected {
            // A contextual result may select an uninstantiated caller UID
            // without any supplied operand or formal binding. Its original
            // declaration, rather than each query's fresh capture, owns the
            // interpretation of that UID.
            work.charge(
                self.functions.len()
                    + self.type_source.environment.generic_context.len()
                    + self.record_bounds.len(),
            )?;
            if !self
                .type_source
                .environment
                .generic_context
                .values()
                .any(|actual| actual == identity)
            {
                return Err(SourceTypesError::Unresolved);
            }
            let binder = self
                .generic_binders
                .get(identity)
                .ok_or(SourceTypesError::MissingNode)?;
            let mut declarations = self
                .functions
                .iter()
                .filter(|function| function.definition == binder.definition);
            let declaration = declarations.next().ok_or(SourceTypesError::MissingNode)?;
            // A repeated nested declaration may have different captures. A
            // canonical definition UID alone cannot choose one such instance.
            if declarations.next().is_some()
                || declaration.syntax.span != binder.owner
                || !declaration
                    .syntax
                    .generics
                    .get(binder.index as usize)
                    .is_some_and(|parameter| {
                        parameter.name == binder.name
                            && crate::sema::record_bounds::certifies_type_sort(
                                identity,
                                binder,
                                parameter,
                                &self.record_bounds,
                            )
                    })
                || declaration.typing_environment.is_poisoned()
            {
                return Err(SourceTypesError::Unresolved);
            }
            declaration.typing_environment.clone()
        } else {
            self.capture_typing_environment()
        };
        self.input_header_schema(&selected, source.0.original(), environment, work)?
            .ok_or(SourceTypesError::Unresolved)
    }
}

pub(super) fn result_environment<'a>(
    parts: impl IntoIterator<Item = (&'a SourceSchema, &'a FrozenEnvironment)>,
    fallback: &FrozenEnvironment,
    work: &mut WorkLimit,
) -> Result<FrozenEnvironment, SourceTypesError> {
    if fallback.is_poisoned() {
        return Err(SourceTypesError::Unresolved);
    }
    let mut selected: Option<&FrozenEnvironment> = None;
    for (schema, environment) in parts {
        work.charge(1)?;
        if environment.is_poisoned() {
            return Err(SourceTypesError::Unresolved);
        }
        if schema.requires_environment(work)? {
            if selected.is_some_and(|original| original.id() != environment.id()) {
                return Err(SourceTypesError::Unresolved);
            }
            selected = Some(environment);
        }
    }
    Ok(selected.unwrap_or(fallback).clone())
}

fn result_causes(checker: &Checker, root: CauseId) -> Option<BTreeSet<u32>> {
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    let mut work = 4096usize;
    while let Some(id) = pending.pop() {
        work = work.checked_sub(1)?;
        if seen.insert(id.0) {
            pending.extend(
                checker
                    .explanations
                    .causes
                    .get(id.0 as usize)?
                    .parents
                    .iter()
                    .copied(),
            );
        }
    }
    Some(seen)
}
