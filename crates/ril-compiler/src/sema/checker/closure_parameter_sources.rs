//! Inferred formals retain the real entry graph in the existing Source index.
//! Their lexical environment remains the closure declaration's environment.
use super::*;
use crate::sema::{
    application_effect::EntryOrigin,
    default_uses::{ArgumentSource, DefaultOrigin},
    scopes::ScopeOrigin,
    source_types::projection_receipts::{self, ProjectionOccurrence, SourceRead},
};

impl Checker {
    pub(in crate::sema::checker) fn signature_closure_return_target(
        &mut self,
        closure: usize,
        span: Span,
    ) -> Result<Option<source_reception::Target>, SourceTypesError> {
        let Some(id) = self.closure_invocation_stack.last() else {
            return Ok(None);
        };
        let call = self
            .closure_invocations
            .get(id.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        let EntryOrigin::SignatureProbe(source) = &call.entry.origin else {
            return Ok(None);
        };
        if call.closure != closure {
            return Err(SourceTypesError::Unresolved);
        }
        let source = source.clone();
        let mut work = WorkLimit::new(32768);
        crate::sema::application_effect::SignatureProbeSource::validate_header(
            &source.header,
            &self.semantic_hir,
            &mut work,
        )?;
        let root = self.with_typing_environment(&source.environment, |checker| {
            checker.original_header_source_schema(&source.header, &mut work)
        })?;
        work.charge(source.path.len() + 1)?;
        let mut path = source.path.as_ref().clone();
        path.push(crate::sema::source_types::SourcePath::CallableResult);
        let result = root.project_steps(&path, &mut work)?;
        let (result, environment) =
            self.selected_input_schema(result, source.environment.clone(), &mut work)?;
        let syntax = result.syntax_projection(span, &mut work, &mut |identity, row, budget| {
            budget
                .charge(environment.generic_context.len() + environment.bound_row_context.len())?;
            let name = environment
                .generic_context
                .iter()
                .find_map(|(name, uid)| (uid == identity).then_some(name))
                .or_else(|| {
                    row.then(|| {
                        environment.bound_row_context.iter().find_map(|(name, id)| {
                            self.bound_rows.get(id.0 as usize).and_then(|bound| {
                                matches!(&bound.identity,
                        crate::sema::model::rows::RowIdentity::Binder(uid) if uid == identity)
                                .then_some(name)
                            })
                        })
                    })
                    .flatten()
                })
                .ok_or(SourceTypesError::Unresolved)?;
            budget.text(name)?;
            Ok(TypeExpr {
                hir_id: None,
                text: String::new(),
                span,
                kind: TypeKind::Name {
                    path: vec![name.clone()],
                    arguments: Vec::new(),
                },
            })
        });
        let syntax = match syntax {
            Ok(syntax) => Some(std::sync::Arc::new(syntax)),
            Err(SourceTypesError::BudgetExceeded) => return Err(SourceTypesError::BudgetExceeded),
            Err(_) => None,
        };
        let sensitivity = match result.sensitivity(&mut work) {
            crate::sema::source_types::SourceSensitivity::Absent { .. } => {
                source_reception::SchemaSensitivity::NotRequired
            }
            crate::sema::source_types::SourceSensitivity::Sensitive { .. } => {
                source_reception::SchemaSensitivity::Required
            }
            crate::sema::source_types::SourceSensitivity::Unknown { reason } => return Err(reason),
        };
        Ok(Some(source_reception::Target {
            source: Some(source_reception::TargetSource {
                header: source.header.clone(),
                environment: source.environment.clone(),
                path,
            }),
            environment,
            span,
            schema: Some(result),
            syntax,
            empty_array_context: None,
            static_projection: None,
            sensitivity,
        }))
    }

    pub(in crate::sema::checker) fn inferred_closure_parameter_source(
        &mut self,
        binding: BindingId,
        name: &str,
    ) -> Option<InputSource> {
        let info = self.bindings.get(binding)?;
        let scope = self.scopes.get(&info.owner)?;
        let ScopeOrigin::Closure(id) = scope.origin else {
            return None;
        };
        let call = self.closure_invocations.get(id.0 as usize)?;
        // Arguments and signature sources are shared. Only a generated
        // origin owns a vector which this invocation snapshot must copy.
        let clone_work = match &call.entry.origin {
            EntryOrigin::Generated { inputs, .. } => inputs.len() + 1,
            _ => 1,
        };
        if !self.application_effect.admit(clone_work) {
            return Some(Err(SourceTypesError::BudgetExceeded));
        }
        let call = call.clone();
        let closure = self.closures.get(call.closure)?;
        let site = self
            .application_effect
            .closure_sites
            .get(closure.site?.0 as usize)?;
        let original = self.semantic_hir.expression(site.source)?;
        let crate::hir::nodes::ExprKind::Lambda { parameters, .. } = &original.kind else {
            return Some(Err(SourceTypesError::Unresolved));
        };
        let mut admission = WorkLimit::new(16384);
        if let Err(error) = admission.charge(parameters.len() + self.call_arguments.len()) {
            return Some(Err(error));
        }
        let slots: Vec<_> = parameters.iter().enumerate().filter(|(_, parameter)| {
            info.pattern == Some(parameter.pattern)
                && self.semantic_hir.pattern(parameter.pattern).is_some_and(|pattern|
                    matches!(&pattern.kind, crate::hir::nodes::PatternKind::Name(actual) if actual == name))
        }).collect();
        let [(slot, parameter)] = slots.as_slice() else {
            return None;
        };
        if parameter.ty.is_some() {
            return None;
        }
        let slot = *slot;
        if call.id != id
            || call.activation != Some(info.owner)
            || info.context.closure_invocation != Some(id)
            || info.context.closure != Some(call.closure)
            || info.context.owner != Some(CallableOwner::Lambda(site.id))
            || closure.hir_id != Some(site.source)
            || info.name != name
            || !info.parameter
        {
            return Some(Err(SourceTypesError::Unresolved));
        }
        Some(match &call.entry.origin {
            EntryOrigin::Application(event) => (|| {
                let mut rows = self
                    .call_arguments
                    .iter()
                    .filter(|row| row.source_event == *event);
                let row = rows.next().ok_or(SourceTypesError::MissingNode)?;
                if rows.next().is_some() || !row.evaluation_complete {
                    return Err(SourceTypesError::Unresolved);
                }
                let input = match row.slots.get(slot).ok_or(SourceTypesError::MissingNode)? {
                    ArgumentSource::Supplied => {
                        let token = row
                            .supplied
                            .get(&(slot as u32))
                            .ok_or(SourceTypesError::MissingNode)?;
                        let input = self
                            .call_input_source
                            .supplied
                            .get(event)
                            .and_then(|slots| slots.get(&slot))
                            .ok_or(SourceTypesError::MissingNode)?;
                        if input.observation != Some(token.expression) || input.default.is_some() {
                            return Err(SourceTypesError::Unresolved);
                        }
                        input
                    }
                    ArgumentSource::Default(id) => {
                        let receipt = self
                            .default_uses
                            .get(id.0 as usize)
                            .ok_or(SourceTypesError::MissingNode)?;
                        let input = self
                            .call_input_source
                            .defaults
                            .get(&(*event, slot))
                            .ok_or(SourceTypesError::MissingNode)?;
                        if receipt.id != *id
                            || receipt.origin != DefaultOrigin::Call(*event)
                            || receipt.parameter as usize != slot
                            || input.default != Some(*id)
                            || input.observation != receipt.result_expression
                        {
                            return Err(SourceTypesError::Unresolved);
                        }
                        input
                    }
                    _ => return Err(SourceTypesError::Unresolved),
                };
                if input.context != call.entry.caller_context
                    || input.allocation_epoch > call.entry.allocation_epoch
                {
                    return Err(SourceTypesError::Unresolved);
                }
                input.source.clone()
            })(),
            EntryOrigin::Generated { .. } => {
                self.generated_input_source_schema(&call.entry.origin, slot)
            }
            EntryOrigin::SignatureProbe(source) => (|| {
                let mut work = WorkLimit::new(32768);
                let auth = crate::sema::application_effect::closure_signature_assumption(
                    &call,
                    slot,
                    &self.semantic_hir,
                    &self.bindings,
                    self.recency_moves.len(),
                    &mut work,
                )?;
                let environment = auth.environment.clone();
                let root = self.with_typing_environment(&environment, |checker| {
                    checker.original_header_source_schema(auth.header, &mut work)
                })?;
                let schema = source.parameter_schema(&root, slot, auth.mode, &mut work)?;
                self.selected_input_schema(schema, environment, &mut work)
                    .map(Some)
            })(),
            _ => Err(SourceTypesError::Unresolved),
        })
    }

    pub(in crate::sema::checker) fn generated_observation_source_schema(
        &self,
        observation: ril_compiler_core::ids::EvaluationOccurrenceId,
        work: &mut WorkLimit,
    ) -> Option<InputSource> {
        let fact = self
            .application_effect
            .expressions
            .get(observation.0 as usize)?;
        let source = fact.source_id?;
        let plan = match projection_receipts::projection_path(&self.semantic_hir, source, work) {
            Ok(Some(plan)) => plan,
            Ok(None) => return None,
            Err(error) => return Some(Err(error)),
        };
        Some((|| {
            let record = self
                .application_effect
                .evaluations
                .get(observation.0 as usize)
                .ok_or(SourceTypesError::MissingNode)?;
            let projection = self.source_projection_receipts().project(
                &plan,
                ProjectionOccurrence {
                    identity: record.identity.ok_or(SourceTypesError::MissingNode)?,
                    context: record.context,
                    cause: fact.value.cause,
                },
                SourceRead::Received,
                work,
            )?;
            let root = self
                .application_effect
                .expressions
                .get(projection.root.0 as usize)
                .ok_or(SourceTypesError::MissingNode)?;
            if root.source_id != Some(plan.root()) || root.value.sources.len() != 1 {
                return Err(SourceTypesError::Unresolved);
            }
            let binding = *root.value.sources.first().unwrap();
            let info = self
                .bindings
                .get(binding)
                .ok_or(SourceTypesError::MissingNode)?;
            if info.name != plan.name() {
                return Err(SourceTypesError::Unresolved);
            }
            let Some((schema, environment)) =
                self.parameter_source_schema_if_known(binding, None, work)?
            else {
                return Ok(None);
            };
            Ok(Some((
                schema.project_steps(&projection.steps, work)?,
                environment,
            )))
        })())
    }
}
