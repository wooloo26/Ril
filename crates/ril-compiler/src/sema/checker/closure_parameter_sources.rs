//! Inferred formals retain the real entry graph in the existing Source index.
//! Their lexical environment remains the closure declaration's environment.
use super::*;
use crate::sema::{application_effect::EntryOrigin, scopes::ScopeOrigin};

impl Checker {
    /// A preparation formal has a declaration type before any closure body
    /// entry exists. Retain that original header under this binding's frozen
    /// interpretation; this supplies no actual argument or capability proof.
    pub(in crate::sema::checker) fn preparation_formal_source(
        &mut self,
        binding: BindingId,
    ) -> InputSource {
        let info = self
            .bindings
            .get(binding)
            .ok_or(SourceTypesError::MissingNode)?;
        let Some(CallableOwner::Lambda(site)) = info.context.owner else {
            return Ok(None);
        };
        if !info.parameter || info.pattern.is_none() || info.context.closure_invocation.is_some() {
            return Ok(None);
        }
        let pattern = info.pattern.ok_or(SourceTypesError::MissingNode)?;
        let environment = info.typing_environment.clone();
        let mut lease = self.application_effect.lease_work(32768);
        let source = (|| {
            let work = lease.work();
            work.charge(4 + self.closures.len())?;
            let site = self
                .application_effect
                .closure_sites
                .get(site.0 as usize)
                .filter(|actual| actual.id == site)
                .ok_or(SourceTypesError::MissingNode)?;
            let original = self
                .semantic_hir
                .expression(site.source)
                .ok_or(SourceTypesError::MissingNode)?;
            let crate::hir::nodes::ExprKind::Lambda { parameters, .. } = &original.kind else {
                return Err(SourceTypesError::Unresolved);
            };
            work.charge(parameters.len())?;
            let Some(parameter) = parameters
                .iter()
                .find(|parameter| parameter.pattern == pattern)
            else {
                return Ok(None);
            };
            let Some(header) = parameter.ty else {
                return Ok(None);
            };
            let mut syntax = None;
            for closure in &self.closures {
                if closure.site != Some(site.id) || closure.hir_id != Some(site.source) {
                    continue;
                }
                work.charge(closure.parameters.len())?;
                if let Some(found) = closure
                    .parameters
                    .iter()
                    .find(|parameter| {
                        parameter.pattern.hir_id == Some(pattern)
                            && parameter.ty.as_ref().and_then(|ty| ty.hir_id) == Some(header)
                    })
                    .and_then(|parameter| parameter.ty.as_ref())
                {
                    let mut remaining = work.remaining();
                    let before = remaining;
                    let admitted =
                        crate::static_eval::charge_type_syntax_clone(found, &mut remaining);
                    work.charge(before - remaining)?;
                    admitted.ok_or(SourceTypesError::BudgetExceeded)?;
                    syntax = Some(found.clone());
                    break;
                }
            }
            let syntax = syntax.ok_or(SourceTypesError::MissingNode)?;
            let binders = self.original_captured_header_binders(&environment, work)?;
            let schema = self.original_header_source_schema_in(&syntax, &binders, work)?;
            Ok(Some((schema, environment)))
        })();
        let returned = self.application_effect.return_work(lease);
        source.and_then(|source| returned.map(|()| source))
    }

    pub(in crate::sema::checker) fn callable_result_target(
        &mut self,
        target: &source_reception::Target,
        span: Span,
    ) -> Result<source_reception::Target, SourceTypesError> {
        use crate::sema::{
            source_reception::{SchemaSensitivity, Target},
            source_types::SourcePath,
        };
        let mut lease = self.application_effect.lease_work(32768);
        let result = (|| {
            let work = lease.work();
            work.charge(3)?;
            let schema = target
                .schema
                .as_ref()
                .ok_or(SourceTypesError::Unresolved)?
                .project_steps(&[SourcePath::CallableResult], work)?;
            let source = target
                .source
                .as_ref()
                .map(|source| source.projected(SourcePath::CallableResult, work))
                .transpose()?;
            let syntax = if let Some(TypeExpr {
                kind:
                    TypeKind::Callable {
                        result: Some(result),
                        ..
                    },
                ..
            }) = target.syntax.as_deref()
            {
                let mut remaining = work.remaining();
                let before = remaining;
                let admitted = crate::static_eval::charge_type_syntax_clone(result, &mut remaining);
                work.charge(before - remaining)?;
                admitted.ok_or(SourceTypesError::BudgetExceeded)?;
                Some(std::sync::Arc::new((**result).clone()))
            } else {
                let projected = schema.syntax_projection(span, work, &mut |identity, row, budget| {
                    budget.charge(target.environment.generic_context.len() + target.environment.bound_row_context.len())?;
                    let name = target.environment.generic_context.iter().find_map(|(name, uid)| (uid == identity).then_some(name))
                        .or_else(|| row.then(|| target.environment.bound_row_context.iter().find_map(|(name, id)| {
                            self.bound_rows.get(id.0 as usize).and_then(|bound| matches!(&bound.identity,
                                crate::sema::model::rows::RowIdentity::Binder(uid) if uid == identity).then_some(name))
                        })).flatten()).ok_or(SourceTypesError::Unresolved)?;
                    budget.text(name)?;
                    Ok(TypeExpr { hir_id: None, text: String::new(), span,
                        kind: TypeKind::Name { path: vec![name.clone()], arguments: Vec::new() } })
                });
                match projected {
                    Ok(syntax) => Some(std::sync::Arc::new(syntax)),
                    Err(SourceTypesError::BudgetExceeded) => {
                        return Err(SourceTypesError::BudgetExceeded);
                    }
                    Err(SourceTypesError::RecursiveLegacyKey | SourceTypesError::Unresolved) => {
                        None
                    }
                    Err(error) => return Err(error),
                }
            };
            let sensitivity = match schema.sensitivity(work) {
                crate::sema::source_types::SourceSensitivity::Absent { .. } => {
                    SchemaSensitivity::NotRequired
                }
                crate::sema::source_types::SourceSensitivity::Sensitive { .. } => {
                    SchemaSensitivity::Required
                }
                crate::sema::source_types::SourceSensitivity::Unknown { reason } => {
                    // A rigid generic result still has a complete type graph.
                    // Unknown sensitivity requires that graph at reception;
                    // it does not prove the absence of source coordinates.
                    if reason == SourceTypesError::BudgetExceeded {
                        return Err(reason);
                    }
                    SchemaSensitivity::Unknown
                }
            };
            Ok(Target {
                source,
                schema: Some(schema),
                environment: target.environment.clone(),
                syntax,
                span,
                sensitivity,
                static_projection: None,
                empty_array_context: None,
            })
        })();
        let returned = self.application_effect.return_work(lease);
        result.and_then(|target| returned.map(|()| target))
    }

    pub(in crate::sema::checker) fn packet_callable_result_target(
        &mut self,
        packet: &EvaluatedValue,
        span: Span,
    ) -> Result<Option<source_reception::Target>, SourceTypesError> {
        let mut lease = self.application_effect.lease_work(32768);
        let original = packet.current_source(
            crate::sema::source_types_ref::SourceTypesRef::Live(
                self.type_source.storage.live_types(),
            ),
            lease.work(),
        );
        let returned = self.application_effect.return_work(lease);
        let original = original.and_then(|source| returned.map(|()| source))?;
        let Some(schema) = original.schema else {
            return Ok(None);
        };
        let target = source_reception::Target {
            source: None,
            schema: Some(schema),
            environment: original.environment,
            syntax: None,
            span,
            sensitivity: source_reception::SchemaSensitivity::Unknown,
            static_projection: None,
            empty_array_context: None,
        };
        self.callable_result_target(&target, span).map(Some)
    }

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
        let result = source.schema.project_steps(
            &[crate::sema::source_types::SourcePath::CallableResult],
            &mut work,
        )?;
        let (result, environment) =
            self.selected_input_schema(result, source.environment.clone(), &mut work)?;
        self.owned_type_receiving_target(result, environment, span, &mut work)
            .map(Some)
    }

    pub(in crate::sema::checker) fn owned_type_receiving_target(
        &self,
        schema: SourceSchema,
        environment: crate::sema::context::FrozenEnvironment,
        span: Span,
        work: &mut WorkLimit,
    ) -> Result<source_reception::Target, SourceTypesError> {
        let environment = schema.callable_interpretation(work)?.unwrap_or(environment);
        let syntax = schema.syntax_projection(span, work, &mut |identity, row, budget| {
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
        let sensitivity = match schema.sensitivity(work) {
            crate::sema::source_types::SourceSensitivity::Absent { .. } => {
                source_reception::SchemaSensitivity::NotRequired
            }
            crate::sema::source_types::SourceSensitivity::Sensitive { .. } => {
                source_reception::SchemaSensitivity::Required
            }
            crate::sema::source_types::SourceSensitivity::Unknown { reason } => {
                if reason == SourceTypesError::BudgetExceeded {
                    return Err(reason);
                }
                source_reception::SchemaSensitivity::Unknown
            }
        };
        Ok(source_reception::Target {
            source: None,
            environment,
            span,
            schema: Some(schema),
            syntax,
            empty_array_context: None,
            static_projection: None,
            sensitivity,
        })
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
        let closure = self.closures.get(call.closure)?;
        let site = self
            .application_effect
            .closure_sites
            .get(closure.site?.0 as usize)?;
        let original = self.semantic_hir.expression(site.source)?;
        let crate::hir::nodes::ExprKind::Lambda { parameters, .. } = &original.kind else {
            return Some(Err(SourceTypesError::Unresolved));
        };
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
        let introducer = info.pattern?;
        let mut work = WorkLimit::new(16384);
        let mut selected = None;
        if !self.application_effect.admit(1 + parameters.len()) {
            return Some(Err(SourceTypesError::BudgetExceeded));
        }
        for (slot, parameter) in parameters.iter().enumerate() {
            let contains = crate::sema::pattern_sources::contains_binding(
                &self.semantic_hir,
                parameter.pattern,
                introducer,
                name,
                &mut work,
            );
            match contains {
                Ok(true) => {
                    if selected
                        .replace((slot, parameter.pattern, parameter.ty.is_some()))
                        .is_some()
                    {
                        return Some(Err(SourceTypesError::Unresolved));
                    }
                }
                Ok(false) => {}
                Err(error) => return Some(Err(error)),
            }
        }
        let (slot, root, annotated) = selected?;
        if annotated {
            return None;
        }
        let packet = call.entry.arguments.get(slot)?.packet.clone();
        let mut lease = self.application_effect.lease_work(32768);
        let result = (|| {
            let source = packet.input_source(
                SourceTypesRef::Live(self.type_source.storage.live_types()),
                lease.work(),
            )?;
            let Some(schema) = source.schema else {
                return Ok(None);
            };
            let projected = self.project_parameter_source(
                binding,
                root,
                &schema,
                &source.environment,
                lease.work(),
            )?;
            Ok(projected.map(|schema| (schema, source.environment)))
        })();
        let returned = self.application_effect.return_work(lease);
        Some(result.and_then(|source| returned.map(|()| source)))
    }
}
