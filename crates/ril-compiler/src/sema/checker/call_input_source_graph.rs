//! Source transport keeps the admitted graph and its declaration environment.
//! Keys enter only at original written headers, never between graph queries.
use super::*;

impl Checker {
    pub(in crate::sema::checker) fn original_source_receiving_schema(
        &mut self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
        work: &mut WorkLimit,
    ) -> InputSource {
        let source = self.raw_original_source_schema(value, syntax, frame, work, 0)?;
        let Some((schema, environment)) = source else {
            return Ok(None);
        };
        let context = self.invocation_context(frame.callable_owner);
        work.charge(self.invocation_witnesses.len())?;
        let projected = self.invocation_witnesses.iter().any(|row| {
            row.context == context
                && matches!(&row.kind, crate::sema::effect_identity::InvocationWitnessKind::ImplicitUnwrap(proof)
                    if Some(proof.occurrence.source) == syntax.hir_id && proof.cause == value.cause)
        });
        if !projected {
            return Ok(Some((schema, environment)));
        }
        let occurrence = self.source_projection_occurrence(
            syntax.hir_id.ok_or(SourceTypesError::MissingNode)?,
            value,
            context,
            work,
        )?;
        let depth = self
            .source_projection_receipts()
            .unwrap_depth(occurrence, work)?;
        let schema = if depth == 1 {
            schema.project_steps(
                &[crate::sema::source_types::SourcePath::OptionalPayload],
                work,
            )?
        } else {
            schema
        };
        Ok(Some((schema, environment)))
    }

    pub(super) fn input_header_schema(
        &self,
        key: &ArgumentKey,
        original: Option<ril_compiler_core::ids::TypeExprId>,
        environment: FrozenEnvironment,
        work: &mut WorkLimit,
    ) -> InputSource {
        if environment.is_poisoned() {
            return Err(SourceTypesError::Unresolved);
        }
        let schema = SourceSchema::import(key, original, work)?;
        let schema = crate::sema::source_types::declarations::resolve_schema(
            &schema,
            &self.semantic_hir,
            work,
        )?;
        Ok(Some((schema, environment)))
    }

    pub(super) fn raw_original_source_schema(
        &mut self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
        work: &mut WorkLimit,
        depth: usize,
    ) -> InputSource {
        work.charge(1)?;
        if depth >= 64 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        if let Some(source) = self.storage_binding_source_schema(value, syntax, frame) {
            return source;
        }
        if let Some(source) = syntax.hir_id
            && let Some(schema) = crate::sema::source_types::declarations::construction_schema(
                source,
                &self.semantic_hir,
                work,
            )?
        {
            let environment = self.capture_typing_environment();
            if environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            return Ok(Some((schema, environment)));
        }
        if value.source_type_witness.is_none()
            && matches!(&syntax.kind, ExprKind::Unary { operator, .. } if operator == "^mut")
        {
            return self.original_composite_source_schema(value, syntax, frame, work, depth);
        }
        if let Some(source) = self.original_copy_source_schema(value, syntax, frame, work, depth)? {
            return Ok(source);
        }
        if let ExprKind::Name(name) = &syntax.kind
            && self.constant_references.contains_key(name)
        {
            let original = self
                .constant_source_views
                .get(name)
                .ok_or(SourceTypesError::MissingNode)?;
            if !original.validate_closed() || value.source_type_witness.as_ref() != Some(original) {
                return Err(SourceTypesError::Unresolved);
            }
            let key = crate::static_eval::effects::bounded_argument_key(
                &original.syntax,
                &BTreeMap::new(),
            )
            .ok_or(SourceTypesError::BudgetExceeded)?;
            return self.input_header_schema(
                &key,
                original.syntax.hir_id,
                self.capture_typing_environment(),
                work,
            );
        }
        if let Some(source) = self.original_carrier_source_schema(value, syntax, frame) {
            return Ok(Some(source));
        }
        if let Some(source) = self.original_called_result_schema(value, syntax, frame, work)? {
            return Ok(Some(source));
        }
        if let Some(source) = self.original_constructor_result_schema(value, syntax, frame, work)? {
            return Ok(Some(source));
        }
        if let Some(source) =
            self.original_public_result_schema(value, syntax, frame, work, depth)?
        {
            return Ok(Some(source));
        }
        if matches!(
            syntax.kind,
            ExprKind::Array(_)
                | ExprKind::Map(_)
                | ExprKind::Tuple(_)
                | ExprKind::Record { ty: None, .. }
        ) && let Some(source) =
            self.original_composite_source_schema(value, syntax, frame, work, depth)?
        {
            return Ok(Some(source));
        }
        if let Some(source) =
            self.original_canonical_builtin_source_schema(value, syntax, frame, work)?
        {
            return Ok(Some(source));
        }
        if let Some(source) = self.original_closure_source_schema(value, work)? {
            return Ok(Some(source));
        }
        if let Some(witness) = &value.source_type_witness {
            if !witness.validate_closed() {
                return Err(SourceTypesError::Unresolved);
            }
            let key = crate::static_eval::effects::bounded_argument_key(
                &witness.syntax,
                &BTreeMap::new(),
            )
            .ok_or(SourceTypesError::BudgetExceeded)?;
            return self.input_header_schema(
                &key,
                witness.syntax.hir_id,
                self.capture_typing_environment(),
                work,
            );
        }
        if let ExprKind::Name(name) = &syntax.kind {
            let Some(binding) = value.sources.first().and_then(|id| self.bindings.get(*id)) else {
                return Ok(None);
            };
            if value.sources.len() != 1 || binding.name != *name {
                return Ok(None);
            }
            if binding.parameter {
                let Some((header, environment)) =
                    self.formal_source_declaration(value, syntax, frame)
                else {
                    return Ok(None);
                };
                return self.with_typing_environment(&environment, |checker| {
                    let target = checker.freeze_source_receiving_target(&header);
                    Ok(target.schema.map(|schema| (schema, environment.clone())))
                });
            }
            if let [Callable::Named(index)] = value.callables.as_slice() {
                let function = self.functions[*index].clone();
                if binding.span != function.syntax.span || !function.syntax.generics.is_empty() {
                    return Ok(None);
                }
                let mut parameters = function.syntax.parameters.clone();
                for parameter in &mut parameters {
                    parameter.default = None;
                }
                let header = TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span: syntax.span,
                    kind: TypeKind::Callable {
                        parameters,
                        result: function.syntax.return_type.clone().map(Box::new),
                        annotations: function.syntax.annotations.clone(),
                    },
                };
                let mut budget = work.remaining();
                super::super::source_receiving::resolved_symbolic_names(
                    &header,
                    &function.typing_environment.generic_context,
                    &self.types,
                    &mut budget,
                    0,
                )
                .ok_or(SourceTypesError::Unresolved)?;
                work.charge(work.remaining() - budget)?;
                let key = crate::static_eval::effects::bounded_argument_key(
                    &header,
                    &function.typing_environment.generic_context,
                )
                .ok_or(SourceTypesError::BudgetExceeded)?;
                return self.input_header_schema(&key, None, function.typing_environment, work);
            }
        }
        if let Some(source) =
            self.original_composite_source_schema(value, syntax, frame, work, depth)?
        {
            return Ok(Some(source));
        }
        Ok(None)
    }

    /// A published callable view owns its result contract. Follow the real
    /// callee observation instead of requiring the value to remain a direct
    /// reference to the named function which originally implemented it.
    fn original_public_result_schema(
        &mut self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
        work: &mut WorkLimit,
        depth: usize,
    ) -> InputSource {
        let Some(application) = crate::hir::application::AstApplication::from_ast(syntax) else {
            return Ok(None);
        };
        let context = self.invocation_context(frame.callable_owner);
        work.charge(self.copy_call_events.len())?;
        let mut events = self.copy_call_events.iter().filter(|event| {
            event.matches_source(syntax)
                && event.owner == context.owner
                && event.parent == context.invocation
                && event
                    .result_expression
                    .and_then(|index| self.application_effect.expressions.get(index))
                    .is_some_and(|fact| {
                        fact.source_id == syntax.hir_id && fact.value.cause == value.cause
                    })
        });
        let Some(event) = events.next() else {
            return Ok(None);
        };
        if events.next().is_some() {
            return Err(SourceTypesError::Unresolved);
        }
        let token = event
            .callee_expression
            .ok_or(SourceTypesError::MissingNode)?;
        let callee = self
            .application_effect
            .expressions
            .get(token)
            .ok_or(SourceTypesError::MissingNode)?;
        let row = self
            .application_effect
            .contexts
            .get(token)
            .ok_or(SourceTypesError::MissingNode)?;
        if application.callee.hir_id.is_none()
            || callee.source_id != application.callee.hir_id
            || row.expression != token
            || row.context != context
        {
            return Err(SourceTypesError::Unresolved);
        }
        if let [Callable::Builtin(name)] = callee.value.callables.as_slice()
            && let Some(operation) = self.operations.get(name)
        {
            let signature = operation
                .signature
                .as_ref()
                .ok_or(SourceTypesError::Unresolved)?;
            let (_, result) = signature
                .callable_parts(work)?
                .ok_or(SourceTypesError::Unresolved)?;
            let environment = if let Some(source) = &operation.source {
                source.environment.clone()
            } else {
                if result.requires_environment(work)? {
                    return Err(SourceTypesError::Unresolved);
                }
                self.capture_typing_environment()
            };
            if environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            return Ok(Some((result, environment)));
        }
        let callee = callee.value.clone();
        let Some((schema, environment)) =
            self.raw_original_source_schema(&callee, application.callee, frame, work, depth + 1)?
        else {
            return Ok(None);
        };
        if environment.is_poisoned() {
            return Err(SourceTypesError::Unresolved);
        }
        Ok(schema
            .callable_parts(work)?
            .map(|(_, result)| (result, environment)))
    }
}
