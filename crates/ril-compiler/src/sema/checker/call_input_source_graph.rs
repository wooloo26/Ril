//! Source transport keeps the admitted graph and its declaration environment.
//! Keys enter only at original written headers, never between graph queries.
use super::*;

impl Checker {
    // The remaining finite closed-witness adapter has its own admission rule.
    // A witness is not an original HIR header, and must not bypass that
    // header's identity checks by presenting a missing or normalized ID.
    fn closed_witness_input_schema(
        &self,
        witness: &SourceTypeWitness,
        environment: FrozenEnvironment,
        work: &mut WorkLimit,
    ) -> InputSource {
        if !witness.validate_closed() {
            return Err(SourceTypesError::Unresolved);
        }
        let key =
            crate::static_eval::effects::bounded_argument_key(&witness.syntax, &BTreeMap::new())
                .ok_or(SourceTypesError::BudgetExceeded)?;
        self.input_header_schema(&key, witness.syntax.hir_id, environment, work)
    }

    pub(in crate::sema::checker) fn input_original_header_schema(
        &self,
        syntax: &TypeExpr,
        environment: FrozenEnvironment,
        work: &mut WorkLimit,
    ) -> InputSource {
        if environment.is_poisoned() {
            return Err(SourceTypesError::Unresolved);
        }
        work.charge(environment.generic_context.len() + environment.bound_row_context.len())?;
        for (name, identity) in &environment.generic_context {
            work.text(name)?;
            work.text(identity)?;
        }
        let mut binders = environment.generic_context.clone();
        for (name, id) in &environment.bound_row_context {
            work.text(name)?;
            let row = self
                .bound_rows
                .get(id.0 as usize)
                .filter(|row| row.id == *id)
                .ok_or(SourceTypesError::MissingNode)?;
            let crate::sema::model::rows::RowIdentity::Binder(identity) = &row.identity else {
                return Err(SourceTypesError::Unresolved);
            };
            work.text(identity)?;
            if binders
                .insert(name.clone(), identity.clone())
                .is_some_and(|old| old != *identity)
            {
                return Err(SourceTypesError::Unresolved);
            }
        }
        let schema = self.original_header_source_schema_in(syntax, &binders, work)?;
        Ok(Some((schema, environment)))
    }

    pub(in crate::sema::checker) fn original_source_receiving_schema(
        &mut self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
        work: &mut WorkLimit,
    ) -> InputSource {
        let observation = self
            .application_effect
            .current_activation()
            .and_then(|id| self.application_effect.activations.get(id.0 as usize))
            .filter(|activation| {
                activation.source == syntax.hir_id
                    && activation.context == self.invocation_context(frame.callable_owner)
            })
            .and_then(|activation| activation.result)
            .map(|id| id.0 as usize);
        self.original_source_receiving_schema_at(value, syntax, frame, work, observation)
    }

    pub(in crate::sema::checker) fn original_source_receiving_schema_at(
        &mut self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
        work: &mut WorkLimit,
        observation: Option<usize>,
    ) -> InputSource {
        let source = self.raw_original_source_schema(value, syntax, frame, work, 0, observation)?;
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
        observation: Option<usize>,
    ) -> InputSource {
        work.charge(1)?;
        if depth >= 64 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        if let Some(source) = self.external_static_callee_source(value, syntax, frame, work)? {
            return Ok(Some(source));
        }
        if let Some(source) = self.numeric_static_callee_source(value, syntax, frame, work)? {
            return Ok(Some(source));
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
            return self.closed_witness_input_schema(
                original,
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
            self.original_canonical_builtin_source_schema(value, syntax, frame, observation, work)?
        {
            return Ok(Some(source));
        }
        if let Some(source) = self.original_closure_source_schema(value, work)? {
            return Ok(Some(source));
        }
        if let Some(source) = self.original_named_header_source_schema(value, syntax, work)? {
            return Ok(Some(source));
        }
        if let Some(witness) = &value.source_type_witness {
            if !witness.validate_closed() {
                return Err(SourceTypesError::Unresolved);
            }
            return self.closed_witness_input_schema(
                witness,
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
        }
        if let Some(source) =
            self.original_composite_source_schema(value, syntax, frame, work, depth)?
        {
            return Ok(Some(source));
        }
        Ok(None)
    }

    /// Qualified module references keep their canonical Path node after name
    /// normalization. The original declaration owns their callable header's
    /// interpretation, just as it does for an unqualified Name. Stored public
    /// views have already been handled before entering this declaration path.
    fn original_named_header_source_schema(
        &self,
        value: &Value,
        syntax: &Expr,
        work: &mut WorkLimit,
    ) -> InputSource {
        let name = match &syntax.kind {
            ExprKind::Name(name) => std::borrow::Cow::Borrowed(name.as_str()),
            ExprKind::Path(path) => {
                work.charge(path.len() + 1)?;
                for part in path {
                    work.text(part)?;
                }
                std::borrow::Cow::Owned(path.join("::"))
            }
            _ => return Ok(None),
        };
        let Some(id) = value.sources.first() else {
            return Ok(None);
        };
        let binding = self
            .bindings
            .get(*id)
            .ok_or(SourceTypesError::MissingNode)?;
        work.text(&binding.name)?;
        work.text(&name)?;
        if value.sources.len() != 1 || binding.parameter || binding.name != name.as_ref() {
            return Ok(None);
        }
        let [Callable::Named(index)] = value.callables.as_slice() else {
            return Ok(None);
        };
        let function = self
            .functions
            .get(*index)
            .ok_or(SourceTypesError::MissingNode)?;
        if !function.syntax.generics.is_empty() {
            return Ok(None);
        }
        work.charge(1 + function.syntax.parameters.len() + function.syntax.annotations.len())?;
        work.text(&function.syntax.name)?;
        let declaration = function
            .hir_id
            .and_then(|id| self.semantic_hir.statement(id))
            .ok_or(SourceTypesError::MissingNode)?;
        let crate::hir::nodes::StmtKind::Function(original) = &declaration.kind else {
            return Err(SourceTypesError::Unresolved);
        };
        work.text(&original.name)?;
        if original.name != function.syntax.name
            || original.name != binding.name
            || function.lexical.get(name.as_ref()) != Some(id)
            || original.parameters.len() != function.syntax.parameters.len()
            || original.return_type
                != function
                    .syntax
                    .return_type
                    .as_ref()
                    .and_then(|ty| ty.hir_id)
            || original.annotations.len() != function.syntax.annotations.len()
            || !matches!(binding.value.callables.as_slice(), [Callable::Named(actual)] if actual == index)
        {
            return Err(SourceTypesError::Unresolved);
        }
        let environment = &function.typing_environment;
        let mut parameters = Vec::with_capacity(function.syntax.parameters.len());
        for (parameter, original) in function.syntax.parameters.iter().zip(&original.parameters) {
            let Some(header) = parameter.ty.as_ref() else {
                return Ok(None);
            };
            if header.hir_id != original.ty
                || parameter.pattern.hir_id != Some(original.pattern)
                || parameter.mode != original.mode
            {
                return Err(SourceTypesError::Unresolved);
            }
            let Some((schema, _)) =
                self.input_original_header_schema(header, environment.clone(), work)?
            else {
                return Ok(None);
            };
            parameters.push((parameter.mode, schema));
        }
        let result = if let Some(header) = &function.syntax.return_type {
            let Some((schema, _)) =
                self.input_original_header_schema(header, environment.clone(), work)?
            else {
                return Ok(None);
            };
            schema
        } else {
            SourceSchema::tuple(&[], None, work)?
        };
        let mut annotations = Vec::with_capacity(function.syntax.annotations.len());
        for (annotation, original) in function
            .syntax
            .annotations
            .iter()
            .zip(&original.annotations)
        {
            work.text(&annotation.text)?;
            work.text(&original.text)?;
            if annotation.kind != original.kind || annotation.text != original.text {
                return Err(SourceTypesError::Unresolved);
            }
            annotations.push(annotation.text.replace(' ', ""));
        }
        let schema = SourceSchema::callable(&parameters, &result, &annotations, None, work)?;
        // A nested declaration captures actual generic Source selections at
        // creation. Its original header still names the declaration's UID;
        // applying those selections after composition keeps both every graph
        // edge and the selected view's interpretation intact.
        let required = schema.binder_identities(work)?;
        work.charge(required.len())?;
        let mut replacements = BTreeMap::new();
        let mut dependencies = Vec::with_capacity(required.len());
        for identity in &required {
            work.text(identity)?;
            work.charge(
                1 + environment
                    .generic_sources
                    .len()
                    .checked_ilog2()
                    .unwrap_or(0) as usize,
            )?;
            let Some(source) = environment.generic_sources.get(identity) else {
                continue;
            };
            if source.environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            work.charge(2 + replacements.len().checked_ilog2().unwrap_or(0) as usize)?;
            replacements.insert(identity.clone(), source.schema.clone());
            dependencies.push((&source.schema, &source.environment));
        }
        let selected = schema.substitute(&replacements, work)?;
        let selected_environment = if !selected.requires_environment(work)? {
            environment.clone()
        } else if schema.requires_declaration_environment(work)? {
            producing_result::result_environment(
                dependencies.into_iter().chain([(&schema, environment)]),
                environment,
                work,
            )?
        } else {
            producing_result::result_environment(dependencies, environment, work)?
        };
        Ok(Some((selected, selected_environment)))
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
        let parent = self.source_projection_occurrence(
            syntax.hir_id.ok_or(SourceTypesError::MissingNode)?,
            value,
            context,
            work,
        )?;
        if self
            .source_projection_receipts()
            .child_observation(
                parent,
                application
                    .callee
                    .hir_id
                    .ok_or(SourceTypesError::MissingNode)?,
                work,
            )?
            .0 as usize
            != token
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
        let Some((schema, environment)) = self.raw_original_source_schema(
            &callee,
            application.callee,
            frame,
            work,
            depth + 1,
            Some(token),
        )?
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
