//! Source transport keeps the admitted graph and its declaration environment.
//! Keys enter only at original written headers, never between graph queries.
use super::*;
use crate::sema::source_types::projection_receipts::ProjectionOccurrence;

impl Checker {
    /// A completed application is selected by its actual evaluation record.
    /// Repeated reads and probes can share a cause and lexical context; neither
    /// identifies which execution produced this result.
    pub(super) fn observed_application_result(
        &self,
        syntax: &Expr,
        value: &Value,
        frame: &Frame,
        observation: usize,
        work: &mut WorkLimit,
    ) -> Result<Option<(CopyCallEventId, ProjectionOccurrence)>, SourceTypesError> {
        work.charge(4 + self.copy_call_events.len())?;
        let context = self.invocation_context(frame.callable_owner);
        let physical = self
            .application_effect
            .expressions
            .get(observation)
            .ok_or(SourceTypesError::MissingNode)?;
        let evaluation = self
            .application_effect
            .evaluations
            .get(observation)
            .ok_or(SourceTypesError::MissingNode)?;
        let identity = evaluation.identity.ok_or(SourceTypesError::MissingNode)?;
        if syntax.hir_id.is_none()
            || physical.source_id != syntax.hir_id
            || evaluation.id.0 as usize != observation
            || Some(identity.source) != syntax.hir_id
            || evaluation.context != context
            || evaluation.scope != frame.owner
            || physical.value.cause != value.cause
        {
            return Err(SourceTypesError::Unresolved);
        }
        let mut selected = None;
        for (index, event) in self.copy_call_events.iter().enumerate() {
            if event.result_expression != Some(observation) {
                continue;
            }
            if selected.is_some()
                || event.id.0 as usize != index
                || !event.matches_source(syntax)
                || event.owner != context.owner
                || event.parent != context.invocation
            {
                return Err(SourceTypesError::Unresolved);
            }
            selected = Some(event.id);
        }
        Ok(selected.map(|event| {
            (
                event,
                ProjectionOccurrence {
                    identity,
                    context,
                    cause: physical.value.cause,
                },
            )
        }))
    }

    // The remaining finite closed-witness adapter has its own admission rule.
    // A witness is not an original HIR header, and must not bypass that
    // header's identity checks by presenting a missing or normalized ID.
    fn closed_witness_input_schema(
        &self,
        witness: &SourceTypeWitness,
        environment: FrozenEnvironment,
        work: &mut WorkLimit,
    ) -> InputSource {
        let mut remaining = work.remaining();
        let before = remaining;
        let valid = witness.validate_closed_with_work(&mut remaining);
        work.charge(before - remaining)?;
        if !valid.ok_or(SourceTypesError::BudgetExceeded)? {
            return Err(SourceTypesError::Unresolved);
        }
        let before = remaining;
        let admitted =
            crate::static_eval::charge_type_syntax_clone(&witness.syntax, &mut remaining);
        work.charge(before - remaining)?;
        admitted.ok_or(SourceTypesError::BudgetExceeded)?;
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
        let binders = self.original_captured_header_binders(&environment, work)?;
        let schema = self.original_header_source_schema_in(syntax, &binders, work)?;
        Ok(Some((schema, environment)))
    }

    pub(in crate::sema::checker) fn original_captured_header_binders(
        &self,
        environment: &FrozenEnvironment,
        work: &mut WorkLimit,
    ) -> Result<BTreeMap<String, String>, SourceTypesError> {
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
        Ok(binders)
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

    pub(in crate::sema::checker) fn input_header_schema(
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
        if matches!(
            &syntax.kind,
            ExprKind::Control {
                operation: ControlOperation::Resume,
                ..
            }
        ) {
            // The transfer occurrence is distinct from the computation's
            // completed answer; only the latter can supply an answer Source.
            return Ok(None);
        }
        if matches!(syntax.kind, ExprKind::Block(_))
            && let Some(source) =
                self.original_block_source_schema(value, syntax, frame, work, observation)?
        {
            return Ok(Some(source));
        }
        if let Some(source) = self.external_static_callee_source(value, syntax, frame, work)? {
            return Ok(Some(source));
        }
        if let Some(source) = self.numeric_static_callee_source(value, syntax, frame, work)? {
            return Ok(Some(source));
        }
        if let Some(source) =
            self.original_key_name_source_schema(value, syntax, frame, observation, work)?
        {
            return Ok(Some(source));
        }
        if let ExprKind::Generic { base, arguments } = &syntax.kind
            && matches!(value.callables.as_slice(), [Callable::Named(_)])
        {
            // An ordinary explicit prefix prepares the application's static
            // arguments; it does not replace the callable's public value or
            // its original header. Keep that Source at the real base read.
            // The application separately authenticates its selected arguments.
            let root = observation.ok_or(SourceTypesError::MissingNode)?;
            work.charge(3 + arguments.len())?;
            let fact = self
                .application_effect
                .expressions
                .get(root)
                .ok_or(SourceTypesError::MissingNode)?;
            let record = self
                .application_effect
                .evaluations
                .get(root)
                .ok_or(SourceTypesError::MissingNode)?;
            let identity = record.identity.ok_or(SourceTypesError::MissingNode)?;
            let context = self.invocation_context(frame.callable_owner);
            let original = self
                .semantic_hir
                .expression(identity.source)
                .ok_or(SourceTypesError::MissingNode)?;
            let crate::hir::nodes::ExprKind::Generic {
                base: original_base,
                arguments: original_arguments,
            } = &original.kind
            else {
                return Err(SourceTypesError::Unresolved);
            };
            if Some(identity.source) != syntax.hir_id
                || fact.source_id != syntax.hir_id
                || record.context != context
                || Some(*original_base) != base.hir_id
                || original_arguments.len() != arguments.len()
                || arguments
                    .iter()
                    .zip(original_arguments)
                    .any(|(actual, original)| actual.hir_id != Some(*original))
            {
                return Err(SourceTypesError::Unresolved);
            }
            let parent = ProjectionOccurrence {
                identity,
                context,
                cause: fact.value.cause,
            };
            let child = self
                .source_projection_receipts()
                .child_observation(parent, *original_base, work)?
                .0 as usize;
            let actual = &self.application_effect.expressions[child];
            let mut remaining = work.remaining();
            let agrees =
                crate::sema::evaluated::same_birth_value(&fact.value, value, &mut remaining)
                    .and_then(|agrees| {
                        if agrees {
                            crate::sema::evaluated::same_birth_value(
                                &actual.value,
                                value,
                                &mut remaining,
                            )
                        } else {
                            Ok(false)
                        }
                    });
            work.charge(work.remaining() - remaining)?;
            if !agrees? {
                return Err(SourceTypesError::Unresolved);
            }
            work.charge(1)?;
            let input = actual.value.packet().clone();
            return self.raw_original_source_schema(
                input.value(),
                base,
                frame,
                work,
                depth + 1,
                Some(child),
            );
        }
        if let Some(source) = self.storage_binding_source_schema(value, syntax, frame) {
            return source;
        }
        // Finite closed witnesses retain their separate existing admission.
        // A uniform branch derivation supplies the missing open graph view.
        if value.source_type_witness.is_none()
            && let Some(root) = observation
        {
            let inputs = crate::sema::control_sources::contributors(
                &self.semantic_hir,
                &self.source_projection_receipts(),
                ril_compiler_core::ids::EvaluationOccurrenceId(root as u32),
                work,
            )?;
            if let Some(inputs) = inputs {
                let mut selected: Option<(SourceSchema, FrozenEnvironment)> = None;
                for input in inputs {
                    let input = self
                        .application_effect
                        .expressions
                        .get(input.0 as usize)
                        .ok_or(SourceTypesError::MissingNode)?
                        .value
                        .packet();
                    let Some(source) = input
                        .input_source(
                            SourceTypesRef::Live(self.type_source.storage.live_types()),
                            work,
                        )?
                        .into_known()
                    else {
                        // This operation only derives uniform complete
                        // views; other existing ingress remains separate.
                        return Ok(None);
                    };
                    if crate::sema::control_sources::never(&source.0, work)? {
                        continue;
                    }
                    if let Some((schema, environment)) = &selected {
                        if !schema.equivalent_in(&source.0, environment, &source.1, work)? {
                            return Err(SourceTypesError::Unresolved);
                        }
                    } else {
                        selected = Some(source);
                    }
                }
                return Ok(selected);
            }
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
            && let Some(reference) = self.constant_pool.references.get(name).copied()
        {
            if let Some(original) = self.constant_pool.source_views.get(name) {
                let source = self.closed_witness_input_schema(
                    original,
                    self.capture_typing_environment(),
                    work,
                )?;
                if let Some(actual) = &value.source_type_witness {
                    work.text(&actual.key)?;
                }
                if value.source_type_witness.as_ref() != Some(original) {
                    return Err(SourceTypesError::Unresolved);
                }
                return Ok(source);
            }
            if value.source_type_witness.is_some() {
                return Err(SourceTypesError::Unresolved);
            }
            return crate::sema::source_types::constants::literal_schema(
                &self.constant_pool,
                reference,
                work,
            )
            .map(|source| source.map(|schema| (schema, self.capture_typing_environment())));
        }
        if let Some(source) = self.original_carrier_source_schema(value, syntax, frame, work) {
            return source;
        }
        if let Some(source) = self.original_called_result_schema(value, syntax, frame, work)? {
            return Ok(Some(source));
        }
        if let Some(source) =
            self.original_constructor_result_schema(value, syntax, frame, work, observation)?
        {
            return Ok(Some(source));
        }
        if let Some(source) =
            self.original_public_result_schema(value, syntax, frame, work, depth, observation)?
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
        if let Some(source) = self.original_closure_source_schema(
            value,
            matches!(syntax.kind, ExprKind::Lambda { .. }),
            work,
        )? {
            return Ok(Some(source));
        }
        if let Some(source) = self.original_named_header_source_schema(value, syntax, work)? {
            return Ok(Some(source));
        }
        if let Some(witness) = &value.source_type_witness {
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

    fn original_block_source_schema(
        &mut self,
        _value: &Value,
        syntax: &Expr,
        _frame: &Frame,
        work: &mut WorkLimit,
        observation: Option<usize>,
    ) -> InputSource {
        let Some(observation) = observation else {
            return Ok(None);
        };
        work.charge(1)?;
        let packet = self.application_effect.packet_at(observation)?;
        if packet.identity.map(|identity| identity.source) != syntax.hir_id {
            return Err(SourceTypesError::Unresolved);
        }
        self.owned_result_type(&packet, work)
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
        work.charge(
            1 + function.syntax.parameters.len()
                + function.syntax.annotations.len()
                + function.syntax.generics.len(),
        )?;
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
            || binding.declaration.is_none()
            || binding.declaration != function.hir_id
            || function.lexical.get(name.as_ref()) != Some(id)
            || original.parameters.len() != function.syntax.parameters.len()
            || original.return_type
                != function
                    .syntax
                    .return_type
                    .as_ref()
                    .and_then(|ty| ty.hir_id)
            || original.annotations.len() != function.syntax.annotations.len()
            || original.generics.len() != function.syntax.generics.len()
            || !matches!(binding.value.callables.as_slice(), [Callable::Named(actual)] if actual == index)
        {
            return Err(SourceTypesError::Unresolved);
        }
        let environment = &function.typing_environment;
        if environment.is_poisoned() {
            return Err(SourceTypesError::Unresolved);
        }
        work.charge(
            environment.generic_context.len()
                + self.generic_binders.len()
                + environment.bound_row_context.len()
                + self.bound_rows.len(),
        )?;
        let mut binders = BTreeMap::new();
        for (name, identity) in &environment.generic_context {
            work.text(name)?;
            work.text(identity)?;
            work.charge(4 + 2 * binders.len().checked_ilog2().unwrap_or(0) as usize)?;
            binders.insert(name.clone(), identity.clone());
            // Keep an enclosing UID available when an inner parameter shadows
            // its spelling. The canonical GenericParamId still chooses it.
            binders.insert(identity.clone(), identity.clone());
        }
        let mut owned = BTreeMap::new();
        for (identity, binder) in &self.generic_binders {
            if binder.definition == function.definition {
                work.text(identity)?;
                work.text(&binder.identity)?;
                work.charge(2 + owned.len().checked_ilog2().unwrap_or(0) as usize)?;
                if identity != &binder.identity || owned.insert(binder.index, binder).is_some() {
                    return Err(SourceTypesError::Unresolved);
                }
            }
        }
        if owned.len() != function.syntax.generics.len() {
            return Err(SourceTypesError::Unresolved);
        }
        for (ordinal, (parameter, original_id)) in function
            .syntax
            .generics
            .iter()
            .zip(&original.generics)
            .enumerate()
        {
            work.charge(3 + owned.len().checked_ilog2().unwrap_or(0) as usize)?;
            let canonical = self
                .semantic_hir
                .generic(*original_id)
                .ok_or(SourceTypesError::MissingNode)?;
            let binder = owned
                .get(&(ordinal as u32))
                .ok_or(SourceTypesError::MissingNode)?;
            work.text(&parameter.name)?;
            work.text(&canonical.name)?;
            work.text(&binder.name)?;
            work.text(&binder.identity)?;
            if parameter.hir_id != Some(*original_id)
                || canonical.info.owner
                    != crate::hir::nodes::LexicalOwner::Declaration(
                        function.hir_id.ok_or(SourceTypesError::MissingNode)?,
                    )
                || parameter.name != canonical.name
                || binder.name != parameter.name
            {
                return Err(SourceTypesError::Unresolved);
            }
            work.charge(2 + binders.len().checked_ilog2().unwrap_or(0) as usize)?;
            binders.insert(parameter.name.clone(), binder.identity.clone());
        }
        for row in &self.bound_rows {
            work.text(&row.name)?;
            work.charge(
                (1 + row.name.len().div_ceil(32))
                    * (1 + environment
                        .bound_row_context
                        .len()
                        .checked_ilog2()
                        .unwrap_or(0) as usize),
            )?;
            if row.definition == function.definition
                || environment.bound_row_context.get(&row.name) == Some(&row.id)
            {
                let crate::sema::model::rows::RowIdentity::Binder(identity) = &row.identity else {
                    return Err(SourceTypesError::Unresolved);
                };
                work.text(&row.name)?;
                work.text(identity)?;
                work.charge(2 + binders.len().checked_ilog2().unwrap_or(0) as usize)?;
                if binders
                    .insert(row.name.clone(), identity.clone())
                    .is_some_and(|previous| previous != *identity)
                {
                    return Err(SourceTypesError::Unresolved);
                }
            }
        }
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
            let schema = self.original_header_source_schema_in(header, &binders, work)?;
            parameters.push((parameter.mode, schema));
        }
        let result = if let Some(header) = &function.syntax.return_type {
            self.original_header_source_schema_in(header, &binders, work)?
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
            annotations.push(annotation.text.clone());
        }
        let row = self.original_callable_row_identity(
            crate::sema::source_types::CallableRowOrigin::Declaration(
                function.hir_id.ok_or(SourceTypesError::MissingNode)?,
            ),
            &function.syntax.annotations,
            &binders,
            work,
        )?;
        let schema = SourceSchema::callable_original(
            &parameters,
            &result,
            &annotations,
            row.as_ref(),
            None,
            work,
        )?;
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
            if let Some(binder) = self.generic_binders.get(identity) {
                work.charge(self.functions.len() + self.record_bounds.len())?;
                let parameter = self
                    .functions
                    .iter()
                    .find(|function| function.definition == binder.definition)
                    .and_then(|function| function.syntax.generics.get(binder.index as usize))
                    .ok_or(SourceTypesError::Unresolved)?;
                work.text(&binder.name)?;
                work.text(&parameter.name)?;
                if !crate::sema::record_bounds::certifies_type_sort(
                    identity,
                    binder,
                    parameter,
                    &self.record_bounds,
                ) {
                    return Err(SourceTypesError::Unresolved);
                }
            } else {
                work.charge(self.bound_rows.len())?;
                if !self.bound_rows.iter().any(|row| matches!(&row.identity, crate::sema::model::rows::RowIdentity::Binder(actual) if actual == identity)) {
                    return Err(SourceTypesError::Unresolved);
                }
            }
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
        observation: Option<usize>,
    ) -> InputSource {
        let Some(application) = crate::hir::application::AstApplication::from_ast(syntax) else {
            return Ok(None);
        };
        let context = self.invocation_context(frame.callable_owner);
        let root = observation.ok_or(SourceTypesError::MissingNode)?;
        let Some((event, parent)) =
            self.observed_application_result(syntax, value, frame, root, work)?
        else {
            return Ok(None);
        };
        let event = self
            .copy_call_events
            .get(event.0 as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        work.charge(self.call_arguments.len())?;
        let mut preparations = self
            .call_arguments
            .iter()
            .filter(|row| row.source_event == event.id);
        let preparation = preparations.next().ok_or(SourceTypesError::MissingNode)?;
        if preparations.next().is_some() {
            return Err(SourceTypesError::Unresolved);
        }
        // A public return contract describes a normally completed application.
        // The evaluation ledger independently checks this completion against
        // every actual prefix/default root. A default which exits before body
        // entry cannot manufacture the callee's normal result Source.
        if !preparation.evaluation_complete {
            return Ok(None);
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
        work.charge(1)?;
        let callee = callee.value.packet().clone();
        let Some((schema, environment)) = self.raw_original_source_schema(
            callee.value(),
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

#[cfg(test)]
mod application_result_tests {
    use super::*;

    #[test]
    fn closed_witness_ingress_charges_before_validation_and_key_construction() {
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 0,
        };
        let scalar = TypeExpr {
            hir_id: None,
            text: String::new(),
            span,
            kind: TypeKind::Name {
                path: vec!["int".into()],
                arguments: vec![],
            },
        };
        let syntax = TypeExpr {
            hir_id: None,
            text: String::new(),
            span,
            kind: TypeKind::Tuple(vec![scalar; 1024]),
        };
        let mut witness = SourceTypeWitness {
            key: crate::static_eval::normalized_argument_key(&syntax),
            syntax,
        };
        let checker = Checker::new(FileId(0));
        let environment = FrozenEnvironment::default();
        let mut work = WorkLimit::new(4_000_000);
        checker
            .closed_witness_input_schema(&witness, environment.clone(), &mut work)
            .unwrap()
            .unwrap();
        let used = 4_000_000 - work.remaining();
        let mut exact = WorkLimit::new(used);
        checker
            .closed_witness_input_schema(&witness, environment.clone(), &mut exact)
            .unwrap()
            .unwrap();
        assert_eq!(exact.remaining(), 0);
        for budget in [0, used - 1] {
            assert!(matches!(
                checker.closed_witness_input_schema(
                    &witness,
                    environment.clone(),
                    &mut WorkLimit::new(budget)
                ),
                Err(SourceTypesError::BudgetExceeded)
            ));
        }
        witness.key.push('x');
        assert!(matches!(
            checker.closed_witness_input_schema(
                &witness,
                environment.clone(),
                &mut WorkLimit::new(0)
            ),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert!(matches!(
            checker.closed_witness_input_schema(
                &witness,
                environment,
                &mut WorkLimit::new(4_000_000)
            ),
            Err(SourceTypesError::Unresolved)
        ));
    }
}
