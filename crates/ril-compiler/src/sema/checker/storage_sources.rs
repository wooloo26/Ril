//! Immutable declaration views and physical receipts for storage reception.
//! The current value of a mutable binding is never its declaration schema.
use super::*;
use crate::sema::source_types::{
    SourceSchema, SourceTypesError, WorkLimit,
    projection_receipts::{self, ProjectionOccurrence, ProjectionReceipts, SourceRead},
};
use crate::sema::{
    context::FrozenEnvironment,
    source_reception,
    storage_sources::{BindingSource, StorageDestination, StorageObservation, StorageWrite},
};
type BindingSchema =
    Result<Option<(SourceSchema, crate::sema::context::FrozenEnvironment)>, SourceTypesError>;

#[derive(Default)]
pub(super) struct State {
    bindings: Vec<BindingSource>,
    writes: Vec<StorageWrite>,
    by_binding: BTreeMap<BindingId, usize>,
    types: crate::sema::source_types::LiveSourceTypes,
}

impl State {
    pub(super) fn declared_operand_source_schema(
        &self,
        syntax: &Expr,
        env: &Env,
        work: &mut WorkLimit,
    ) -> BindingSchema {
        let mut path = Vec::new();
        let mut budget = work.remaining();
        let name = source_path(syntax, &mut path, &mut budget);
        work.charge(work.remaining() - budget)?;
        let Some(name) = name else { return Ok(None) };
        let Some(binding) = env.get(name) else {
            return Ok(None);
        };
        let Some((schema, environment)) =
            self.types.binding_schema_if_known(*binding, None, work)?
        else {
            return Ok(None);
        };
        let steps = crate::sema::source_types::steps_in(&path, work)?;
        schema
            .project_steps_if_structural(&steps, work)
            .map(|schema| schema.map(|schema| (schema, environment)))
    }
    pub(super) fn live_types(&self) -> &crate::sema::source_types::LiveSourceTypes {
        &self.types
    }

    pub(super) fn live_types_mut(&mut self) -> &mut crate::sema::source_types::LiveSourceTypes {
        &mut self.types
    }

    pub(super) fn into_parts(
        self,
    ) -> (
        Vec<BindingSource>,
        Vec<StorageWrite>,
        crate::sema::source_types::SourceTypeIndex,
    ) {
        (self.bindings, self.writes, self.types.freeze())
    }
}

pub(super) struct PreparedBindingSource {
    context: crate::sema::effect_identity::InvocationContext,
    activation: ScopeId,
    root: Option<crate::sema::source_types::SourceSchema>,
    environment: crate::sema::context::FrozenEnvironment,
}

pub(super) struct StoreReception<'a> {
    pub target: &'a Expr,
    pub operator: &'a str,
    pub rhs_syntax: &'a Expr,
    pub rhs: StorageObservation,
    pub destination: StorageDestination,
    pub receiver: Option<&'a Value>,
}

impl Checker {
    pub(super) fn intern_source_schema(
        &mut self,
        schema: &SourceSchema,
        environment: FrozenEnvironment,
        work: &mut WorkLimit,
    ) -> Result<crate::sema::source_types::SourceView, SourceTypesError> {
        self.type_source
            .storage
            .types
            .intern_schema(schema, environment, work)
    }

    pub(super) fn source_schema_view(
        &self,
        view: crate::sema::source_types::SourceView,
        work: &mut WorkLimit,
    ) -> Result<(SourceSchema, FrozenEnvironment), SourceTypesError> {
        self.type_source.storage.types.view_schema(view, None, work)
    }

    pub(super) fn parameter_source_schema_if_known(
        &self,
        binding: BindingId,
        original: Option<ril_compiler_core::ids::TypeExprId>,
        work: &mut WorkLimit,
    ) -> BindingSchema {
        self.type_source
            .storage
            .types
            .binding_schema_if_known(binding, original, work)
    }
    pub(super) fn record_parameter_source(&mut self, binding: BindingId, name: &str, span: Span) {
        match self.preparation_formal_source(binding) {
            Ok(Some((schema, environment))) => {
                if let Err(error) = self.type_source.storage.types.record_schema(
                    binding,
                    Some(&schema),
                    environment,
                ) {
                    self.unsupported(
                        span,
                        format!("preparation formal Source admission failed: {error}"),
                    );
                }
                return;
            }
            Ok(None) => {}
            Err(error) => {
                self.unsupported(
                    span,
                    format!("preparation formal declaration Source failed: {error}"),
                );
                return;
            }
        }
        if let Some(source) = self.inferred_closure_parameter_source(binding, name) {
            let (schema, environment) = match source {
                Ok(Some((schema, environment))) => (Some(schema), environment),
                Ok(None) => (None, self.bindings[binding].typing_environment.clone()),
                Err(error) => {
                    self.unsupported(
                        span,
                        format!("inferred closure parameter lost its actual Source: {error}"),
                    );
                    return;
                }
            };
            if let Err(error) =
                self.type_source
                    .storage
                    .types
                    .record_schema(binding, schema.as_ref(), environment)
            {
                self.unsupported(
                    span,
                    format!("inferred closure parameter graph admission failed: {error}"),
                );
            }
            return;
        }
        let environment = self.bindings[binding].typing_environment.clone();
        let named = self
            .scopes
            .get(&self.bindings[binding].owner)
            .is_some_and(|scope| {
                matches!(scope.origin, crate::sema::scopes::ScopeOrigin::Named(_))
            });
        let universal = matches!(
            self.bindings[binding].context.owner,
            Some(CallableOwner::Function(_))
        ) && self.bindings[binding].context.invocation.is_none()
            && self
                .scopes
                .get(&self.bindings[binding].owner)
                .is_some_and(|scope| {
                    matches!(scope.origin, crate::sema::scopes::ScopeOrigin::Unresolved)
                });
        if named || universal {
            let mut stage = "original parameter declaration";
            let schema = match self
                .parameter_declaration_source_schema(binding, name, named, &mut stage)
            {
                Ok(schema) => schema,
                Err(error) => {
                    let original = &self.bindings[binding];
                    self.unsupported(
                        span,
                        format!("named parameter lost its original declaration graph: {error}; stage={stage}, binding={binding}, context={:?}, scope={:?}, declaration_environment={:?}, active_invocation={:?}, active_default={:?}", original.context, original.owner, original.typing_environment.id(), self.copy_invocation_stack.last(), self.default_use_stack.last()),
                    );
                    return;
                }
            };
            if let Err(error) =
                self.type_source
                    .storage
                    .types
                    .record_schema(binding, schema.as_ref(), environment)
            {
                self.unsupported(
                    span,
                    format!("parameter Source graph admission failed: {error}"),
                );
            }
            return;
        }
        let schema =
            self.formal_binding_declaration(binding, name)
                .and_then(|(syntax, environment)| {
                    self.with_typing_environment(&environment, |checker| {
                        checker.freeze_source_receiving_target(&syntax).schema
                    })
                });
        if self
            .type_source
            .storage
            .types
            .record_schema(binding, schema.as_ref(), environment)
            .is_err()
        {
            self.unsupported(span, "parameter source view exceeded its metadata budget");
        }
    }

    fn parameter_declaration_source_schema(
        &mut self,
        binding: BindingId,
        name: &str,
        actual_named_entry: bool,
        stage: &mut &'static str,
    ) -> Result<Option<SourceSchema>, SourceTypesError> {
        use crate::sema::effect_identity::ArgumentKey;
        let Some((syntax, environment)) = self.formal_binding_declaration(binding, name) else {
            return Ok(None);
        };
        *stage = "original parameter environment";
        if environment.is_poisoned()
            || environment.id() != self.bindings[binding].typing_environment.id()
        {
            return Err(SourceTypesError::Unresolved);
        }
        self.with_typing_environment(&environment, |checker| {
            let mut work = WorkLimit::new(16384);
            work.charge(
                checker.type_source.environment.generic_context.len()
                    + checker.type_source.environment.bound_row_context.len(),
            )?;
            let scope = checker.record_bound_scope();
            *stage = "original parameter key";
            let key = checker
                .record_bound_key(&syntax, &scope)
                .ok_or(SourceTypesError::BudgetExceeded)?;
            let mut pending = vec![&key];
            let mut has_binder = false;
            *stage = "original parameter binder identity";
            while let Some(part) = pending.pop() {
                work.charge(1)?;
                match part {
                    ArgumentKey::Binder { identity, .. } => {
                        work.charge(identity.len().div_ceil(32))?;
                        if let Some(binder) = checker.generic_binders.get(identity) {
                            work.charge(checker.functions.len())?;
                            let parameter = checker
                                .functions
                                .iter()
                                .find(|function| function.definition == binder.definition)
                                .and_then(|function| function.syntax.generics.get(binder.index as usize))
                                .ok_or(SourceTypesError::Unresolved)?;
                            if !crate::sema::record_bounds::certifies_type_sort(
                                identity,
                                binder,
                                parameter,
                                &checker.record_bounds,
                            ) {
                                // A Key remains a static coordinate sort. Its
                                // run-time argument nevertheless has the scalar
                                // carrier certified by this original header.
                                if matches!(parameter.bound.as_ref().map(|bound| &bound.kind), Some(TypeKind::KeyOf(_))) {
                                    continue;
                                }
                                return Ok(None);
                            }
                        } else {
                            work.charge(scope.rows.len())?;
                            if !scope.rows.values().any(|id| {
                                checker.bound_rows.get(id.0 as usize).is_some_and(|row| {
                                    row.id == *id && matches!(&row.identity,
                                        crate::sema::model::rows::RowIdentity::Binder(actual) if actual == identity)
                                })
                            }) {
                                return Err(SourceTypesError::Unresolved);
                            }
                        }
                        has_binder = true;
                    }
                    ArgumentKey::Name { arguments, .. } | ArgumentKey::Tuple(arguments) => {
                        work.charge(arguments.len())?;
                        pending.extend(arguments);
                    }
                    ArgumentKey::Array { element, .. } => {
                        work.charge(1)?;
                        pending.push(element);
                    }
                    ArgumentKey::Map { key, value } => {
                        work.charge(2)?;
                        pending.extend([&**key, &**value]);
                    }
                    ArgumentKey::Record { fields, row } => {
                        work.charge(fields.len() + usize::from(row.is_some()))?;
                        pending.extend(fields.iter().map(|field| &field.2));
                        pending.extend(row.as_deref());
                    }
                    ArgumentKey::Callable { parameters, result, .. } => {
                        work.charge(parameters.len() + 1)?;
                        pending.extend(parameters.iter().map(|parameter| &parameter.1));
                        pending.push(result);
                    }
                    ArgumentKey::Closed(_) | ArgumentKey::GenericBuiltin(_) => {}
                }
            }
            let schema = if has_binder && actual_named_entry {
                *stage = "actual named receiver identity";
                let owner = checker.bindings[binding]
                    .context
                    .owner
                    .ok_or(SourceTypesError::Unresolved)?;
                let CallableOwner::Function(definition) = owner else {
                    return Err(SourceTypesError::Unresolved);
                };
                let invocation = checker.bindings[binding]
                    .context
                    .invocation
                    .ok_or(SourceTypesError::Unresolved)?;
                if checker.copy_invocation_stack.last() != Some(&invocation) {
                    return Err(SourceTypesError::Unresolved);
                }
                let call = checker
                    .copy_invocations
                    .get(invocation.0 as usize)
                    .filter(|call| call.id == invocation && call.target == definition)
                    .ok_or(SourceTypesError::Unresolved)?;
                let (event, span) = (call.source_event, call.span);
                work.charge(
                    checker.functions.len()
                        + checker.scoped_source_identities.len()
                        + checker.generic_bound_checks.len(),
                )?;
                // The actual selection can come from a nested product's
                // independently recorded scoped identity. An erased ordinary
                // substitution never reconstructs its missing Source.
                *stage = "actual named selected Source graphs";
                let actual = checker.actual_input_source_schemas(definition,event,span,&mut work)?;
                *stage = "actual named original HIR header";
                let header = checker.original_owned_header_source_schema(&syntax,definition,&environment,&mut work)?;
                *stage = "actual named Source substitution";
                header.substitute(&actual,&mut work)?
            } else {
                *stage = "universal original HIR header";
                // A universal header has genuine rigid Type UIDs, but no
                // application whose selected arguments could replace them.
                // Both cases enter through the original HIR header and its
                // frozen interpretation; an erased parameter Ty is not input.
                let Some(CallableOwner::Function(definition)) = checker.bindings[binding].context.owner else {
                    return Err(SourceTypesError::Unresolved);
                };
                checker.original_owned_header_source_schema(
                    &syntax,definition,&environment,&mut work,
                )?
            };
            *stage = "original parameter declaration resolution";
            crate::sema::source_types::declarations::resolve_schema(
                &schema,
                &checker.semantic_hir,
                &mut work,
            )
            .map(Some)
        })
    }

    pub(super) fn prepare_storage_binding_source(
        &mut self,
        binding: &Binding,
        target: Option<&source_reception::Target>,
        initializer: StorageObservation,
        frame: &Frame,
    ) -> PreparedBindingSource {
        let context = self.invocation_context(frame.callable_owner);
        let mut environment = target
            .map(|target| target.environment.clone())
            .unwrap_or_else(|| self.capture_typing_environment_with_bindings(&frame.env));
        let mut work = crate::sema::source_types::WorkLimit::new(16384);
        let original = self
            .application_effect
            .expressions
            .get(initializer.expression)
            .map(|fact| fact.value.packet());
        let original = match work.charge(1) {
            Ok(()) => original.cloned(),
            Err(error) => {
                self.unsupported(
                    binding.value.span,
                    format!("binding physical packet borrow: {error}"),
                );
                None
            }
        };
        let root = if let Some(target) = target {
            match target
                .schema
                .as_ref()
                .map(|schema| {
                    crate::sema::source_types::declarations::resolve_schema(
                        schema,
                        &self.semantic_hir,
                        &mut work,
                    )
                })
                .transpose()
            {
                Ok(schema) => schema,
                Err(_) => {
                    self.unsupported(
                        binding.value.span,
                        "storage receiving graph could not retain its original declaration",
                    );
                    None
                }
            }
        } else if let Some(source) = original.as_ref().and_then(|original| {
            self.storage_binding_source_schema_view(
                original.value(),
                &binding.value,
                frame,
                SourceRead::Received,
            )
        }) {
            match source {
                Ok(Some((schema, captured))) => {
                    environment = captured;
                    Some(schema)
                }
                Ok(None) => None,
                Err(_) => {
                    self.unsupported(
                        binding.value.span,
                        "storage input lost its original Source graph or work budget",
                    );
                    None
                }
            }
        } else {
            original.as_ref().and_then(|original| {
                match self.original_source_receiving_schema_at(
                    original.value(),
                    &binding.value,
                    frame,
                    &mut work,
                    Some(initializer.expression),
                ) {
                    Ok(Some((schema, captured))) => {
                        environment = captured;
                        Some(schema)
                    }
                    Ok(None) => None,
                    Err(error) => {
                        self.unsupported(
                            binding.value.span,
                            format!("storage input Source graph could not be admitted: {error}"),
                        );
                        None
                    }
                }
            })
        };
        PreparedBindingSource {
            context,
            activation: frame.owner,
            root,
            environment,
        }
    }

    pub(super) fn record_storage_binding_sources(
        &mut self,
        binding: &Binding,
        prepared: &PreparedBindingSource,
        initializer: StorageObservation,
        start: usize,
        frame: &Frame,
    ) {
        let context = prepared.context;
        let root = &prepared.root;
        let Some(declaration) = binding.pattern.hir_id else {
            self.unsupported(
                binding.pattern.span,
                "storage declaration has no original PatternId",
            );
            return;
        };
        if prepared.activation != frame.owner
            || context != self.invocation_context(frame.callable_owner)
        {
            self.unsupported(
                binding.pattern.span,
                "storage declaration changed its original elaboration context",
            );
            return;
        }
        let mut plan_work = 16384usize;
        let plan = match self
            .semantic_hir
            .pattern_bindings(declaration, &mut plan_work)
        {
            Ok(plan) => plan,
            Err(_) => {
                self.unsupported(
                    binding.pattern.span,
                    "storage declaration lost its bounded original HIR binding plan",
                );
                return;
            }
        };
        let Some(_) = plan_work.checked_sub(plan.len().saturating_mul(3)) else {
            self.unsupported(
                binding.pattern.span,
                "storage binding plan index exceeds its work bound",
            );
            return;
        };
        let mut plans = BTreeMap::<_, BTreeMap<_, _>>::new();
        for site in plan {
            plans
                .entry(site.pattern)
                .or_default()
                .insert(site.name, site.projection);
        }
        for id in start..self.bindings.len() {
            let actual = &self.bindings[id];
            if actual.parameter || actual.owner != frame.owner {
                continue;
            }
            let selected = actual
                .pattern
                .and_then(|pattern| plans.get_mut(&pattern))
                .and_then(|names| names.remove(actual.name.as_str()));
            let Some(path) = selected else {
                self.unsupported(
                    binding.pattern.span,
                    "storage binding has no original HIR introducer",
                );
                continue;
            };
            let schema = match root
                .as_ref()
                .zip(path.as_ref())
                .map(|(root, path)| {
                    root.project_steps(path, &mut crate::sema::source_types::WorkLimit::new(16384))
                })
                .transpose()
            {
                Ok(schema) => schema,
                Err(_) => {
                    self.unsupported(
                        binding.pattern.span,
                        "storage projection lost its original Source graph or work budget",
                    );
                    None
                }
            };
            self.bindings[id].typing_environment = prepared.environment.clone();
            self.type_source
                .storage
                .by_binding
                .insert(id, self.type_source.storage.bindings.len());
            if self
                .type_source
                .storage
                .types
                .record_schema(id, schema.as_ref(), prepared.environment.clone())
                .is_err()
            {
                self.unsupported(
                    binding.pattern.span,
                    "storage source graph admission exceeded its metadata budget",
                );
            }
            self.type_source.storage.bindings.push(BindingSource {
                binding: id,
                context,
                activation: frame.owner,
                declaration,
                declared: binding.ty.is_some(),
                initializer,
                path,
            });
        }
    }

    /// A real declaration graph is transported without exporting a legacy
    /// tree. Its frozen interpretation follows the graph through aliases.
    pub(super) fn storage_binding_source_schema(
        &self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
    ) -> Option<BindingSchema> {
        self.storage_binding_source_schema_view(value, syntax, frame, SourceRead::Raw)
    }

    pub(super) fn source_projection_receipts(&self) -> ProjectionReceipts<'_> {
        ProjectionReceipts {
            activations: &self.application_effect.activations,
            evaluations: &self.application_effect.evaluations,
            expressions: &self.application_effect.expressions,
            witnesses: &self.invocation_witnesses,
            explanations: &self.explanations,
            open: self.application_effect.current_activation(),
        }
    }

    pub(super) fn source_projection_occurrence(
        &self,
        source: ril_compiler_core::ids::ExprId,
        value: &Value,
        context: crate::sema::effect_identity::InvocationContext,
        work: &mut WorkLimit,
    ) -> Result<ProjectionOccurrence, SourceTypesError> {
        for &index in self
            .application_effect
            .occurrences(source, context)
            .iter()
            .rev()
        {
            work.charge(1)?;
            let fact = self
                .application_effect
                .expressions
                .get(index)
                .ok_or(SourceTypesError::MissingNode)?;
            let record = self
                .application_effect
                .evaluations
                .get(index)
                .ok_or(SourceTypesError::MissingNode)?;
            let identity = record.identity.ok_or(SourceTypesError::MissingNode)?;
            let activation = self
                .application_effect
                .activations
                .get(identity.activation.0 as usize)
                .ok_or(SourceTypesError::MissingNode)?;
            if fact.value.cause == value.cause
                && activation.kind == crate::sema::application_effect::ActivationKind::Expression
                && identity.source == source
                && record.context == context
            {
                return Ok(ProjectionOccurrence {
                    identity,
                    context,
                    cause: value.cause,
                });
            }
        }
        Err(SourceTypesError::MissingNode)
    }

    fn storage_binding_source_schema_view(
        &self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
        view: SourceRead,
    ) -> Option<BindingSchema> {
        if value.sources.len() != 1 {
            return None;
        }
        let id = *value.sources.first()?;
        let named_parameter = self.bindings.get(id).is_some_and(|binding| {
            binding.parameter
                && matches!(binding.context.owner, Some(CallableOwner::Function(_)))
                && self.scopes.get(&binding.owner).is_some_and(|scope| {
                    matches!(scope.origin, crate::sema::scopes::ScopeOrigin::Named(invocation)
                        if binding.context.invocation == Some(invocation))
                })
        });
        let parameter = self
            .bindings
            .get(id)
            .is_some_and(|binding| binding.parameter);
        if !parameter && !self.type_source.storage.by_binding.contains_key(&id) {
            return None;
        }
        let source = syntax.hir_id?;
        let mut work = WorkLimit::new(16384);
        let plan = match projection_receipts::projection_path(&self.semantic_hir, source, &mut work)
        {
            Ok(Some(plan)) => plan,
            Ok(None) => return None,
            Err(error) => return Some(Err(error)),
        };
        if frame.env.get(plan.name()) != Some(&id)
            || self
                .bindings
                .get(id)
                .is_none_or(|binding| binding.name != plan.name())
        {
            return Some(Err(SourceTypesError::Unresolved));
        }
        let stored = match self
            .type_source
            .storage
            .types
            .binding_schema_if_known(id, None, &mut work)
        {
            Ok(stored) => stored,
            Err(error) => return Some(Err(error)),
        };
        let stored = if named_parameter {
            match stored
                .map(|(schema, environment)| {
                    let schema = crate::sema::source_types::declarations::resolve_schema(
                        &schema,
                        &self.semantic_hir,
                        &mut work,
                    )?;
                    Ok((schema, environment))
                })
                .transpose()
            {
                Ok(stored) => stored,
                Err(error) => return Some(Err(error)),
            }
        } else {
            stored
        };
        let result = (|| {
            let context = self.invocation_context(frame.callable_owner);
            let occurrence =
                self.source_projection_occurrence(source, value, context, &mut work)?;
            let projection = self
                .source_projection_receipts()
                .project(&plan, occurrence, view, &mut work)?;
            if self
                .application_effect
                .expressions
                .get(projection.root.0 as usize)
                .is_none_or(|fact| {
                    fact.source_id != Some(plan.root())
                        || fact.value.sources != BTreeSet::from([id])
                })
            {
                return Err(SourceTypesError::Unresolved);
            }
            let Some((schema, environment)) = stored else {
                return Ok(None);
            };
            let mut schema = schema;
            for step in &projection.steps {
                if schema.root_is_binder(&mut work)? {
                    let ril_compiler_core::projection::TypeProjection::Field(label) = step else {
                        return Err(SourceTypesError::Unresolved);
                    };
                    schema = self.storage_projection_source_schema(
                        &schema,
                        &environment,
                        &Slot::Field(label.clone()),
                        &mut work,
                    )?;
                } else {
                    schema = schema.project_steps(std::slice::from_ref(step), &mut work)?;
                }
            }
            Ok(Some((schema, environment)))
        })();
        Some(result)
    }

    /// A recorded declaration can be unknown, but an admission failure remains
    /// an error. The caller must establish the original read occurrence.
    pub(super) fn recorded_binding_source_schema(
        &self,
        binding: BindingId,
        work: &mut crate::sema::source_types::WorkLimit,
    ) -> Option<
        Result<
            Option<(
                crate::sema::source_types::SourceSchema,
                crate::sema::context::FrozenEnvironment,
            )>,
            crate::sema::source_types::SourceTypesError,
        >,
    > {
        self.type_source.storage.by_binding.get(&binding)?;
        Some(
            self.type_source
                .storage
                .types
                .binding_schema_if_known(binding, None, work),
        )
    }

    pub(super) fn check_storage_write_source(
        &mut self,
        reception: StoreReception<'_>,
        replacement: &mut Value,
        frame: &Frame,
    ) -> bool {
        let StoreReception {
            target,
            operator,
            rhs_syntax,
            rhs,
            destination,
            receiver,
        } = reception;
        let Some(target_id) = target.hir_id else {
            self.unsupported(target.span, "storage write has no original target ExprId");
            return false;
        };
        let mut work = WorkLimit::new(16384);
        let expected = (|| -> BindingSchema {
            match &destination {
                StorageDestination::Binding(binding) => self
                    .type_source
                    .storage
                    .types
                    .binding_schema_if_known(*binding, None, &mut work),
                StorageDestination::Projection { slot, .. } => {
                    let syntax = match &target.kind {
                        ExprKind::Field { base, .. }
                        | ExprKind::Index { base, .. }
                        | ExprKind::ComputedField { base, .. } => base.as_ref(),
                        _ => return Err(SourceTypesError::Unresolved),
                    };
                    let value = receiver.ok_or(SourceTypesError::MissingNode)?;
                    let Some((schema, environment)) =
                        self.original_source_receiving_schema(value, syntax, frame, &mut work)?
                    else {
                        return Ok(None);
                    };
                    let schema = self.storage_projection_source_schema(
                        &schema,
                        &environment,
                        slot,
                        &mut work,
                    )?;
                    Ok(Some((schema, environment)))
                }
            }
        })();
        let expected = match expected {
            Ok(source) => source,
            Err(error) => {
                self.unsupported(
                    target.span,
                    format!("storage destination Source graph failed: {error}"),
                );
                None
            }
        };
        let retained = match &expected {
            Some((schema, environment)) => match self.type_source.storage.types.intern_schema(
                schema,
                environment.clone(),
                &mut work,
            ) {
                Ok(view) => Some(view),
                Err(error) => {
                    self.unsupported(
                        target.span,
                        format!("storage destination Source admission failed: {error}"),
                    );
                    None
                }
            },
            None => None,
        };
        let context = self.invocation_context(frame.callable_owner);
        self.type_source.storage.writes.push(StorageWrite {
            target: target_id,
            context,
            activation: frame.owner,
            span: target.span,
            operator: operator.into(),
            rhs,
            destination,
            expected: retained,
            completed: true,
        });
        let answer = (|| {
            let (expected, environment) = expected.as_ref().ok_or(SourceTypesError::Unresolved)?;
            if environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            if matches!(
                expected.sensitivity(&mut work),
                crate::sema::source_types::SourceSensitivity::Absent { .. }
            ) {
                return Ok(true);
            }
            if operator != "=" {
                return Ok(false);
            }
            // Type coordinates alone cannot certify nested latent callable rows.
            if expected.has_callable(&mut work)? {
                return Err(SourceTypesError::Unresolved);
            }
            work.charge(1)?;
            let original = self
                .application_effect
                .expressions
                .get(rhs.expression)
                .ok_or(SourceTypesError::MissingNode)?
                .value
                .packet()
                .clone();
            let actual = self.original_source_receiving_schema(
                original.value(),
                rhs_syntax,
                frame,
                &mut work,
            )?;
            let fresh = source_reception::construction(rhs_syntax, &mut 4096)
                .ok_or(SourceTypesError::BudgetExceeded)?;
            match actual {
                Some((actual, environment)) if !environment.is_poisoned() => {
                    expected.receive_schema(&actual, Some(&fresh), &mut work)
                }
                Some(_) => Err(SourceTypesError::Unresolved),
                None => expected
                    .empty_context(&fresh, &mut work)?
                    .ok_or(SourceTypesError::Unresolved),
            }
        })();
        match answer {
            Ok(true) => true,
            Ok(false) => {
                self.error("E0301",target.span,"stored input source does not fit the destination's original declaration schema",[replacement.cause]);
                false
            }
            Err(error) => {
                self.unsupported(target.span,format!("storage reception requires its original declaration and complete input source coordinates: {error}"));
                false
            }
        }
    }

    fn storage_projection_source_schema(
        &self,
        source: &SourceSchema,
        environment: &crate::sema::context::FrozenEnvironment,
        slot: &Slot,
        work: &mut WorkLimit,
    ) -> Result<SourceSchema, SourceTypesError> {
        let steps = crate::sema::source_types::steps_in(std::slice::from_ref(slot), work)?;
        if let Some(schema) = source.project_steps_if_structural(&steps, work)? {
            return Ok(schema);
        }
        let Slot::Field(label) = slot else {
            return Err(SourceTypesError::Unresolved);
        };
        let identities = source.binder_identities(work)?;
        let mut identities = identities.iter();
        let identity = identities.next().ok_or(SourceTypesError::Unresolved)?;
        if identities.next().is_some() {
            return Err(SourceTypesError::Unresolved);
        }
        let binder = self
            .generic_binders
            .get(identity)
            .ok_or(SourceTypesError::Unresolved)?;
        work.charge(self.functions.len())?;
        let declaration = self
            .functions
            .iter()
            .find(|function| function.definition == binder.definition)
            .ok_or(SourceTypesError::Unresolved)?;
        let parameter = declaration
            .syntax
            .generics
            .get(binder.index as usize)
            .ok_or(SourceTypesError::Unresolved)?;
        if !crate::sema::record_bounds::certifies_type_sort(
            identity,
            binder,
            parameter,
            &self.record_bounds,
        ) {
            return Err(SourceTypesError::Unresolved);
        }
        let bound = self
            .record_bounds
            .get(
                self.record_bounds_by_binder
                    .get(identity)
                    .ok_or(SourceTypesError::MissingNode)?
                    .0 as usize,
            )
            .ok_or(SourceTypesError::MissingNode)?;
        if bound.binder != *identity
            || bound.definition != binder.definition
            || bound.generic_index != binder.index
        {
            return Err(SourceTypesError::Unresolved);
        }
        work.charge(bound.fields.len())?;
        let mut fields = bound.fields.iter().filter(|field| field.label == *label);
        let field = fields.next().ok_or(SourceTypesError::MissingProjection)?;
        if fields.next().is_some() {
            return Err(SourceTypesError::DuplicateField);
        }
        let schema = SourceSchema::import(&field.key, None, work)?;
        work.charge(environment.generic_sources.len())?;
        let selected = environment
            .generic_sources
            .iter()
            .map(|(identity, source)| (identity.clone(), source.schema.clone()))
            .collect();
        let schema = schema.substitute(&selected, work)?;
        crate::sema::source_types::declarations::resolve_schema(&schema, &self.semantic_hir, work)
    }
    pub(super) fn record_aborted_storage_write(
        &mut self,
        target: &Expr,
        operator: &str,
        rhs: StorageObservation,
        destination: StorageDestination,
        frame: &Frame,
    ) {
        let Some(target_id) = target.hir_id else {
            self.unsupported(
                target.span,
                "aborted storage write has no original target ExprId",
            );
            return;
        };
        self.type_source.storage.writes.push(StorageWrite {
            target: target_id,
            context: self.invocation_context(frame.callable_owner),
            activation: frame.owner,
            span: target.span,
            operator: operator.into(),
            rhs,
            destination,
            expected: None,
            completed: false,
        });
    }
}

fn source_path<'a>(syntax: &'a Expr, path: &mut Vec<Slot>, work: &mut usize) -> Option<&'a str> {
    *work = work.checked_sub(1)?;
    match &syntax.kind {
        ExprKind::Name(name) => Some(name),
        ExprKind::Field { base, field, .. } => {
            let name = source_path(base, path, work)?;
            path.push(
                field
                    .parse()
                    .map(Slot::Tuple)
                    .unwrap_or_else(|_| Slot::Field(field.clone())),
            );
            Some(name)
        }
        ExprKind::Index { base, .. } => {
            let name = source_path(base, path, work)?;
            path.push(Slot::AnyIndex);
            Some(name)
        }
        _ => None,
    }
}
