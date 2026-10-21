//! Immutable declaration views and physical receipts for storage reception.
//! The current value of a mutable binding is never its declaration schema.
use super::*;
use crate::sema::source_types::{
    SourceSchema, SourceTypesError, WorkLimit,
    projection_receipts::{self, ProjectionOccurrence, ProjectionReceipts, SourceRead},
};
use crate::sema::{
    effect_identity::ArgumentKey,
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
    pub(super) fn parameter_source_schema(
        &self,
        binding: BindingId,
        original: Option<ril_compiler_core::ids::TypeExprId>,
    ) -> Option<(
        crate::sema::source_types::SourceSchema,
        crate::sema::context::FrozenEnvironment,
    )> {
        self.type_source
            .storage
            .types
            .binding_schema(
                binding,
                original,
                &mut crate::sema::source_types::WorkLimit::new(16384),
            )
            .ok()
    }
    pub(super) fn record_parameter_source(&mut self, binding: BindingId, name: &str, span: Span) {
        let environment = self.bindings[binding].typing_environment.clone();
        let named = self
            .scopes
            .get(&self.bindings[binding].owner)
            .is_some_and(|scope| {
                matches!(scope.origin, crate::sema::scopes::ScopeOrigin::Named(_))
            });
        if named {
            let schema = match self.named_parameter_declaration_schema(binding, name) {
                Ok(schema) => schema,
                Err(error) => {
                    self.unsupported(
                        span,
                        format!("named parameter lost its original declaration graph: {error}"),
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
        let key = self.declared_formal_source(binding, name);
        if self
            .type_source
            .storage
            .types
            .record(binding, key.as_ref(), environment)
            .is_err()
        {
            self.unsupported(span, "parameter source view exceeded its metadata budget");
        }
    }

    fn named_parameter_declaration_schema(
        &mut self,
        binding: BindingId,
        name: &str,
    ) -> Result<Option<SourceSchema>, SourceTypesError> {
        use crate::sema::{effect_identity::ArgumentKey, source_types::substitute_key};
        let Some((syntax, environment)) = self.formal_binding_declaration(binding, name) else {
            return Ok(None);
        };
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
            let key = checker
                .record_bound_key(&syntax, &scope)
                .ok_or(SourceTypesError::BudgetExceeded)?;
            let mut pending = vec![&key];
            let mut has_binder = false;
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
                                // A genuine Key coordinate is not an ordinary
                                // Type Source, even though it has a binder UID.
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
            let selected = if has_binder {
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
                let info = checker
                    .functions
                    .iter()
                    .find(|info| info.definition == definition)
                    .ok_or(SourceTypesError::Unresolved)?
                    .clone();
                // The actual selection can come from a nested product's
                // independently recorded scoped identity. An erased ordinary
                // substitution never reconstructs its missing Source.
                let actual = checker
                    .actual_input_source_selections(&info, event, span)
                    .ok_or(SourceTypesError::Unresolved)?;
                substitute_key(&key, &actual, &mut work)?
            } else {
                let Some(key) = checker.freeze_source_receiving_target(&syntax).key() else {
                    return Ok(None);
                };
                key
            };
            let schema = SourceSchema::import(&selected, syntax.hir_id, &mut work)?;
            crate::sema::source_types::declarations::resolve_schema(
                &schema,
                &checker.semantic_hir,
                &mut work,
            )
            .map(Some)
        })
    }

    /// Static constraint lookup only. This projects the immutable declaration
    /// view, never the binding's current value, heap contents or numeric data.
    pub(super) fn declared_operand_source(
        &mut self,
        syntax: &Expr,
        frame: &Frame,
    ) -> Option<ArgumentKey> {
        let mut path = Vec::new();
        let name = source_path(syntax, &mut path, &mut 4096)?;
        let id = *frame.env.get(name)?;
        if let Ok(key) = self.type_source.storage.types.projected_binding_key(
            id,
            &path,
            Some(&self.semantic_hir),
        ) {
            return Some(key);
        }
        let mut key = self.declared_formal_source(id, name)?;
        for slot in path {
            key = self.storage_projection_source_key(&key, &slot)?;
        }
        Some(key)
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
        let original = self
            .application_effect
            .expressions
            .get(initializer.expression)
            .cloned();
        let mut work = crate::sema::source_types::WorkLimit::new(16384);
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
                &original.value,
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
                let key =
                    self.original_source_receiving_key(&original.value, &binding.value, frame)?;
                match crate::sema::source_types::declarations::schema(
                    &key,
                    &self.semantic_hir,
                    &mut work,
                ) {
                    Ok(schema) => Some(schema),
                    Err(_) => {
                        self.unsupported(
                            binding.value.span,
                            "storage input Source graph could not be admitted",
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
        if !named_parameter && !self.type_source.storage.by_binding.contains_key(&id) {
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
        let known_source = stored.is_some();
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
            Ok(schema
                .project_steps_if_structural(&projection.steps, &mut work)?
                .map(|schema| (schema, environment)))
        })();
        match result {
            Ok(None) if known_source => None,
            result => Some(result),
        }
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
        let expected = match &destination {
            StorageDestination::Binding(binding) => self
                .type_source
                .storage
                .types
                .projected_binding_key(*binding, &[], Some(&self.semantic_hir))
                .ok(),
            StorageDestination::Projection { slot, .. } => {
                let syntax = match &target.kind {
                    ExprKind::Field { base, .. } | ExprKind::Index { base, .. } => {
                        Some(base.as_ref())
                    }
                    _ => None,
                };
                receiver
                    .zip(syntax)
                    .and_then(|(value, syntax)| {
                        self.original_source_receiving_key(value, syntax, frame)
                    })
                    .and_then(|key| self.storage_projection_source_key(&key, slot))
            }
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
            expected: expected.clone(),
            completed: true,
        });
        let observation = self
            .application_effect
            .expressions
            .get(rhs.expression)
            .cloned();
        let actual = observation.as_ref().and_then(|original| {
            self.original_source_receiving_key(&original.value, rhs_syntax, frame)
        });
        let fresh = source_reception::construction(rhs_syntax, &mut 4096);
        let answer = expected.as_ref().and_then(|expected| {
            if crate::sema::source_types::key_is_coordinate_free_with_declarations(
                expected,
                Some(&self.semantic_hir),
            ) {
                return Some(true);
            }
            // Arithmetic compound assignment is checked separately and cannot
            // create a collection/Fn Source from its numeric RHS.
            if operator != "=" {
                return Some(false);
            }
            compatible(expected, actual.as_ref(), fresh.as_ref())
        });
        match answer {
            Some(true) => {
                // Replace only the type view. Permission, publication, causes,
                // origins and all actual write obligations remain unchanged.
                replacement.source_type_witness = expected
                    .as_ref()
                    .and_then(|key| {
                        super::call_input_source::storage_closed_source_syntax(key, target.span)
                    })
                    .and_then(|syntax| self.source_type_from_frozen_syntax(&syntax));
                true
            }
            Some(false) => {
                self.error("E0301", target.span,
                    "stored input source does not fit the destination's original declaration schema",
                    [replacement.cause]);
                false
            }
            None => {
                self.unsupported(target.span,
                    "storage reception requires its original declaration and complete input source coordinates");
                false
            }
        }
    }

    /// A structural bound guarantees the Source of a named member, not a
    /// complete Source for its open parent. Select the declared member before
    /// substituting its leaves; unrelated row members remain unresolved.
    fn storage_projection_source_key(
        &self,
        source: &ArgumentKey,
        slot: &Slot,
    ) -> Option<ArgumentKey> {
        let (
            ArgumentKey::Binder {
                identity,
                sort: crate::sema::effect_identity::StaticBinderSort::Type,
            },
            Slot::Field(label),
        ) = (source, slot)
        else {
            return crate::sema::source_types::declarations::project(
                source,
                std::slice::from_ref(slot),
                &self.semantic_hir,
                &mut crate::sema::source_types::WorkLimit::new(4096),
            )
            .ok();
        };
        let binder = self.generic_binders.get(identity)?;
        let declaration = self
            .functions
            .iter()
            .find(|function| function.definition == binder.definition)?;
        let parameter = declaration.syntax.generics.get(binder.index as usize)?;
        if !crate::sema::record_bounds::certifies_type_sort(
            identity,
            binder,
            parameter,
            &self.record_bounds,
        ) {
            return None;
        }
        let bound = self
            .record_bounds
            .get(self.record_bounds_by_binder.get(identity)?.0 as usize)?;
        if bound.binder != *identity
            || bound.definition != binder.definition
            || bound.generic_index != binder.index
        {
            return None;
        }
        let fields: Vec<_> = bound
            .fields
            .iter()
            .filter(|field| field.label == *label)
            .collect();
        let [field] = fields.as_slice() else {
            return None;
        };
        self.selected_bound_key(&field.key)
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

fn compatible(
    expected: &ArgumentKey,
    actual: Option<&ArgumentKey>,
    fresh: Option<&source_reception::Construction>,
) -> Option<bool> {
    // A type-coordinate relation does not prove retained callable bounds.
    // Until frozen lexical row/latent certificates are attached to stores,
    // every callable coordinate (also nested) remains an obligation.
    if has_callable(expected, &mut 4096)? {
        return None;
    }
    if let Some(actual) = actual {
        return source_reception::compatible(expected, actual, fresh, &mut 4096);
    }
    match (expected, fresh) {
        (
            ArgumentKey::Array { length, element },
            Some(source_reception::Construction::Array(items)),
        ) if items.is_empty() => {
            source_reception::complete(element, &mut 4096)?;
            Some(
                length
                    .as_ref()
                    .is_none_or(|length| length == "const(int:0)"),
            )
        }
        _ => None,
    }
}

pub(in crate::sema::checker) fn has_callable(key: &ArgumentKey, work: &mut usize) -> Option<bool> {
    *work = work.checked_sub(1)?;
    let children: Vec<&ArgumentKey> = match key {
        ArgumentKey::Callable { .. } | ArgumentKey::GenericBuiltin(_) => return Some(true),
        ArgumentKey::Array { element, .. } => vec![element],
        ArgumentKey::Map { key, value } => vec![key, value],
        ArgumentKey::Name { arguments, .. } | ArgumentKey::Tuple(arguments) => {
            arguments.iter().collect()
        }
        ArgumentKey::Record { fields, row } => fields
            .iter()
            .map(|field| &field.2)
            .chain(row.iter().map(|row| row.as_ref()))
            .collect(),
        ArgumentKey::Closed(_) => return None,
        ArgumentKey::Binder { .. } => vec![],
    };
    for child in children {
        if has_callable(child, work)? {
            return Some(true);
        }
    }
    Some(false)
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
