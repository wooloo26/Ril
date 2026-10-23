//! Source transport follows actual observations in graph form. Genuine source
//! headers enter once; a retained graph is never exported and readmitted here.
use super::*;
use crate::sema::source_types::projection_receipts::SourceRead;
use ril_syntax::ast::RecordMember;

pub(super) fn schema_work<T>(
    work: &mut usize,
    query: impl FnOnce(&mut WorkLimit) -> Result<T, crate::sema::source_types::SourceTypesError>,
) -> Check<T> {
    let mut budget = WorkLimit::new(*work);
    let result = query(&mut budget);
    *work = budget.remaining();
    result.map_err(|error| format!("original Source graph: {error}"))
}

impl Replay<'_> {
    /// A sealed finite compatibility witness is normalized type evidence, not
    /// an original HIR header. Its value/constant origin is authenticated by
    /// the caller before this distinct, single ingress is used.
    pub(in crate::sema::record_bound_validation) fn closed_witness_source_schema(
        &self,
        witness: &crate::sema::model::SourceTypeWitness,
        environment: FrozenEnvironment,
        work: &mut usize,
    ) -> Check<OriginalSource> {
        let valid = witness
            .validate_closed_with_work(work)
            .ok_or("closed Source witness exceeds its validation work bound")?;
        // resolved_names and the final bounded key construction each walk
        // this same original witness after its shared validation admission.
        for _ in 0..2 {
            crate::static_eval::charge_type_syntax_clone(&witness.syntax, work)
                .ok_or("closed Source witness exceeds its validation work bound")?;
        }
        require(
            valid
                && crate::sema::source_type_validation::resolved_names(
                    witness,
                    &self.facts.external_type_declarations,
                ),
            "closed Source witness is inconsistent or unresolved",
        )?;
        let key =
            crate::static_eval::effects::bounded_argument_key(&witness.syntax, &BTreeMap::new())
                .ok_or("closed Source witness exceeds its syntax admission")?;
        self.source_header_schema(&key, environment, work)
    }

    pub(in crate::sema::record_bound_validation) fn source_selected_schemas(
        &self,
        environment: &FrozenEnvironment,
        work: &mut usize,
    ) -> Check<BTreeMap<String, OriginalSource>> {
        require(
            !environment.is_poisoned(),
            "selected Source graph has a poisoned interpretation",
        )?;
        *work = work
            .checked_sub(environment.generic_sources.len())
            .ok_or("selected Source graph map exceeds its work bound")?;
        let mut selected = BTreeMap::new();
        for (identity, source) in &environment.generic_sources {
            *work = work
                .checked_sub(identity.len().div_ceil(32))
                .ok_or("selected Source graph identities exceed their work bound")?;
            require(
                !source.environment.is_poisoned(),
                "selected Source graph lost its frozen interpretation",
            )?;
            selected.insert(
                identity.clone(),
                (source.schema.clone(), source.environment.clone()),
            );
        }
        Ok(selected)
    }

    pub(in crate::sema::record_bound_validation) fn source_substitute_schema(
        &self,
        schema: SourceSchema,
        environment: FrozenEnvironment,
        selected: &BTreeMap<String, OriginalSource>,
        work: &mut usize,
    ) -> Check<OriginalSource> {
        let required = schema_work(work, |budget| schema.binder_identities(budget))?;
        if schema_work(work, |budget| schema.root_is_binder(budget))?
            && let Some(identity) = required.first()
            && schema_work(work, |budget| {
                schema.equivalent_key(
                    &ArgumentKey::Binder {
                        identity: identity.clone(),
                        sort: StaticBinderSort::Type,
                    },
                    budget,
                )
            })?
            && let Some(source) = selected.get(identity)
        {
            return Ok(source.clone());
        }
        *work = work
            .checked_sub(selected.len())
            .ok_or("Source substitution exceeds its work bound")?;
        let replacements = selected
            .iter()
            .map(|(identity, (source, _))| (identity.clone(), source.clone()))
            .collect();
        let result = schema_work(work, |budget| schema.substitute(&replacements, budget))?;
        if !schema_work(work, |budget| result.requires_environment(budget))? {
            return Ok((result, environment));
        }
        let mut dependencies: Vec<_> = selected
            .iter()
            .filter(|(identity, _)| required.contains(*identity))
            .map(|(_, source)| source.clone())
            .collect();
        if schema_work(work, |budget| {
            schema.requires_declaration_environment(budget)
        })? {
            dependencies.push((schema, environment.clone()));
        }
        let dependency_environment = self.source_composite_environment(&dependencies, work)?;
        let has_dependency = dependencies
            .iter()
            .map(|(schema, _)| schema_work(work, |budget| schema.requires_environment(budget)))
            .collect::<Check<Vec<_>>>()?
            .into_iter()
            .any(|dependent| dependent);
        Ok((
            result,
            if has_dependency {
                dependency_environment
            } else {
                environment
            },
        ))
    }

    pub(in crate::sema::record_bound_validation) fn source_type_header(
        &self,
        syntax: &TypeExpr,
        scope: &BoundScope,
        environment: FrozenEnvironment,
        work: &mut usize,
    ) -> Check<OriginalSource> {
        let (schema, environment) =
            self.source_type_header_raw(syntax, scope, environment, work)?;
        let selected = self.source_selected_schemas(&environment, work)?;
        self.source_substitute_schema(schema, environment, &selected, work)
    }

    pub(in crate::sema::record_bound_validation) fn source_type_header_raw(
        &self,
        syntax: &TypeExpr,
        scope: &BoundScope,
        environment: FrozenEnvironment,
        work: &mut usize,
    ) -> Check<OriginalSource> {
        use crate::sema::source_types::declarations::{
            HeaderContext, elaborate_original_header, original_header,
        };
        require(
            !environment.is_poisoned(),
            "original Source header has a poisoned interpretation",
        )?;
        let mut binders = self.key_scope(scope)?;
        *work = work
            .checked_sub(environment.generic_context.len())
            .ok_or("original Source binder map exceeds its work bound")?;
        for (name, identity) in &environment.generic_context {
            *work = work
                .checked_sub(name.len().div_ceil(32) + identity.len().div_ceil(32))
                .ok_or("original Source binder names exceed their work bound")?;
            binders
                .entry(name.clone())
                .or_insert_with(|| identity.clone());
        }
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("original Source header has no HIR")?;
        let context = HeaderContext {
            declarations: &self.facts.external_type_declarations,
            program: self
                .facts
                .source_program
                .as_deref()
                .ok_or("original Source header has no program")?,
            hir,
            lexical: self
                .lexical
                .as_ref()
                .ok_or("original Source header has no lexical index")?,
            binders: &binders,
            functions: &self.facts.functions,
            generic_binders: &self.facts.generic_binders,
            layout: self
                .facts
                .target_layout
                .ok_or("original Source header has no layout")?,
        };
        let schema = schema_work(work, |budget| {
            match original_header(syntax, context, budget) {
                Err(crate::sema::source_types::SourceTypesError::NeedsStaticElaboration) => {
                    elaborate_original_header(syntax, context, budget)
                }
                result => result,
            }
        })?;
        for identity in schema_work(work, |budget| schema.binder_identities(budget))? {
            if self.facts.generic_binders.contains_key(&identity) {
                require(
                    self.input_type_sort(&identity)?,
                    "original Source used a non-Type coordinate as a Type",
                )?;
            } else {
                *work = work
                    .checked_sub(self.facts.bound_rows.len())
                    .ok_or("original Source row identity exceeds its work bound")?;
                require(self.facts.bound_rows.iter().any(|row| matches!(&row.identity, RowIdentity::Binder(actual) if actual == &identity)),
                    "original Source has no genuine Type or row identity")?;
            }
        }
        Ok((schema, environment))
    }

    pub(super) fn source_callable_row_identity(
        &self,
        origin: crate::sema::source_types::CallableRowOrigin,
        annotations: &[ril_syntax::ast::Annotation],
        scope: &BoundScope,
        environment: &FrozenEnvironment,
        work: &mut usize,
    ) -> Check<Option<crate::sema::source_types::CallableRowIdentity<SourceSchema>>> {
        use crate::sema::source_types::declarations::{HeaderContext, callable_row_identity};
        require(
            !environment.is_poisoned(),
            "original callable row has a poisoned environment",
        )?;
        let mut binders = self.key_scope(scope)?;
        source_scan_work(work, environment.generic_context.len())?;
        for (name, identity) in &environment.generic_context {
            source_scan_work(
                work,
                name.len().div_ceil(32) + identity.len().div_ceil(32) + 1,
            )?;
            binders
                .entry(name.clone())
                .or_insert_with(|| identity.clone());
        }
        schema_work(work, |budget| {
            callable_row_identity(
                origin,
                annotations,
                HeaderContext {
                    declarations: &self.facts.external_type_declarations,
                    program: self
                        .facts
                        .source_program
                        .as_deref()
                        .ok_or(crate::sema::source_types::SourceTypesError::MissingNode)?,
                    hir: self
                        .facts
                        .semantic_hir
                        .as_deref()
                        .ok_or(crate::sema::source_types::SourceTypesError::MissingNode)?,
                    lexical: self
                        .lexical
                        .as_ref()
                        .ok_or(crate::sema::source_types::SourceTypesError::MissingNode)?,
                    binders: &binders,
                    functions: &self.facts.functions,
                    generic_binders: &self.facts.generic_binders,
                    layout: self
                        .facts
                        .target_layout
                        .ok_or(crate::sema::source_types::SourceTypesError::MissingNode)?,
                },
                budget,
            )
        })
    }

    fn original_source_header_schema(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        visit: SourceVisit,
    ) -> Check<Option<OriginalSource>> {
        if crate::sema::checker::BuiltinNameIndex::is_candidate(expression, work)? {
            let observation =
                self.original_source_root(expression, value, context, visit.observation, work)?;
            let names = self.builtin_source_names(work)?;
            let mut builtin_work = WorkLimit::new(*work);
            let builtin = crate::sema::checker::original_canonical_builtin_source(
                self.facts,
                &crate::sema::checker::CanonicalBuiltinUse {
                    value,
                    actual: expression,
                    context,
                    observation,
                },
                &names,
                &mut builtin_work,
            );
            *work = builtin_work.remaining();
            drop(names);
            if let Some(source) = builtin? {
                return Ok(Some(source));
            }
        }
        if let Some(source) = self.original_constructor_result_schema(
            expression,
            value,
            context,
            visit.observation,
            work,
        )? {
            return Ok(Some(source));
        }
        let root =
            self.original_source_root(expression, value, context, visit.observation, work)?;
        if let Some(source) =
            self.public_builtin_result_source(expression, root, context, sites, work)?
        {
            return Ok(Some(source));
        }
        let environment = self.source_graph_environment(context, visit.observation, work)?;
        if let Some(observation) = visit.observation
            && let Some(key) = self.operation_result_source(observation, work)?
        {
            return self.source_header_schema(&key, environment, work).map(Some);
        }
        if matches!(
            expression.kind,
            ExprKind::Field { .. } | ExprKind::Index { .. } | ExprKind::ComputedField { .. }
        ) && let Some(key) =
            self.formal_input_path_key_if_known(expression, value, context, work)?
        {
            let selected = self.source_selected_schemas(&environment, work)?;
            let (schema, environment) = self.source_header_schema(&key, environment, work)?;
            return self
                .source_substitute_schema(schema, environment, &selected, work)
                .map(Some);
        }
        let name = match &expression.kind {
            ExprKind::Name(name) => Some(Cow::Borrowed(name.as_str())),
            ExprKind::Path(path) => {
                source_scan_work(work, path.len() + 1)?;
                for part in path {
                    source_scan_work(work, part.len().div_ceil(32))?;
                }
                Some(Cow::Owned(path.join("::")))
            }
            _ => None,
        };
        if let Some(name) = name {
            let name = name.as_ref();
            if let Some(original) = self.facts.constant_pool.source_views.get(name) {
                let source = self.closed_witness_source_schema(original, environment, work)?;
                if let Some(actual) = &value.source_type_witness {
                    source_scan_work(work, actual.key.len())?;
                }
                require(
                    value.source_type_witness.as_ref() == Some(original),
                    "constant Source differs from its sealed original header",
                )?;
                return Ok(Some(source));
            }
            if let Some(reference) = self.facts.constant_pool.references.get(name).copied() {
                require(
                    value.source_type_witness.is_none(),
                    "constant literal borrowed a publication Source view",
                )?;
                return schema_work(work, |budget| {
                    crate::sema::source_types::constants::literal_schema(
                        &self.facts.constant_pool,
                        reference,
                        budget,
                    )
                })
                .map(|schema| schema.map(|schema| (schema, environment)));
            }
            if value.sources.len() == 1 {
                let id = *value.sources.first().unwrap();
                let binding = self
                    .facts
                    .bindings
                    .get(id)
                    .ok_or("original header Name has no binding")?;
                source_scan_work(
                    work,
                    binding.name.len().div_ceil(32) + name.len().div_ceil(32),
                )?;
                require(
                    binding.name == name,
                    "original header borrowed another named binding",
                )?;
                if binding.parameter {
                    if let Some(key) = self.operation_formal_source_key(binding, work)? {
                        return self
                            .source_header_schema(&key, binding.typing_environment.clone(), work)
                            .map(Some);
                    }
                    if matches!(binding.context.owner, Some(CallableOwner::Lambda(_))) {
                        return self
                            .lambda_formal_source_schema(
                                expression, value, context, sites, work, visit,
                            )
                            .map(Some);
                    }
                }
                if let [Callable::Named(index)] = value.callables.as_slice() {
                    let function = self
                        .facts
                        .functions
                        .get(*index)
                        .ok_or("original function header is absent")?;
                    require(binding.declaration.is_some() && binding.declaration == function.hir_id && function.hir_id.and_then(|id| self.facts.semantic_hir.as_deref()?.statement(id)).is_some_and(|statement| {
                        matches!(&statement.kind, crate::hir::nodes::StmtKind::Function(header) if header.name == binding.name)
                    }) && function.lexical.get(name) == Some(&id), "callable source is not its actual named declaration")?;
                    let scope = self.scope(function.definition)?;
                    let mut parameters = Vec::new();
                    *work = work
                        .checked_sub(
                            function.syntax.parameters.len()
                                + function.syntax.annotations.len()
                                + 1,
                        )
                        .ok_or("function Source header exceeds its work bound")?;
                    for parameter in &function.syntax.parameters {
                        let syntax = parameter
                            .ty
                            .as_ref()
                            .ok_or("function parameter has no original Source header")?;
                        parameters.push((
                            parameter.mode,
                            self.source_type_header_raw(
                                syntax,
                                &scope,
                                function.typing_environment.clone(),
                                work,
                            )?
                            .0,
                        ));
                    }
                    let result = if let Some(result) = &function.syntax.return_type {
                        self.source_type_header_raw(
                            result,
                            &scope,
                            function.typing_environment.clone(),
                            work,
                        )?
                        .0
                    } else {
                        self.source_header_schema(
                            &ArgumentKey::Tuple(vec![]),
                            FrozenEnvironment::default(),
                            work,
                        )?
                        .0
                    };
                    let mut annotations = Vec::with_capacity(function.syntax.annotations.len());
                    for annotation in &function.syntax.annotations {
                        source_scan_work(work, annotation.text.len().div_ceil(32))?;
                        annotations.push(annotation.text.clone());
                    }
                    let row = self.source_callable_row_identity(
                        crate::sema::source_types::CallableRowOrigin::Declaration(
                            function
                                .hir_id
                                .ok_or("named callable row has no original declaration")?,
                        ),
                        &function.syntax.annotations,
                        &scope,
                        &function.typing_environment,
                        work,
                    )?;
                    let schema = schema_work(work, |budget| {
                        SourceSchema::callable_original(
                            &parameters,
                            &result,
                            &annotations,
                            row.as_ref(),
                            None,
                            budget,
                        )
                    })?;
                    let required = schema_work(work, |budget| schema.binder_identities(budget))?;
                    source_scan_work(work, required.len())?;
                    let mut selected = BTreeMap::new();
                    for identity in required {
                        source_scan_work(
                            work,
                            1 + identity.len().div_ceil(32)
                                + function
                                    .typing_environment
                                    .generic_sources
                                    .len()
                                    .checked_ilog2()
                                    .unwrap_or(0) as usize,
                        )?;
                        let Some(source) =
                            function.typing_environment.generic_sources.get(&identity)
                        else {
                            continue;
                        };
                        require(
                            !source.environment.is_poisoned(),
                            "captured function Source lost its frozen interpretation",
                        )?;
                        source_scan_work(
                            work,
                            2 + selected.len().checked_ilog2().unwrap_or(0) as usize,
                        )?;
                        selected.insert(
                            identity,
                            (source.schema.clone(), source.environment.clone()),
                        );
                    }
                    return self
                        .source_substitute_schema(
                            schema,
                            function.typing_environment.clone(),
                            &selected,
                            work,
                        )
                        .map(Some);
                }
            }
        }
        if let Some(source) =
            self.inferred_lambda_source_schema(expression, value, context, sites, work)?
        {
            return Ok(Some(source));
        }
        if let Some(application) = AstApplication::from_ast(expression) {
            let root =
                self.original_source_root(expression, value, context, visit.observation, work)?;
            *work = work
                .checked_sub(self.facts.copy_call_events.len())
                .ok_or("returned Source event work exhausted")?;
            let mut events = self
                .facts
                .copy_call_events
                .iter()
                .filter(|event| event.result_expression == Some(root));
            if let Some(event) = events.next() {
                require(
                    events.next().is_none() && event.matches_source(expression),
                    "returned Source borrowed another physical call",
                )?;
                if let Some(target) = event.target {
                    let causes = self.producing_result_causes(value.cause, work)?;
                    let instances: Vec<_> =
                        self.facts
                            .copy_invocations
                            .iter()
                            .filter(|call| {
                                call.source_event == Some(event.id)
                                    && call.result.as_ref().is_some_and(|result| {
                                        causes.contains(&result.value.cause.0)
                                    })
                            })
                            .collect();
                    if let [instance] = instances.as_slice() {
                        require(
                            instance.target == target,
                            "returned Source entry changed its actual application target",
                        )?;
                        self.validate_producing_result_transport(instance, value, work)?;
                        let token = event
                            .callee_expression
                            .ok_or("returned Source has no original callee token")?;
                        let Some((callee, callee_environment)) = self
                            .original_observed_source_schema_with_work(
                                application.callee,
                                token,
                                context,
                                sites,
                                work,
                            )?
                        else {
                            return Err("returned Source callee has no complete graph".into());
                        };
                        let (_, result) =
                            schema_work(work, |budget| callee.callable_parts(budget))?
                                .ok_or("returned Source callee graph is not callable")?;
                        // Every selected graph keeps its own actual input
                        // interpretation. The callee receiver's Γ is not the
                        // declaration environment of a caller UID occurring in
                        // a static argument or an open row.
                        let mut selected = self
                            .named_input_source_schemas(instance, sites, work)?
                            .selected;
                        for argument in self.input_static_arguments(instance)? {
                            if selected.contains_key(&argument.binder)
                                || !self.input_type_sort(&argument.binder)?
                            {
                                continue;
                            }
                            if let Some(key) = &argument.key {
                                selected.insert(
                                    argument.binder.clone(),
                                    self.original_input_selection_schema(
                                        instance,
                                        &argument.binder,
                                        key,
                                        sites,
                                        work,
                                    )?,
                                );
                            }
                        }
                        return self
                            .source_substitute_schema(result, callee_environment, &selected, work)
                            .map(Some);
                    }
                }
            }
        }
        // A sealed closed descriptor is a header ingress, not a projection of
        // a retained graph. Composite/copy/storage paths were handled above.
        if let Some(witness) = &value.source_type_witness {
            return self
                .closed_witness_source_schema(witness, environment, work)
                .map(Some);
        }
        if matches!(value.ty, Ty::Generic(_)) {
            let key = self.symbolic_input_source_key(expression, value, context)?;
            return self.source_header_schema(&key, environment, work).map(Some);
        }
        Ok(None)
    }

    /// One ingress from an independently reconstructed declaration/header key.
    /// This is deliberately distinct from the legacy graph-export entrypoints.
    pub(in crate::sema::record_bound_validation) fn source_header_schema(
        &self,
        key: &ArgumentKey,
        environment: FrozenEnvironment,
        work: &mut usize,
    ) -> Check<OriginalSource> {
        require(
            !environment.is_poisoned(),
            "original Source header has a poisoned environment",
        )?;
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("original Source header has no HIR")?;
        let schema = schema_work(work, |budget| {
            crate::sema::source_types::declarations::schema(key, hir, budget)
        })?;
        Ok((schema, environment))
    }

    pub(in crate::sema::record_bound_validation) fn source_graph_environment(
        &self,
        context: InvocationContext,
        observation: Option<usize>,
        work: &mut usize,
    ) -> Check<FrozenEnvironment> {
        *work = work
            .checked_sub(self.facts.binding_sources.len() + self.facts.bindings.len())
            .ok_or("Source declaration environment lookup exceeded its work bound")?;
        let mut found: Option<FrozenEnvironment> = None;
        if let Some(observation) = observation {
            for row in
                self.facts.binding_sources.iter().filter(|row| {
                    row.initializer.expression == observation && row.context == context
                })
            {
                let binding = self
                    .facts
                    .bindings
                    .get(row.binding)
                    .ok_or("Source receiving environment has no binding")?;
                if let Some(previous) = &found {
                    require(
                        previous.id() == binding.typing_environment.id(),
                        "one original receiver has different frozen Source environments",
                    )?;
                } else {
                    found = Some(binding.typing_environment.clone());
                }
            }
        }
        if let Some(environment) = found {
            return Ok(environment);
        }
        if let Some(invocation) = context.invocation
            && let Some(binding) = self.facts.bindings.iter().find(|binding| {
                binding.parameter
                    && binding.context.invocation == Some(invocation)
                    && binding.context.owner == context.owner
            })
        {
            return Ok(binding.typing_environment.clone());
        }
        match context.owner {
            Some(CallableOwner::Function(owner)) => {
                Ok(self.function(owner)?.typing_environment.clone())
            }
            Some(CallableOwner::Lambda(_)) => context
                .closure
                .and_then(|id| self.facts.closures.get(id))
                .map(|closure| closure.contract.typing_environment.clone())
                .ok_or_else(|| "Source header has no original closure environment".into()),
            _ => Ok(FrozenEnvironment::default()),
        }
    }

    pub(in crate::sema::record_bound_validation) fn source_composite_environment(
        &self,
        parts: &[OriginalSource],
        work: &mut usize,
    ) -> Check<FrozenEnvironment> {
        let mut environment: Option<FrozenEnvironment> = None;
        for (schema, captured) in parts {
            require(
                !captured.is_poisoned(),
                "product Source has a poisoned original environment",
            )?;
            if schema_work(work, |budget| schema.requires_environment(budget))? {
                if let Some(previous) = &environment {
                    require(
                        previous.id() == captured.id(),
                        "product Source combines different lexical interpretations",
                    )?;
                } else {
                    environment = Some(captured.clone());
                }
            }
        }
        Ok(environment.unwrap_or_default())
    }

    fn original_typed_record_source_schema(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        visit: SourceVisit,
    ) -> Check<Option<OriginalSource>> {
        let ExprKind::Record {
            ty: Some(ty),
            members,
            ..
        } = &expression.kind
        else {
            return Ok(None);
        };
        let environment = self.source_graph_environment(context, visit.observation, work)?;
        let scope = context
            .owner
            .map(|owner| self.lambda_input_scope(owner, work))
            .transpose()?
            .unwrap_or_default();
        let (schema, environment) = self.source_type_header(ty, &scope, environment, work)?;
        match schema_work(work, |budget| Ok(schema.sensitivity(budget)))? {
            crate::sema::source_types::SourceSensitivity::Absent { .. } => {
                return Ok(Some((schema, environment)));
            }
            crate::sema::source_types::SourceSensitivity::Unknown { reason } => {
                return Err(reason.to_string());
            }
            crate::sema::source_types::SourceSensitivity::Sensitive { .. } => {}
        }
        let root =
            self.original_source_root(expression, value, context, visit.observation, work)?;
        let expected_labels = schema_work(work, |budget| schema.closed_record_labels(budget))?;
        let mut previous = None;
        let mut supplied = BTreeMap::new();
        for member in members {
            *work = work
                .checked_sub(1)
                .ok_or("typed record Source members exceed their work bound")?;
            let (label, child) = match member {
                RecordMember::Field(field) => (Some(&field.name), &field.value),
                RecordMember::Spread(source) => (None, source),
            };
            let source = child
                .hir_id
                .ok_or("typed record member has no original HIR identity")?;
            let observation = self.source_child_observation(root, source, context, work)?;
            require(
                previous.is_none_or(|previous| previous < observation),
                "typed record Source changed its actual member order",
            )?;
            previous = Some(observation);
            let actual = &self.facts.expressions[observation];
            let source = self.original_source_schema_inner(
                child,
                &actual.value,
                context,
                sites,
                work,
                SourceVisit {
                    depth: visit.depth + 1,
                    observation: Some(observation),
                },
            )?;
            if let Some(label) = label {
                *work = work
                    .checked_sub(label.len().div_ceil(32))
                    .ok_or("typed record labels exceed their work bound")?;
                require(
                    expected_labels.contains(label),
                    "typed record member is absent from its original declaration",
                )?;
                let fresh = source_reception::construction(child, work)
                    .ok_or("typed record construction exceeded its work bound")?;
                require(
                    supplied.insert(label.clone(), (source, fresh)).is_none(),
                    "typed record Source repeats an explicit member",
                )?;
            } else {
                let (spread, spread_environment) =
                    source.ok_or("typed record spread has no original Source graph")?;
                let labels = schema_work(work, |budget| spread.closed_record_labels(budget))?;
                for label in labels {
                    *work = work
                        .checked_sub(1 + label.len().div_ceil(32))
                        .ok_or("typed record spread exceeds its work bound")?;
                    require(
                        expected_labels.contains(&label),
                        "typed record spread adds an undeclared member",
                    )?;
                    let field = schema_work(work, |budget| {
                        spread.project_steps(
                            &[crate::sema::source_types::SourcePath::Field(label.clone())],
                            budget,
                        )
                    })?;
                    // Spreading is a stored view, never an empty-literal receiving permission.
                    require(
                        supplied
                            .insert(
                                label,
                                (
                                    Some((field, spread_environment.clone())),
                                    source_reception::Construction::Opaque,
                                ),
                            )
                            .is_none(),
                        "typed record Source repeats a spread member",
                    )?;
                }
            }
        }
        require(
            supplied.len() == expected_labels.len(),
            "typed record Source lost an original declared member",
        )?;
        for (label, (actual, fresh)) in supplied {
            let expected = schema_work(work, |budget| {
                schema.project_steps(
                    &[crate::sema::source_types::SourcePath::Field(label)],
                    budget,
                )
            })?;
            match schema_work(work, |budget| Ok(expected.sensitivity(budget)))? {
                crate::sema::source_types::SourceSensitivity::Absent { .. } => continue,
                crate::sema::source_types::SourceSensitivity::Unknown { reason } => {
                    return Err(reason.to_string());
                }
                crate::sema::source_types::SourceSensitivity::Sensitive { .. } => {}
            }
            if let Some(answer) =
                schema_work(work, |budget| expected.empty_context(&fresh, budget))?
            {
                require(
                    answer,
                    "typed record empty member differs from its original declaration",
                )?;
                continue;
            }
            let (actual, actual_environment) =
                actual.ok_or("typed record member has no original Source graph")?;
            require(
                !actual_environment.is_poisoned(),
                "typed record member lost its frozen interpretation",
            )?;
            require(
                schema_work(work, |budget| {
                    expected.receive_schema(&actual, Some(&fresh), budget)
                })?,
                "typed record member differs from its original Source declaration",
            )?;
        }
        Ok(Some((schema, environment)))
    }

    pub(in crate::sema::record_bound_validation) fn original_observed_source_schema_with_work(
        &self,
        expression: &Expr,
        observation: usize,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
    ) -> Check<Option<OriginalSource>> {
        let fact = self
            .facts
            .expressions
            .get(observation)
            .ok_or("original Source graph root is outside its arena")?;
        self.original_source_root(expression, &fact.value, context, Some(observation), work)?;
        self.original_source_schema_inner(
            expression,
            &fact.value,
            context,
            sites,
            work,
            SourceVisit {
                depth: 0,
                observation: Some(observation),
            },
        )
    }

    pub(super) fn source_child_observation(
        &self,
        parent: usize,
        source: ril_compiler_core::ids::ExprId,
        context: InvocationContext,
        work: &mut usize,
    ) -> Check<usize> {
        use crate::sema::source_types::projection_receipts::{
            ProjectionOccurrence, ProjectionReceipts,
        };
        let record = self
            .facts
            .evaluations
            .get(parent)
            .ok_or("Source product parent has no actual occurrence")?;
        require(
            record.context == context,
            "Source product parent borrowed another invocation context",
        )?;
        let fact = self
            .facts
            .expressions
            .get(parent)
            .ok_or("Source product parent is outside its arena")?;
        let occurrence = ProjectionOccurrence {
            identity: record
                .identity
                .ok_or("Source product parent has no original activation")?,
            context,
            cause: fact.value.cause,
        };
        schema_work(work, |budget| {
            ProjectionReceipts::from_facts(self.facts).child_observation(occurrence, source, budget)
        })
        .map(|observation| observation.0 as usize)
    }

    pub(super) fn original_source_schema_inner(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        visit: SourceVisit,
    ) -> Check<Option<OriginalSource>> {
        *work = work
            .checked_sub(1)
            .ok_or("original Source graph work exhausted")?;
        require(
            visit.depth < 64,
            "original Source graph ancestry exceeds its bound",
        )?;
        let root =
            self.original_source_root(expression, value, context, visit.observation, work)?;
        if let Some(source) =
            self.original_key_name_source_schema(expression, value, context, root, work)?
        {
            return Ok(Some(source));
        }
        if let Some(source) =
            self.numeric_static_callee_source(expression, value, root, context, work)?
        {
            return Ok(Some(source));
        }
        if matches!(self.facts.expressions[root].value.ty, Ty::NumericHole(_)) {
            return self
                .original_numeric_source_schema(root, context, work)
                .map(Some);
        }
        if let Some(source) = self.storage_binding_source_schema(
            expression,
            value,
            context,
            visit.observation,
            SourceRead::Received,
        ) {
            let source = source?;
            if source.is_some() {
                self.authenticate_storage_read(root, sites, work)?;
            }
            return Ok(source);
        }
        if matches!(expression.kind, ExprKind::Generic { .. })
            && let Some(authenticated) =
                crate::sema::external_instance_validation::application_instance(
                    self.facts,
                    ril_compiler_core::ids::EvaluationOccurrenceId(
                        u32::try_from(root)
                            .map_err(|_| "foreign callee observation identity overflow")?,
                    ),
                    sites,
                    work,
                )?
        {
            let function = authenticated.function();
            let environment = function.typing_environment.clone();
            let scope = super::reception::environment_scope(&environment, work)?;
            *work = work
                .checked_sub(function.syntax.parameters.len() + function.syntax.annotations.len())
                .ok_or("foreign callable Source graph exceeds its work bound")?;
            let mut parameters = Vec::with_capacity(function.syntax.parameters.len());
            for parameter in &function.syntax.parameters {
                let header = parameter
                    .ty
                    .as_ref()
                    .ok_or("foreign callable has an untyped parameter")?;
                let (schema, selected_environment) =
                    self.source_type_header(header, &scope, environment.clone(), work)?;
                let dependent = schema_work(work, |budget| schema.requires_environment(budget))?;
                require(
                    !dependent || selected_environment.id() == environment.id(),
                    "foreign callable parameter borrowed another declaration environment",
                )?;
                parameters.push((parameter.mode, schema));
            }
            let result = if let Some(header) = &function.syntax.return_type {
                let (schema, selected_environment) =
                    self.source_type_header(header, &scope, environment.clone(), work)?;
                let dependent = schema_work(work, |budget| schema.requires_environment(budget))?;
                require(
                    !dependent || selected_environment.id() == environment.id(),
                    "foreign callable result borrowed another declaration environment",
                )?;
                schema
            } else {
                schema_work(work, |budget| SourceSchema::tuple(&[], None, budget))?
            };
            let mut annotations = Vec::with_capacity(function.syntax.annotations.len());
            for annotation in &function.syntax.annotations {
                *work = work
                    .checked_sub(1 + annotation.text.len().div_ceil(32))
                    .ok_or("foreign callable annotations exceed their work bound")?;
                annotations.push(annotation.text.clone());
            }
            let row = self.source_callable_row_identity(
                crate::sema::source_types::CallableRowOrigin::Declaration(
                    function
                        .hir_id
                        .ok_or("foreign callable row has no generated declaration")?,
                ),
                &function.syntax.annotations,
                &scope,
                &environment,
                work,
            )?;
            let schema = schema_work(work, |budget| {
                SourceSchema::callable_original(
                    &parameters,
                    &result,
                    &annotations,
                    row.as_ref(),
                    None,
                    budget,
                )
            })?;
            return Ok(Some((schema, environment)));
        }
        if let ExprKind::Generic { base, arguments } = &expression.kind
            && matches!(value.callables.as_slice(), [Callable::Named(_)])
        {
            let root =
                self.original_source_root(expression, value, context, visit.observation, work)?;
            source_scan_work(work, 1 + arguments.len())?;
            let hir = self
                .facts
                .semantic_hir
                .as_deref()
                .ok_or("generic named prefix has no original HIR")?;
            let original = expression
                .hir_id
                .and_then(|id| hir.expression(id))
                .ok_or("generic named prefix lost its original HIR node")?;
            let crate::hir::nodes::ExprKind::Generic {
                base: original_base,
                arguments: original_arguments,
            } = &original.kind
            else {
                return Err("generic named prefix has another original syntax role".into());
            };
            require(
                base.hir_id == Some(*original_base)
                    && arguments.len() == original_arguments.len()
                    && arguments
                        .iter()
                        .zip(original_arguments)
                        .all(|(actual, original)| actual.hir_id == Some(*original)),
                "generic named prefix changed its original base or Type arguments",
            )?;
            let source = base
                .hir_id
                .ok_or("generic callee base has no original HIR identity")?;
            let observation = self.source_child_observation(root, source, context, work)?;
            let actual = &self.facts.expressions[observation];
            require(
                crate::sema::evaluated::same_birth_value(&actual.value, value, work)
                    .map_err(|error| format!("generic named prefix value comparison: {error}"))?,
                "generic named prefix changed its original callable value",
            )?;
            return self.original_source_schema_inner(
                base,
                &actual.value,
                context,
                sites,
                work,
                SourceVisit {
                    depth: visit.depth + 1,
                    observation: Some(observation),
                },
            );
        }
        if let Some(source) = self
            .original_typed_record_source_schema(expression, value, context, sites, work, visit)?
        {
            return Ok(Some(source));
        }
        if let Some(source) =
            self.original_carrier_source_schema(expression, value, context, sites, work, visit)?
        {
            return Ok(source);
        }
        if let Some(source) =
            self.original_copy_source_schema(expression, value, context, sites, work, visit)?
        {
            return Ok(source);
        }
        if let Some(source) =
            self.original_composite_source_schema(expression, value, context, sites, work, visit)?
        {
            return Ok(Some(source));
        }
        let source =
            self.original_source_header_schema(expression, value, context, sites, work, visit)?;
        let Some((schema, environment)) = source else {
            return Ok(None);
        };
        if self.source_optional_projection(expression, value, context, visit.observation, work)? {
            let schema = schema_work(work, |budget| {
                schema.project_steps(
                    &[crate::sema::source_types::SourcePath::OptionalPayload],
                    budget,
                )
            })?;
            return Ok(Some((schema, environment)));
        }
        Ok(Some((schema, environment)))
    }

    /// A selected scalar comes from the independently replayed numeric term,
    /// while the historical expression keeps its original hole descriptor.
    /// Neither an erased current type nor a missing schema selects this path.
    pub(super) fn original_numeric_source_schema(
        &self,
        observation: usize,
        context: InvocationContext,
        work: &mut usize,
    ) -> Check<OriginalSource> {
        let observation_id = ril_compiler_core::ids::EvaluationOccurrenceId(
            u32::try_from(observation).map_err(|_| "numeric occurrence is outside its arena")?,
        );
        let (_, resolution) = crate::sema::numeric_selection::checked_resolution_in_query(
            self.facts,
            observation_id,
            &self.numeric_session,
            &self.source_query,
            work,
        )
        .map_err(|error| format!("numeric Source derivation could not be replayed: {error}"))?
        .ok_or("numeric Source derivation has no actual hole resolution")?;
        let schema = schema_work(work, |budget| {
            SourceSchema::scalar(
                crate::sema::evaluated::numeric_source_scalar(resolution.number_type),
                None,
                budget,
            )
        })?;
        let environment = self.source_graph_environment(context, Some(observation), work)?;
        Ok((schema, environment))
    }
}

#[cfg(test)]
mod closed_ingress_tests {
    use super::*;

    #[test]
    fn closed_witness_ingress_charges_before_validation_and_key_construction() {
        let program = crate::Session::new(
            ril_test::case_bytes(
                "tests/regressions/source-transport.ril::fresh-tuple-construction",
            )
            .to_vec(),
        )
        .verify()
        .unwrap();
        let replay = Replay::new(program.facts()).unwrap();
        let span = program.facts().expressions[0].span;
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
        let mut witness = crate::sema::model::SourceTypeWitness {
            key: crate::static_eval::normalized_argument_key(&syntax),
            syntax,
        };
        let environment = FrozenEnvironment::default();
        let mut work = 4_000_000;
        replay
            .closed_witness_source_schema(&witness, environment.clone(), &mut work)
            .unwrap();
        let used = 4_000_000 - work;
        let mut exact = used;
        replay
            .closed_witness_source_schema(&witness, environment.clone(), &mut exact)
            .unwrap();
        assert_eq!(exact, 0);
        for mut short in [0, used - 1] {
            assert!(
                replay
                    .closed_witness_source_schema(&witness, environment.clone(), &mut short)
                    .is_err()
            );
        }
        witness.key.push('x');
        assert!(
            replay
                .closed_witness_source_schema(&witness, environment.clone(), &mut 0)
                .unwrap_err()
                .contains("work bound")
        );
        assert!(
            replay
                .closed_witness_source_schema(&witness, environment, &mut 4_000_000)
                .unwrap_err()
                .contains("inconsistent")
        );
    }

    #[test]
    fn normalized_closed_witness_does_not_impersonate_an_original_hir_header() {
        let source = ril_test::case_source(
            "tests/regressions/source-transport.ril::fresh-tuple-construction",
        );
        let program = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let facts = program.facts();
        let replay = Replay::new(facts).unwrap();
        let sites = super::super::super::explicit_named::source_sites_base(facts).unwrap();
        let written = sites
            .bindings
            .iter()
            .find_map(|site| site.binding.ty.as_ref())
            .unwrap();
        let environment = FrozenEnvironment::default();
        let original = replay
            .source_type_header(
                written,
                &BoundScope::default(),
                environment.clone(),
                &mut 16384,
            )
            .unwrap();
        let mut witness = crate::sema::model::SourceTypeWitness {
            key: crate::static_eval::normalized_argument_key(written),
            syntax: written.clone(),
        };
        witness.syntax.hir_id = None;
        assert!(
            replay
                .source_type_header(
                    &witness.syntax,
                    &BoundScope::default(),
                    environment.clone(),
                    &mut 16384
                )
                .is_err()
        );
        let admitted = replay
            .closed_witness_source_schema(&witness, environment.clone(), &mut 16384)
            .unwrap();
        assert!(
            original
                .0
                .equivalent(&admitted.0, &mut WorkLimit::new(4096))
                .unwrap()
        );
        assert!(
            replay
                .closed_witness_source_schema(&witness, environment.clone(), &mut 0)
                .is_err()
        );
        witness.key.push_str("forged");
        assert!(
            replay
                .closed_witness_source_schema(&witness, environment, &mut 16384)
                .is_err()
        );
    }
}
