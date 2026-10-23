//! One graph reception relation for original named and public callable inputs.
use super::*;
use crate::sema::source_types::{SourceNode, SourceTypeId, SourceTypeQueries, SourceTypesError};

pub(super) struct NamedInputSchemas {
    pub(super) raw: Vec<Option<OriginalSource>>,
    pub(super) expected: Vec<Option<OriginalSource>>,
    pub(super) selected: BTreeMap<String, OriginalSource>,
}

pub(super) struct InputSourceOccurrence<'a> {
    pub(super) expression: &'a Expr,
    pub(super) value: &'a Value,
    pub(super) context: InvocationContext,
    pub(super) observation: usize,
}

pub(super) fn environment_scope(
    environment: &FrozenEnvironment,
    work: &mut usize,
) -> Check<BoundScope> {
    require(
        !environment.is_poisoned(),
        "input header has a poisoned declaration scope",
    )?;
    *work = work
        .checked_sub(environment.generic_context.len() + environment.bound_row_context.len())
        .ok_or("input declaration scope exceeds its work bound")?;
    for (name, identity) in &environment.generic_context {
        *work = work
            .checked_sub(name.len().div_ceil(32) + identity.len().div_ceil(32))
            .ok_or("input declaration binder names exceed their work bound")?;
    }
    for name in environment.bound_row_context.keys() {
        *work = work
            .checked_sub(name.len().div_ceil(32))
            .ok_or("input declaration row names exceed their work bound")?;
    }
    Ok(BoundScope {
        types: environment.generic_context.clone(),
        rows: environment.bound_row_context.clone(),
    })
}

impl Replay<'_> {
    pub(super) fn input_graph_required(
        &self,
        schema: &SourceSchema,
        work: &mut usize,
    ) -> Check<bool> {
        super::graph_sources::schema_work(work, |budget| {
            // Unknown coordinate absence is an obligation, not an exemption.
            // Validate completeness separately so a poison cannot take that
            // conservative branch, including when no argument is later read.
            if !schema.equivalent(schema, budget)? {
                return Err(SourceTypesError::Unresolved);
            }
            match schema.sensitivity(budget) {
                crate::sema::source_types::SourceSensitivity::Absent { .. } => Ok(false),
                crate::sema::source_types::SourceSensitivity::Sensitive { .. } => Ok(true),
                crate::sema::source_types::SourceSensitivity::Unknown {
                    reason: SourceTypesError::Unresolved,
                } => Ok(true),
                crate::sema::source_types::SourceSensitivity::Unknown { reason } => Err(reason),
            }
        })
    }

    pub(super) fn named_input_source_schemas(
        &self,
        call: &CopyInvocation,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
    ) -> Check<NamedInputSchemas> {
        let function = self.function(call.target)?;
        let scope = self.scope(call.target)?;
        *work = work
            .checked_sub(function.syntax.parameters.len() + self.facts.bindings.len())
            .ok_or("named Source header selection exceeds its work bound")?;
        let raw = function
            .syntax
            .parameters
            .iter()
            .map(|parameter| {
                let Some(syntax) = &parameter.ty else {
                    return Ok(None);
                };
                if !self.parameter_has_type_source(syntax, &scope)? {
                    return Ok(None);
                }
                self.source_type_header(syntax, &scope, function.typing_environment.clone(), work)
                    .map(Some)
            })
            .collect::<Check<Vec<_>>>()?;
        let mut selected = BTreeMap::<String, OriginalSource>::new();
        for binding in &self.facts.bindings {
            if !binding.parameter || binding.context.owner != Some(CallableOwner::Function(call.target))
                || binding.context.invocation != Some(call.id)
                || !self.facts.scopes.get(&binding.owner).is_some_and(|scope|
                    matches!(scope.origin, crate::sema::scopes::ScopeOrigin::Named(id) if id == call.id)) {
                continue;
            }
            require(
                !binding.typing_environment.is_poisoned(),
                "named input Source has a poisoned original environment",
            )?;
            for (identity, source) in
                self.source_selected_schemas(&binding.typing_environment, work)?
            {
                if let Some((previous, original)) = selected.get(&identity) {
                    let equivalent = super::graph_sources::schema_work(work, |budget| {
                        previous.equivalent(&source.0, budget)
                    })?;
                    let dependent = super::graph_sources::schema_work(work, |budget| {
                        previous.requires_environment(budget)
                    })?;
                    require(
                        equivalent && (!dependent || original.id() == source.1.id()),
                        "named formals disagree about their actual selected Source",
                    )?;
                } else {
                    selected.insert(identity, source);
                }
            }
        }
        let mut required = BTreeSet::new();
        for (schema, _) in raw.iter().flatten() {
            required.extend(super::graph_sources::schema_work(work, |budget| {
                schema.binder_identities(budget)
            })?);
        }
        // A complete declaration graph with no Type/row UID needs no actual
        // static selection. A missing selection for a genuine UID remains an
        // error; this is applicability derived from the original graph.
        let selected_keys = if required.is_empty() {
            BTreeMap::new()
        } else {
            self.input_selected_keys(call)?
        };
        for identity in required {
            *work = work
                .checked_sub(1 + identity.len().div_ceil(32))
                .ok_or("named Source selections exceed their work bound")?;
            if selected.contains_key(&identity) {
                continue;
            }
            let Some(key) = selected_keys.get(&identity) else {
                continue;
            };
            if matches!(key, ArgumentKey::Binder { identity: actual, .. } if actual == &identity) {
                continue;
            }
            // An original static argument or independently registered scoped
            // row is still an ingress. No existing graph is exported here.
            let source = self.original_input_selection_schema(call, &identity, key, sites, work)?;
            selected.insert(identity, source);
        }
        let expected = raw
            .iter()
            .map(|source| {
                source
                    .as_ref()
                    .map(|(schema, environment)| {
                        self.source_substitute_schema(
                            schema.clone(),
                            environment.clone(),
                            &selected,
                            work,
                        )
                    })
                    .transpose()
            })
            .collect::<Check<Vec<_>>>()?;
        Ok(NamedInputSchemas {
            raw,
            expected,
            selected,
        })
    }

    pub(super) fn original_input_selection_schema(
        &self,
        call: &CopyInvocation,
        identity: &str,
        key: &ArgumentKey,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
    ) -> Check<OriginalSource> {
        source_reception::complete(key, work)
            .ok_or("original static Source selection exceeds its complete key admission")?;
        *work = work
            .checked_sub(self.facts.effect_invocations.len())
            .ok_or("original static Source lookup exceeds its work bound")?;
        let row = self.input_static_environment(call)?;
        let owned = &row.arguments;
        *work = work
            .checked_sub(owned.len())
            .ok_or("original static Source lookup exceeds its work bound")?;
        *work = work
            .checked_sub(row.captured_arguments.len())
            .ok_or("captured static Source lookup exceeds its work bound")?;
        if let Some(argument) = owned
            .iter()
            .chain(&row.captured_arguments)
            .find(|argument| argument.binder == identity)
            && let Some(syntax) = argument
                .syntax
                .as_ref()
                .filter(|syntax| syntax.hir_id.is_some() || key.is_closed())
        {
            let (scope, environment) = if argument.definition == call.target
                && matches!(
                    call.entry.origin,
                    crate::sema::application_effect::EntryOrigin::SignatureProbe(_)
                ) {
                let hir = self
                    .facts
                    .semantic_hir
                    .as_deref()
                    .ok_or("signature selection lost its original HIR")?;
                let authenticated = super::graph_sources::schema_work(work, |budget| {
                    crate::sema::application_effect::signature_assumption(
                        call,
                        0,
                        hir,
                        &self.facts.bindings,
                        self.facts.allocation_history.len(),
                        budget,
                    )
                })?;
                (
                    environment_scope(authenticated.environment, work)?,
                    authenticated.environment.clone(),
                )
            } else if argument.definition == call.target {
                let context = self.input_caller_context(call)?;
                let scope = context.owner.map_or(Ok(BoundScope::default()), |owner| {
                    self.lambda_input_scope(owner, work)
                })?;
                let observation = call
                    .source_event
                    .and_then(|id| self.facts.copy_call_events.get(id.0 as usize))
                    .and_then(|event| event.callee_expression);
                (
                    scope,
                    self.source_graph_environment(context, observation, work)?,
                )
            } else {
                (
                    self.scope(call.target)?,
                    self.function(call.target)?.typing_environment.clone(),
                )
            };
            if key.is_closed() && argument.key.as_ref() == Some(key) {
                let normalized =
                    crate::static_eval::effects::bounded_argument_key(syntax, &BTreeMap::new())
                        .ok_or("normalized static Source exceeds its syntax admission")?;
                if &normalized == key {
                    // StaticArgumentWitness.syntax is also used for the
                    // normalized finite selection. That evidence has its
                    // own sealed/key-checked ingress, even if a compatibility
                    // projection kept an earlier syntax ID.
                    crate::static_eval::charge_type_syntax_clone(syntax, work)
                        .ok_or("normalized static Source copy exceeds its work bound")?;
                    let witness = crate::sema::model::SourceTypeWitness {
                        key: crate::static_eval::normalized_argument_key(syntax),
                        syntax: syntax.clone(),
                    };
                    return self.closed_witness_source_schema(&witness, environment, work);
                }
            }
            require(
                syntax.hir_id.is_some(),
                "normalized static Source has neither a matching closed witness nor an original header",
            )?;
            return self.source_type_header(syntax, &scope, environment, work);
        }
        if let ArgumentKey::Binder {
            identity,
            sort: StaticBinderSort::Type,
        } = key
            && matches!(call.entry.origin, crate::sema::application_effect::EntryOrigin::Application(event) if call.source_event == Some(event))
        {
            // A caller UID may occur below a product's root. Its actual
            // argument graph owns the interpretation, not the creation Γ of
            // whichever declaration registered the UID spelling.
            require(
                self.input_type_sort(identity)?,
                "actual input Source projection requires a genuine Type UID",
            )?;
            source_scan_work(work, call.entry.arguments.len())?;
            let mut selected: Option<OriginalSource> = None;
            for slot in 0..call.entry.arguments.len() {
                let Some((schema, environment)) =
                    self.named_entry_source_schema_if_known(call, slot, sites, work)?
                else {
                    continue;
                };
                let Some(schema) = super::graph_sources::schema_work(work, |budget| {
                    schema.binder_view(identity, budget)
                })?
                else {
                    continue;
                };
                if let Some((original, original_environment)) = &selected {
                    require(
                        original_environment.id() == environment.id()
                            && super::graph_sources::schema_work(work, |budget| {
                                original.equivalent(&schema, budget)
                            })?,
                        "actual inputs disagree about the original Source of a selected UID",
                    )?;
                } else {
                    selected = Some((schema, environment));
                }
            }
            if let Some(selected) = selected {
                return Ok(selected);
            }
        }
        let fallback = self.function(call.target)?.typing_environment.clone();
        let (schema, _) = self.source_header_schema(key, fallback.clone(), work)?;
        if !super::graph_sources::schema_work(work, |budget| schema.requires_environment(budget))? {
            return Ok((schema, fallback));
        }
        require(
            !super::graph_sources::schema_work(work, |budget| {
                schema.requires_declaration_environment(budget)
            })?,
            "a lexical static Source needs its original header or actual graph",
        )?;
        let identities =
            super::graph_sources::schema_work(work, |budget| schema.binder_identities(budget))?;
        let mut environment = None;
        for identity in identities {
            *work = work
                .checked_sub(self.facts.bound_rows.len() + self.facts.functions.len() + 1)
                .ok_or("static Source declaration environments exceed their work bound")?;
            let definition = if let Some(binder) = self.facts.generic_binders.get(&identity) {
                require(
                    self.input_type_sort(&identity)?,
                    "a static coordinate cannot become a Source Type UID",
                )?;
                binder.definition
            } else {
                let mut rows = self.facts.bound_rows.iter().filter(|row|
                    matches!(&row.identity, RowIdentity::Binder(actual) if actual == &identity));
                let row = rows
                    .next()
                    .ok_or("static Source tail has no genuine declaration")?;
                require(
                    rows.next().is_none(),
                    "static Source tail has multiple declarations",
                )?;
                row.definition
            };
            let mut functions = self
                .facts
                .functions
                .iter()
                .filter(|function| function.definition == definition);
            let declaration = functions
                .next()
                .ok_or("static Source binder has no original function")?;
            require(
                functions.next().is_none() && !declaration.typing_environment.is_poisoned(),
                "static Source binder has no unique frozen declaration environment",
            )?;
            if let Some(previous) = &environment {
                require(
                    FrozenEnvironment::id(previous) == declaration.typing_environment.id(),
                    "static Source combines different declaration environments",
                )?;
            } else {
                environment = Some(declaration.typing_environment.clone())
            }
        }
        Ok((
            schema,
            environment.ok_or("static Source lost its original interpretation")?,
        ))
    }

    pub(super) fn receive_input_source_graph(
        &self,
        expected: &SourceSchema,
        actual: Option<&OriginalSource>,
        fresh: &source_reception::Construction,
        work: &mut usize,
    ) -> Check {
        let answer = super::graph_sources::schema_work(work, |budget| {
            if actual.is_some_and(|(_, environment)| environment.is_poisoned()) {
                return Err(SourceTypesError::Unresolved);
            }
            if let Some(answer) = expected.empty_context(fresh, budget)? {
                if let Some((source, _)) = actual
                    && !source.equivalent(source, budget)?
                {
                    return Err(SourceTypesError::Unresolved);
                }
                return Ok(answer);
            }
            let (source, environment) = actual.ok_or(SourceTypesError::Unresolved)?;
            if environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            expected.receive_schema(source, Some(fresh), budget)
        })?;
        require(
            answer,
            "call input original whole Source does not prove its receiving coordinates",
        )
    }

    pub(super) fn input_source_reception_schema(
        &self,
        expected: &SourceSchema,
        occurrence: InputSourceOccurrence<'_>,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
    ) -> Check<Option<OriginalSource>> {
        // Establish the physical occurrence before an actual empty literal is
        // allowed to omit its unavailable element Source.
        let actual = self.original_source_schema_inner(
            occurrence.expression,
            occurrence.value,
            occurrence.context,
            sites,
            work,
            SourceVisit {
                depth: 0,
                observation: Some(occurrence.observation),
            },
        )?;
        let fresh = source_reception::construction(occurrence.expression, work)
            .ok_or("call input construction exceeds its work bound")?;
        self.receive_input_source_graph(expected, actual.as_ref(), &fresh, work)?;
        Ok(actual)
    }

    /// Additional owned row equations after receiving has checked complete
    /// source compatibility. This query grants no receiving or value proof.
    pub(super) fn input_row_graph_equations(
        &self,
        raw: &SourceSchema,
        actual: &SourceSchema,
        selected: &BTreeMap<String, OriginalSource>,
        owner: DefinitionId,
        work: &mut usize,
    ) -> Check {
        *work = work
            .checked_sub(1)
            .ok_or("call input row graph work exhausted")?;
        let mut pending = vec![(raw.clone(), actual.clone())];
        let mut seen = BTreeSet::new();
        while let Some((raw, actual)) = pending.pop() {
            let (left, right) = super::graph_sources::schema_work(work, |budget| {
                Ok((read_root(&raw, budget)?, read_root(&actual, budget)?))
            })?;
            *work = work
                .checked_sub(1)
                .ok_or("call input row graph work exhausted")?;
            if !seen.insert((left, right)) {
                continue;
            }
            let (raw_types, _) = raw.graph();
            let (actual_types, _) = actual.graph();
            let left_node = raw_types.get(left).map_err(|error| error.to_string())?;
            let right_node = actual_types.get(right).map_err(|error| error.to_string())?;
            let mut pairs = Vec::new();
            match (left_node, right_node) {
                (SourceNode::Record { .. }, SourceNode::Record { .. }) => {
                    let (required, row) =
                        super::graph_sources::schema_work(work, |budget| raw.record_parts(budget))?
                            .ok_or("row equation lost its original record")?;
                    let (present, tail) = super::graph_sources::schema_work(work, |budget| {
                        actual.record_parts(budget)
                    })?
                    .ok_or("row equation lost its actual record")?;
                    *work = work
                        .checked_sub(required.len() + present.len())
                        .ok_or("call input row fields exceed their work bound")?;
                    let present_map: BTreeMap<_, _> = present
                        .iter()
                        .map(|(name, mode, source)| (name.as_str(), (*mode, source)))
                        .collect();
                    for (name, mode, source) in &required {
                        let (actual_mode, actual_source) = present_map
                            .get(name.as_str())
                            .ok_or("call input row equation lost a genuine required field")?;
                        require(
                            mode == actual_mode,
                            "call input row equation changed a field mode",
                        )?;
                        pairs.push((source.clone(), (*actual_source).clone()));
                    }
                    if let Some(row) = row {
                        self.input_row_graph_remainder(
                            &row,
                            &actual,
                            &required,
                            &present,
                            tail.as_ref(),
                            selected,
                            owner,
                            work,
                        )?;
                    }
                }
                (SourceNode::Tuple(_), SourceNode::Tuple(_)) => {
                    let left =
                        super::graph_sources::schema_work(work, |budget| raw.tuple_parts(budget))?
                            .ok_or("row equation lost its original tuple")?;
                    let right = super::graph_sources::schema_work(work, |budget| {
                        actual.tuple_parts(budget)
                    })?
                    .ok_or("row equation lost its actual tuple")?;
                    require(
                        left.len() == right.len(),
                        "row equation changed its tuple arity",
                    )?;
                    pairs.extend(left.into_iter().zip(right));
                }
                (SourceNode::Array { .. }, SourceNode::Array { .. }) => {
                    let (_, left) =
                        super::graph_sources::schema_work(work, |budget| raw.array_parts(budget))?
                            .ok_or("row equation lost its original array")?;
                    let (_, right) = super::graph_sources::schema_work(work, |budget| {
                        actual.array_parts(budget)
                    })?
                    .ok_or("row equation lost its actual array")?;
                    pairs.push((left, right));
                }
                (
                    SourceNode::Map { key: lk, value: lv },
                    SourceNode::Map { key: rk, value: rv },
                ) => {
                    for (left, right) in [(*lk, *rk), (*lv, *rv)] {
                        pairs.push(super::graph_sources::schema_work(work, |budget| {
                            Ok((raw.view_at(left, budget)?, actual.view_at(right, budget)?))
                        })?);
                    }
                }
                (
                    SourceNode::Container {
                        kind: left_kind,
                        arguments: left,
                    },
                    SourceNode::Container {
                        kind: right_kind,
                        arguments: right,
                    },
                ) if left_kind == right_kind => {
                    require(
                        left.len() == right.len(),
                        "row equation changed its container arity",
                    )?;
                    *work = work
                        .checked_sub(left.len())
                        .ok_or("container row equation work exhausted")?;
                    for (left, right) in left.iter().zip(right) {
                        pairs.push(super::graph_sources::schema_work(work, |budget| {
                            Ok((raw.view_at(*left, budget)?, actual.view_at(*right, budget)?))
                        })?);
                    }
                }
                (
                    SourceNode::OpaqueName {
                        name: left_name,
                        arguments: left,
                    },
                    SourceNode::OpaqueName {
                        name: right_name,
                        arguments: right,
                    },
                ) if left_name == right_name => {
                    require(
                        left.len() == right.len(),
                        "row equation changed its nominal argument count",
                    )?;
                    *work = work
                        .checked_sub(left.len())
                        .ok_or("nominal row equation work exhausted")?;
                    for (left, right) in left.iter().zip(right) {
                        pairs.push(super::graph_sources::schema_work(work, |budget| {
                            Ok((raw.view_at(*left, budget)?, actual.view_at(*right, budget)?))
                        })?);
                    }
                }
                // Callable parameter/result variance belongs to receive_schema.
                // Its own actual invocation checks row equations at that
                // boundary; this call cannot impose an invariant equation on
                // a contravariant callback parameter or covariant result.
                (SourceNode::OpaqueComputation(_) | SourceNode::Unresolved { .. }, _)
                | (_, SourceNode::OpaqueComputation(_) | SourceNode::Unresolved { .. }) => {
                    return Err("call input row equation contains an unresolved Source".into());
                }
                _ => {}
            }
            *work = work
                .checked_sub(pairs.len())
                .ok_or("row equation edges exceed their work bound")?;
            pending.extend(pairs);
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn input_row_graph_remainder(
        &self,
        row: &SourceSchema,
        actual: &SourceSchema,
        required: &[(String, bool, SourceSchema)],
        present: &[(String, bool, SourceSchema)],
        tail: Option<&SourceSchema>,
        selected: &BTreeMap<String, OriginalSource>,
        owner: DefinitionId,
        work: &mut usize,
    ) -> Check {
        let identity =
            super::graph_sources::schema_work(work, |budget| row.bare_binder_identity(budget))?
                .ok_or("call input original row has no genuine rigid binder")?;
        *work = work
            .checked_sub(self.facts.bound_rows.len())
            .ok_or("call input row declaration lookup exceeds its work bound")?;
        let declarations: Vec<_> = self
            .facts
            .bound_rows
            .iter()
            .filter(|row| {
                row.definition == owner
                    && matches!(&row.identity, RowIdentity::Binder(actual) if actual == &identity)
            })
            .collect();
        let (residual_owner, ordinal, declared_lacks) = match declarations.as_slice() {
            [] => {
                let Some(binder) = self.facts.generic_binders.get(&identity) else {
                    *work = work
                        .checked_sub(self.facts.bound_rows.len())
                        .ok_or("captured row declaration lookup exceeds its work bound")?;
                    let mut enclosing = self.facts.bound_rows.iter().filter(|row|
                        matches!(&row.identity, RowIdentity::Binder(actual) if actual == &identity));
                    let declaration = enclosing
                        .next()
                        .ok_or("call input row has no genuine declaration")?;
                    require(
                        enclosing.next().is_none() && declaration.definition != owner,
                        "captured row changed its original declaration identity",
                    )?;
                    return Ok(());
                };
                if binder.definition != owner {
                    // A captured Type parameter, just like an enclosing
                    // implicit residual, remains rigid at this boundary.
                    return Ok(());
                }
                *work = work
                    .checked_sub(
                        self.facts.generic_binders.len()
                            + self.facts.functions.len()
                            + required.len(),
                    )
                    .ok_or("explicit Type row admission exceeds its work bound")?;
                require(
                    self.input_type_sort(&identity)?,
                    "call input row is not a genuine Type parameter",
                )?;
                let mut lacks = BTreeSet::new();
                for (name, _, _) in required {
                    *work = work
                        .checked_sub(name.len().div_ceil(32))
                        .ok_or("explicit Type row labels exceed their work bound")?;
                    lacks.insert(name.clone());
                }
                // A direct formal `{fields,..S}` can give a real Type
                // parameter its row role without a GenericRecordBound or
                // BoundRowDeclaration. Its original Source fields establish
                // these absences; S still needs the same exact equation.
                (
                    format!("call-source:{}:type-row", owner.0),
                    u64::from(binder.index),
                    lacks,
                )
            }
            [declaration] => {
                *work = work
                    .checked_sub(declaration.lacks.len())
                    .ok_or("declared row lacks exceed their copy work bound")?;
                for name in &declaration.lacks {
                    *work = work
                        .checked_sub(name.len().div_ceil(32))
                        .ok_or("declared row labels exceed their copy work bound")?;
                }
                (
                    format!("call-source:{}", owner.0),
                    u64::from(declaration.id.0),
                    declaration.lacks.clone(),
                )
            }
            _ => return Err("call input owned row has multiple declaration identities".into()),
        };
        let actual_tail = if let Some(tail) = tail {
            let identity = super::graph_sources::schema_work(work, |budget| {
                tail.bare_binder_identity(budget)
            })?
            .ok_or("actual row has no canonical rigid tail")?;
            *work = work
                .checked_sub(self.facts.bound_rows.len())
                .ok_or("actual row declaration lookup exceeds its work bound")?;
            let mut declarations = self.facts.bound_rows.iter().filter(
                |row| matches!(&row.identity, RowIdentity::Binder(actual) if actual == &identity),
            );
            if let Some(declaration) = declarations.next() {
                require(
                    declarations.next().is_none(),
                    "actual row has multiple declaration identities",
                )?;
                for name in &declaration.lacks {
                    *work = work
                        .checked_sub(1 + name.len().div_ceil(32))
                        .ok_or("actual rigid row lacks exceed their work bound")?;
                }
                RowTail::Open(OpenTail {
                    identity: declaration.identity.clone(),
                    lacks: declaration.lacks.clone(),
                })
            } else {
                *work = work
                    .checked_sub(
                        self.facts.generic_binders.len()
                            + self.facts.functions.len()
                            + present.len(),
                    )
                    .ok_or("actual Type row admission exceeds its work bound")?;
                require(
                    self.input_type_sort(&identity)?,
                    "actual row has no genuine Type declaration",
                )?;
                let mut lacks = BTreeSet::new();
                for (name, _, _) in present {
                    *work = work
                        .checked_sub(name.len().div_ceil(32))
                        .ok_or("actual Type row labels exceed their work bound")?;
                    lacks.insert(name.clone());
                }
                // These labels belong to the independently authenticated
                // actual Source record, rather than its erased runtime Ty.
                // Its caller Type UID remains rigid, including recursion.
                RowTail::Open(OpenTail {
                    identity: RowIdentity::Binder(identity),
                    lacks,
                })
            }
        } else {
            RowTail::Closed
        };
        for (name, _, _) in required.iter().chain(present) {
            *work = work
                .checked_sub(1 + name.len().div_ceil(32).saturating_mul(8))
                .ok_or("row solver field names exceed their work bound")?;
        }
        for name in &declared_lacks {
            *work = work
                .checked_sub(1 + name.len().div_ceil(32).saturating_mul(4))
                .ok_or("row solver declared lacks exceed their work bound")?;
        }
        let tail_lacks = match &actual_tail {
            RowTail::Closed => 0,
            RowTail::Open(tail) => tail.lacks.len(),
        };
        let field_count = required
            .len()
            .checked_add(present.len())
            .and_then(|count| count.checked_add(declared_lacks.len()))
            .and_then(|count| count.checked_add(tail_lacks))
            .and_then(|count| count.checked_add(1))
            .ok_or("row solver input count overflow")?;
        let solver_work = field_count
            .checked_add(1)
            .and_then(|next| field_count.checked_mul(next))
            .ok_or("row solver work overflow")?;
        *work = work
            .checked_sub(solver_work)
            .ok_or("row solver exceeds its Source work bound")?;
        let fields: BTreeMap<_, _> = present
            .iter()
            .map(|(name, mode, schema)| (name.clone(), (*mode, schema.root_id())))
            .collect();
        let required_fields = required
            .iter()
            .map(|(name, mode, _)| {
                let (actual_mode, value) = fields
                    .get(name)
                    .ok_or("row equation lost a required field")?;
                require(
                    mode == actual_mode,
                    "row equation changed a required field mode",
                )?;
                Ok((name.clone(), (*actual_mode, *value)))
            })
            .collect::<Check<BTreeMap<_, _>>>()?;
        let actual_row = Row {
            fields,
            tail: actual_tail.clone(),
        };
        let residual = OpenTail {
            identity: RowIdentity::Fresh {
                owner: residual_owner,
                ordinal,
            },
            lacks: declared_lacks,
        };
        let mut solver = Solver::new("original call input", [residual.identity.clone()]);
        if let RowTail::Open(tail) = &actual_row.tail {
            solver
                .declare_rigid(tail.identity.clone(), tail.lacks.clone())
                .map_err(|_| "actual row changed its genuine rigid role")?;
        }
        let remainder = crate::sema::record_bound_shapes::entail(
            &mut solver,
            &required_fields,
            Some(&residual),
            &actual_row,
        )
        .map_err(|_| "selected row does not solve its actual Source equation")?;
        let excluded: BTreeSet<_> = required.iter().map(|(name, _, _)| name.clone()).collect();
        let difference = Row {
            fields: actual_row
                .fields
                .into_iter()
                .filter(|(name, _)| !excluded.contains(name))
                .collect(),
            tail: actual_tail,
        };
        let difference = solver
            .normalize(&difference)
            .map_err(|_| "actual row remainder changed its original rigid constraints")?;
        require(
            remainder == difference,
            "row solver changed the actual remainder graph or rigid tail",
        )?;
        let remainder = super::graph_sources::schema_work(work, |budget| {
            actual.record_remainder(&excluded, budget)
        })?;
        let choice = selected
            .get(&identity)
            .map(|source| &source.0)
            .unwrap_or(row);
        require(
            super::graph_sources::schema_work(work, |budget| {
                choice.equivalent(&remainder, budget)
            })?,
            "selected closed/open row differs from its independently solved actual remainder",
        )
    }
}

fn read_root(
    schema: &SourceSchema,
    work: &mut WorkLimit,
) -> Result<SourceTypeId, SourceTypesError> {
    let (types, mut root) = schema.graph();
    let mut seen = BTreeSet::new();
    loop {
        work.charge(1)?;
        root = types.unalias(root, work)?;
        if !seen.insert(root) {
            return Err(SourceTypesError::AliasCycle);
        }
        let node = types.get(root)?;
        match node {
            SourceNode::Container {
                kind: crate::sema::source_types::SourceContainer::Immutable,
                arguments,
            } => {
                if arguments.len() != 1 {
                    return Err(SourceTypesError::InvalidContainer);
                }
                root = arguments[0];
            }
            _ => return Ok(root),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::source_types::SourceLength;

    #[test]
    fn a_selected_caller_uid_keeps_the_real_input_graph_environment() {
        let source = ril_test::case_source(
            "tests/regressions/source-transport.ril::bounded-record-tuple-return",
        );
        for layout in ["pointer32", "pointer64"] {
            let program = crate::Session::with_options(
                source.as_bytes().to_vec(),
                crate::CheckOptions {
                    target: layout.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|error| panic!("{layout}: {error:?}"));
            let facts = program.facts();
            let first = facts
                .functions
                .iter()
                .find(|function| function.syntax.name == "first")
                .unwrap()
                .definition;
            let forward = facts
                .functions
                .iter()
                .find(|function| function.syntax.name == "forward")
                .unwrap();
            let call = facts
                .copy_invocations
                .iter()
                .find(|call| {
                    call.target == first
                        && call.caller_owner == Some(CallableOwner::Function(forward.definition))
                        && matches!(
                            call.entry.origin,
                            crate::sema::application_effect::EntryOrigin::Application(_)
                        )
                })
                .unwrap();
            let sites = super::super::super::explicit_named::source_sites_base(facts).unwrap();
            let replay = Replay::new(facts).unwrap();
            let mut work = 262_144;
            let argument = &replay.input_static_arguments(call).unwrap()[0];
            let key = argument.key.as_ref().unwrap();
            let ArgumentKey::Binder {
                identity,
                sort: StaticBinderSort::Type,
            } = key
            else {
                panic!("the real explicit argument must select the caller's rigid UID")
            };
            let (input, environment) = replay
                .named_entry_source_schema(call, 0, &sites, &mut work)
                .unwrap();
            let projected = input
                .binder_view(identity, &mut WorkLimit::new(16384))
                .unwrap()
                .unwrap();
            assert_ne!(
                environment.id(),
                forward.typing_environment.id(),
                "the fixture must distinguish input Γ from declaration Γ"
            );
            let selected = replay
                .original_input_selection_schema(call, &argument.binder, key, &sites, &mut work)
                .unwrap();
            assert_eq!(selected.1.id(), environment.id());
            assert!(
                selected
                    .0
                    .equivalent_in(
                        &projected,
                        &selected.1,
                        &environment,
                        &mut WorkLimit::new(16384)
                    )
                    .unwrap()
            );
            assert!(
                replay
                    .original_input_selection_schema(call, &argument.binder, key, &sites, &mut 0)
                    .is_err()
            );

            let mut changed = facts.clone();
            let event = call.source_event.unwrap();
            let preparation = changed
                .call_arguments
                .iter_mut()
                .find(|row| row.source_event == event)
                .unwrap();
            assert!(preparation.supplied.remove(&0).is_some());
            assert!(
                Replay::new(&changed)
                    .and_then(|replay| {
                        replay.original_input_selection_schema(
                            &changed.copy_invocations[call.id.0 as usize],
                            &argument.binder,
                            key,
                            &sites,
                            &mut 262_144,
                        )
                    })
                    .is_err(),
                "a missing actual input must not fall back to the declaration Γ"
            );
        }
    }

    #[test]
    fn recursive_input_sources_only_demand_real_static_receipts_for_graph_dependencies() {
        let source = ril_test::case_source(
            "tests/regressions/source-transport.ril::recursive-static-input-receipts",
        );
        let program = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let baseline = program.facts();
        let definition = |name: &str| {
            baseline
                .functions
                .iter()
                .find(|function| function.syntax.name == name)
                .unwrap()
                .definition
        };
        let down = definition("down");
        let recursive = |target| {
            baseline
                .copy_invocations
                .iter()
                .find(|call| call.target == target && call.caller == Some(target))
                .unwrap()
        };
        let down_call = recursive(down).id;
        let mut no_static = baseline.clone();
        assert!(
            no_static
                .effect_invocations
                .iter()
                .any(|row| row.invocation == Some(down_call))
        );
        no_static
            .effect_invocations
            .retain(|row| row.invocation != Some(down_call));
        let replay = Replay::new(&no_static).unwrap();
        let sites = super::super::super::explicit_named::source_sites_base(&no_static).unwrap();
        let schemas = replay
            .named_input_source_schemas(
                &no_static.copy_invocations[down_call.0 as usize],
                &sites,
                &mut 262_144,
            )
            .unwrap();
        assert!(schemas.selected.is_empty());
        assert!(schemas.raw.iter().flatten().all(|(schema, _)| {
            schema
                .binder_identities(&mut WorkLimit::new(4096))
                .unwrap()
                .is_empty()
        }));

        let recur_call = recursive(definition("recur")).id;
        let sibling_call = recursive(definition("sibling")).id;
        let expected_row = baseline
            .effect_invocations
            .iter()
            .find(|row| row.invocation == Some(recur_call))
            .unwrap();
        assert_eq!(expected_row.arguments.len(), 1);
        let sibling_row = baseline
            .effect_invocations
            .iter()
            .find(|row| row.invocation == Some(sibling_call))
            .unwrap();
        assert_ne!(
            expected_row.arguments[0].binder,
            sibling_row.arguments[0].binder
        );
        let replay = Replay::new(baseline).unwrap();
        let sites = super::super::super::explicit_named::source_sites_base(baseline).unwrap();
        let original = replay
            .named_input_source_schemas(
                &baseline.copy_invocations[recur_call.0 as usize],
                &sites,
                &mut 262_144,
            )
            .unwrap();
        assert!(original.raw.iter().flatten().any(|(schema, _)| {
            !schema
                .binder_identities(&mut WorkLimit::new(4096))
                .unwrap()
                .is_empty()
        }));
        for mutation in 0..4 {
            let mut changed = baseline.clone();
            let index = changed
                .effect_invocations
                .iter()
                .position(|row| row.invocation == Some(recur_call))
                .unwrap();
            match mutation {
                0 => {
                    changed.effect_invocations.remove(index);
                }
                1 => changed
                    .effect_invocations
                    .push(changed.effect_invocations[index].clone()),
                2 => {
                    changed.effect_invocations[index].arguments[0].binder =
                        sibling_row.arguments[0].binder.clone()
                }
                3 => {
                    changed.effect_invocations[index] = sibling_row.clone();
                }
                _ => unreachable!(),
            }
            let replay = Replay::new(&changed).unwrap();
            let sites = super::super::super::explicit_named::source_sites_base(&changed).unwrap();
            assert!(
                replay
                    .named_input_source_schemas(
                        &changed.copy_invocations[recur_call.0 as usize],
                        &sites,
                        &mut 262_144
                    )
                    .is_err(),
                "recursive static receipt mutation {mutation} was accepted"
            );
        }
    }

    #[test]
    fn row_graph_equations_keep_hidden_extents_modes_and_their_work_bound() {
        let source = ril_test::case_source(
            "tests/regressions/source-transport.ril::composed-row-with-array-and-callback",
        );
        let program = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let facts = program.facts();
        let replay = Replay::new(facts).unwrap();
        let sites = super::super::super::explicit_named::source_sites_base(facts).unwrap();
        let target = facts
            .functions
            .iter()
            .find(|function| function.syntax.name == "outer")
            .unwrap()
            .definition;
        let call = facts
            .copy_invocations
            .iter()
            .find(|call| {
                call.target == target
            && call.source_event.is_some() && call.entry.arguments.first().is_some_and(|value|
                matches!(&value.value().ty, Ty::Record(fields) if fields.contains_key("extra")))
            })
            .expect("fixture must enter its real outer call with the complete record");
        let schemas = replay
            .named_input_source_schemas(call, &sites, &mut 262_144)
            .unwrap();
        let raw = &schemas.raw[0].as_ref().unwrap().0;
        let actual = replay
            .named_entry_source_schema(call, 0, &sites, &mut 262_144)
            .unwrap();
        replay
            .input_row_graph_equations(raw, &actual.0, &schemas.selected, target, &mut 262_144)
            .unwrap();
        assert!(
            replay
                .input_row_graph_equations(raw, &actual.0, &schemas.selected, target, &mut 0)
                .is_err()
        );
        let (_, tail) = raw
            .record_parts(&mut WorkLimit::new(4096))
            .unwrap()
            .unwrap();
        let identity = tail
            .unwrap()
            .bare_binder_identity(&mut WorkLimit::new(4096))
            .unwrap()
            .unwrap();
        assert_eq!(facts.generic_binders[&identity].definition, target);
        assert!(
            !facts.bound_rows.iter().any(|row| {
                row.definition == target
                    && matches!(&row.identity, RowIdentity::Binder(actual) if actual == &identity)
            }),
            "the explicit formal Type row must be checked without an implicit-bound row receipt"
        );
        let selected = schemas
            .selected
            .get(&identity)
            .expect("actual row must have a selected Source graph");
        for mutation in 0..2 {
            let (mut fields, tail) = selected
                .0
                .record_parts(&mut WorkLimit::new(16384))
                .unwrap()
                .unwrap();
            let extra = fields
                .iter_mut()
                .find(|(name, _, _)| name == "extra")
                .unwrap();
            if mutation == 0 {
                let (outer_length, inner) = extra
                    .2
                    .array_parts(&mut WorkLimit::new(4096))
                    .unwrap()
                    .unwrap();
                assert_eq!(outer_length, SourceLength::Fixed(0));
                let (inner_length, item) = inner
                    .array_parts(&mut WorkLimit::new(4096))
                    .unwrap()
                    .unwrap();
                assert_eq!(inner_length, SourceLength::Fixed(3));
                let wrong_inner = SourceSchema::array(
                    SourceLength::Fixed(2),
                    &item,
                    None,
                    &mut WorkLimit::new(4096),
                )
                .unwrap();
                extra.2 = SourceSchema::array(
                    outer_length,
                    &wrong_inner,
                    None,
                    &mut WorkLimit::new(4096),
                )
                .unwrap();
            } else {
                extra.1 = !extra.1
            }
            let wrong = SourceSchema::record(
                &fields,
                tail.as_ref(),
                selected.0.original(),
                &mut WorkLimit::new(16384),
            )
            .unwrap();
            let mut choices = schemas.selected.clone();
            choices.get_mut(&identity).unwrap().0 = wrong;
            assert!(
                replay
                    .input_row_graph_equations(raw, &actual.0, &choices, target, &mut 262_144)
                    .is_err(),
                "row mutation {mutation} was accepted"
            );
        }
        let unknown = SourceSchema::import(
            &ArgumentKey::Closed("unknown row source".into()),
            None,
            &mut WorkLimit::new(4096),
        )
        .unwrap();
        assert!(
            replay
                .input_row_graph_equations(raw, &unknown, &schemas.selected, target, &mut 262_144)
                .is_err()
        );
    }
}
