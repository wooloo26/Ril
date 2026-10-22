//! Declaration normalization and actual instance selection are separate steps.
//! This keeps open rows and qualified callable fields out of erased Ty reifiers.
use super::*;
use crate::sema::effect_identity::StaticBinderSort;

impl Checker {
    pub(in crate::sema::checker) fn selected_input_schema(
        &self,
        schema: SourceSchema,
        environment: FrozenEnvironment,
        work: &mut WorkLimit,
    ) -> Result<(SourceSchema, FrozenEnvironment), SourceTypesError> {
        let required = schema.binder_identities(work)?;
        if schema.root_is_binder(work)?
            && let Some(identity) = required.first()
            && schema.equivalent_key(
                &ArgumentKey::Binder {
                    identity: identity.clone(),
                    sort: StaticBinderSort::Type,
                },
                work,
            )?
            && let Some(selected) = environment.generic_sources.get(identity)
        {
            if selected.environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            return Ok((selected.schema.clone(), selected.environment.clone()));
        }
        work.charge(environment.generic_sources.len())?;
        let mut selected = BTreeMap::new();
        let mut dependencies = Vec::new();
        for (identity, source) in &environment.generic_sources {
            work.text(identity)?;
            if source.environment.is_poisoned() {
                return Err(SourceTypesError::Unresolved);
            }
            selected.insert(identity.clone(), source.schema.clone());
            if required.contains(identity) {
                dependencies.push((&source.schema, &source.environment));
            }
        }
        let result = schema.substitute(&selected, work)?;
        if !result.requires_environment(work)? {
            return Ok((result, environment));
        }
        if schema.requires_declaration_environment(work)? {
            dependencies.push((&schema, &environment));
        }
        let selected_environment =
            super::producing_result::result_environment(dependencies, &environment, work)?;
        Ok((result, selected_environment))
    }
    pub(in crate::sema::checker) fn actual_input_source_schemas(
        &mut self,
        definition: ril_compiler_core::ids::DefinitionId,
        event: Option<CopyCallEventId>,
        span: Span,
        work: &mut WorkLimit,
    ) -> Result<BTreeMap<String, SourceSchema>, SourceTypesError> {
        let mut selected = BTreeMap::new();
        let mut deferred = Vec::new();
        let mut owned = Vec::new();
        work.charge(self.functions.len())?;
        let info = self
            .functions
            .iter()
            .find(|info| info.definition == definition)
            .ok_or(SourceTypesError::MissingNode)?;
        work.charge(info.syntax.generics.len() + info.typing_environment.generic_context.len())?;
        for (index, parameter) in info.syntax.generics.iter().enumerate() {
            let identity = self
                .type_source
                .environment
                .generic_context
                .get(&parameter.name)
                .ok_or(SourceTypesError::Unresolved)?;
            if !self.generic_binders.get(identity).is_some_and(|binder| {
                binder.definition == definition
                    && binder.index as usize == index
                    && binder.name == parameter.name
            }) {
                return Err(SourceTypesError::Unresolved);
            }
            work.text(&parameter.name)?;
            work.text(identity)?;
            owned.push((parameter.name.clone(), identity.clone()));
        }
        for (name, identity) in &info.typing_environment.generic_context {
            if !owned.iter().any(|(_, actual)| actual == identity) {
                work.text(name)?;
                work.text(identity)?;
                owned.push((name.clone(), identity.clone()));
            }
        }
        for (name, identity) in owned {
            work.charge(self.functions.len() + 1)?;
            let binder = self
                .generic_binders
                .get(&identity)
                .ok_or(SourceTypesError::Unresolved)?;
            let parameter = self
                .functions
                .iter()
                .find(|function| function.definition == binder.definition)
                .and_then(|function| function.syntax.generics.get(binder.index as usize))
                .ok_or(SourceTypesError::Unresolved)?;
            if !crate::sema::record_bounds::certifies_type_sort(
                &identity,
                binder,
                parameter,
                &self.record_bounds,
            ) {
                continue;
            }
            if let Some(source) = self.type_source.environment.generic_sources.get(&identity) {
                if source.environment.is_poisoned()
                    || (source.closed().is_some() && !source.validate_closed())
                    || (source.closed().is_none()
                        && (source.input.is_none()
                            || source.syntax.hir_id.is_none()
                            || source.schema.original() != source.syntax.hir_id))
                {
                    return Err(SourceTypesError::Unresolved);
                }
                selected.insert(identity, source.schema.clone());
            } else {
                deferred.push((name, identity));
            }
        }
        let invocation = self
            .copy_invocation_stack
            .last()
            .and_then(|id| self.copy_invocations.get(id.0 as usize))
            .filter(|call| call.target == definition && call.source_event == event);
        let Some(invocation) = invocation else {
            return self.complete_input_static_schemas(selected, deferred, span, work);
        };
        let context = self.invocation_context(Some(CallableOwner::Function(definition)));
        if context.invocation != Some(invocation.id) {
            return Err(SourceTypesError::Unresolved);
        }
        work.charge(self.scoped_source_identities.len() + self.generic_bound_checks.len())?;
        for source in &self.scoped_source_identities {
            if source.context != context {
                continue;
            }
            let bound = self
                .record_bounds
                .get(source.required.0 as usize)
                .ok_or(SourceTypesError::MissingNode)?;
            if bound.id != source.required
                || bound.definition != definition
                || bound.binder != source.binder
                || source.occurrences.is_empty()
            {
                return Err(SourceTypesError::Unresolved);
            }
            // A captured graph already is the whole actual selection. Legacy
            // constraint rows cannot replace it with an exported approximation.
            if selected.contains_key(&source.binder) {
                continue;
            }
            selected.insert(
                source.binder.clone(),
                SourceSchema::import(&source.key, None, work)?,
            );
        }
        for check in &self.generic_bound_checks {
            if check.context != context {
                continue;
            }
            for (binder, key) in &check.substitutions {
                if !selected.contains_key(binder) {
                    selected.insert(binder.clone(), SourceSchema::import(key, None, work)?);
                }
            }
        }
        self.complete_input_static_schemas(selected, deferred, span, work)
    }

    fn complete_input_static_schemas(
        &mut self,
        mut selected: BTreeMap<String, SourceSchema>,
        deferred: Vec<(String, String)>,
        span: Span,
        work: &mut WorkLimit,
    ) -> Result<BTreeMap<String, SourceSchema>, SourceTypesError> {
        for (name, identity) in deferred {
            work.charge(1)?;
            if selected.contains_key(&identity) {
                continue;
            }
            let syntax = TypeExpr {
                hir_id: None,
                text: String::new(),
                span,
                kind: TypeKind::Name {
                    path: vec![name],
                    arguments: vec![],
                },
            };
            let syntax = self
                .effect_argument_syntax(&syntax)
                .map_err(|_| SourceTypesError::Unresolved)?;
            let key = crate::static_eval::effects::bounded_argument_key(
                &syntax,
                &self.effect_type_binders,
            )
            .ok_or(SourceTypesError::BudgetExceeded)?;
            selected.insert(identity, SourceSchema::import(&key, syntax.hir_id, work)?);
        }
        Ok(selected)
    }
}
