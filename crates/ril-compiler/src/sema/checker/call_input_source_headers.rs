//! Declaration normalization and actual instance selection are separate steps.
//! This keeps open rows and qualified callable fields out of erased Ty reifiers.
use super::*;
use crate::sema::model::rows::RowIdentity;

impl Checker {
    pub(in crate::sema::checker) fn actual_input_source_schemas(
        &mut self,
        info: &FunctionInfo,
        event: Option<CopyCallEventId>,
        span: Span,
        work: &mut WorkLimit,
    ) -> Result<BTreeMap<String, SourceSchema>, SourceTypesError> {
        let mut selected = BTreeMap::new();
        let mut deferred = Vec::new();
        let mut owned = Vec::new();
        work.charge(info.syntax.generics.len() + info.typing_environment.generic_context.len())?;
        for parameter in &info.syntax.generics {
            let identity = self
                .type_source
                .environment
                .generic_context
                .get(&parameter.name)
                .ok_or(SourceTypesError::Unresolved)?;
            owned.push((parameter.name.clone(), identity.clone()));
        }
        for (name, identity) in &info.typing_environment.generic_context {
            if !owned.iter().any(|(_, actual)| actual == identity) {
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
            .filter(|call| call.target == info.definition && call.source_event == event);
        let Some(invocation) = invocation else {
            return self.complete_input_static_schemas(selected, deferred, span, work);
        };
        let context = self.invocation_context(Some(CallableOwner::Function(info.definition)));
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
                || bound.definition != info.definition
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

    pub(super) fn original_source_header_key(
        &self,
        syntax: &TypeExpr,
        scope: &crate::sema::record_bounds::BoundScope,
    ) -> Option<ArgumentKey> {
        let mut names = scope.types.clone();
        for (name, id) in &scope.rows {
            let row = self.bound_rows.get(id.0 as usize)?;
            let RowIdentity::Binder(identity) = &row.identity else {
                return None;
            };
            if names.get(name).is_some_and(|existing| existing != identity) {
                return None;
            }
            names.insert(name.clone(), identity.clone());
        }
        let mut work = 4096;
        let syntax = super::super::source_receiving::qualified_source_aliases_in(
            self,
            syntax,
            scope,
            &mut BTreeSet::new(),
            &mut work,
            0,
        )?;
        let syntax =
            super::super::source_types::expand_builtin_source_syntax(&self.types, &syntax, 0)?;
        super::super::source_receiving::resolved_symbolic_names(
            &syntax,
            &names,
            &self.types,
            &mut work,
            0,
        )?;
        let key = self.record_bound_key(&syntax, scope)?;
        source_reception::complete(&key, &mut work)?;
        Some(key)
    }
}
