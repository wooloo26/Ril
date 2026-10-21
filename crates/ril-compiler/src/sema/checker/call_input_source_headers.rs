//! Declaration normalization and actual instance selection are separate steps.
//! This keeps open rows and qualified callable fields out of erased Ty reifiers.
use super::*;
use crate::sema::model::rows::RowIdentity;

impl Checker {
    pub(super) fn original_input_header_key(&self, syntax: &TypeExpr) -> Option<ArgumentKey> {
        self.original_source_header_key(syntax, &self.record_bound_scope())
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

    pub(in crate::sema::checker) fn actual_input_source_selections(
        &mut self,
        info: &FunctionInfo,
        event: Option<CopyCallEventId>,
        span: Span,
    ) -> Option<BTreeMap<String, ArgumentKey>> {
        fn insert(
            selected: &mut BTreeMap<String, ArgumentKey>,
            binder: &str,
            key: &ArgumentKey,
        ) -> Option<()> {
            source_reception::complete(key, &mut 4096)?;
            if selected.get(binder).is_some_and(|old| old != key) {
                return None;
            }
            selected.insert(binder.into(), key.clone());
            Some(())
        }
        let arguments = self.static_arguments_for(info, span);
        let mut selected = BTreeMap::new();
        for argument in arguments
            .arguments
            .iter()
            .chain(&arguments.captured_arguments)
        {
            let binder = self.generic_binders.get(&argument.binder)?;
            let declaration = self
                .functions
                .iter()
                .find(|function| function.definition == binder.definition)?;
            if !crate::sema::record_bounds::certifies_type_sort(
                &argument.binder,
                binder,
                declaration.syntax.generics.get(binder.index as usize)?,
                &self.record_bounds,
            ) {
                continue;
            }
            if let Some(key) = &argument.key {
                insert(&mut selected, &argument.binder, key)?;
            }
        }
        // Preparation before body entry has no invocation Source receipts.
        // It may use its actual supplied static keys, never its caller's table.
        let invocation = self
            .copy_invocation_stack
            .last()
            .and_then(|id| self.copy_invocations.get(id.0 as usize))
            .filter(|call| call.target == info.definition && call.source_event == event);
        let Some(invocation) = invocation else {
            return Some(selected);
        };
        let context = self.invocation_context(Some(CallableOwner::Function(info.definition)));
        if context.invocation != Some(invocation.id) {
            return None;
        }
        for source in &self.scoped_source_identities {
            if source.context != context {
                continue;
            }
            let bound = self.record_bounds.get(source.required.0 as usize)?;
            if bound.id != source.required
                || bound.definition != info.definition
                || bound.binder != source.binder
                || source.occurrences.is_empty()
            {
                return None;
            }
            insert(&mut selected, &source.binder, &source.key)?;
        }
        for check in &self.generic_bound_checks {
            if check.context != context {
                continue;
            }
            for (binder, key) in &check.substitutions {
                insert(&mut selected, binder, key)?;
            }
        }
        Some(selected)
    }
}
