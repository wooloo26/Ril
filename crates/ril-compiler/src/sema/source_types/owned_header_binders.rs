//! Bound function parameters are declared by their original HIR coordinates.
//! A declaration's capture need not contain the spelling of its own binder.
use super::{SourceTypesError, WorkLimit};
use crate::{
    hir::nodes::{HirProgram, LexicalOwner, StmtKind},
    sema::{GenericBinder, model::FunctionInfo},
};
use ril_compiler_core::ids::{DefinitionId, GenericParamId, StmtId};
use std::collections::BTreeMap;

pub(crate) fn function(
    definition: DefinitionId,
    declaration: StmtId,
    functions: &[FunctionInfo],
    registry: &BTreeMap<String, GenericBinder>,
    hir: &HirProgram,
    work: &mut WorkLimit,
) -> Result<BTreeMap<GenericParamId, String>, SourceTypesError> {
    work.charge(1 + functions.len() + registry.len())?;
    let original = hir
        .statement(declaration)
        .ok_or(SourceTypesError::MissingNode)?;
    let StmtKind::Function(original) = &original.kind else {
        return Err(SourceTypesError::Unresolved);
    };
    let mut matched = false;
    for function in functions
        .iter()
        .filter(|function| function.definition == definition)
    {
        if function.hir_id != Some(declaration)
            || function.syntax.generics.len() != original.generics.len()
        {
            return Err(SourceTypesError::Unresolved);
        }
        work.charge(original.generics.len())?;
        for (parameter, id) in function.syntax.generics.iter().zip(&original.generics) {
            let canonical = hir.generic(*id).ok_or(SourceTypesError::MissingNode)?;
            work.text(&canonical.name)?;
            work.text(&parameter.name)?;
            if parameter.hir_id != Some(*id)
                || parameter.name != canonical.name
                || canonical.info.owner != LexicalOwner::Declaration(declaration)
            {
                return Err(SourceTypesError::Unresolved);
            }
        }
        matched = true;
    }
    if !matched {
        return Err(SourceTypesError::MissingNode);
    }
    let mut owned = BTreeMap::new();
    for (identity, binder) in registry
        .iter()
        .filter(|(_, binder)| binder.definition == definition)
    {
        work.text(identity)?;
        work.text(&binder.identity)?;
        work.text(&binder.name)?;
        let id = original
            .generics
            .get(binder.index as usize)
            .ok_or(SourceTypesError::Unresolved)?;
        let canonical = hir.generic(*id).ok_or(SourceTypesError::MissingNode)?;
        work.text(&canonical.name)?;
        work.charge(2 + owned.len().checked_ilog2().unwrap_or(0) as usize)?;
        if identity != &binder.identity
            || binder.name != canonical.name
            || owned.insert(*id, identity.clone()).is_some()
        {
            return Err(SourceTypesError::Unresolved);
        }
    }
    if owned.len() != original.generics.len() {
        return Err(SourceTypesError::MissingNode);
    }
    Ok(owned)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn owned_header_parameters_require_their_real_declaration_and_registry_identity() {
        let source = ril_test::case_source(
            "tests/regressions/source-transport.ril::partial-static-argument-inference",
        );
        let program = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let facts = program.facts();
        let hir = facts.semantic_hir.as_deref().unwrap();
        let original = facts
            .functions
            .iter()
            .find(|function| function.syntax.generics.len() == 2)
            .unwrap();
        let declaration = original.hir_id.unwrap();
        let mut budget = WorkLimit::new(16384);
        let owned = function(
            original.definition,
            declaration,
            &facts.functions,
            &facts.generic_binders,
            hir,
            &mut budget,
        )
        .unwrap();
        assert_eq!(owned.len(), 2);
        for parameter in &original.syntax.generics {
            let identity = &owned[&parameter.hir_id.unwrap()];
            assert_eq!(
                facts.generic_binders[identity].definition,
                original.definition
            );
            assert!(
                !original
                    .typing_environment
                    .generic_context
                    .values()
                    .any(|actual| actual == identity),
                "a bound parameter is not a free creation capture"
            );
        }
        let used = 16384 - budget.remaining();
        assert_eq!(
            function(
                original.definition,
                declaration,
                &facts.functions,
                &facts.generic_binders,
                hir,
                &mut WorkLimit::new(used)
            )
            .unwrap(),
            owned
        );
        assert!(
            function(
                original.definition,
                declaration,
                &facts.functions,
                &facts.generic_binders,
                hir,
                &mut WorkLimit::new(used - 1)
            )
            .is_err()
        );
        assert!(
            function(
                original.definition,
                declaration,
                &facts.functions,
                &facts.generic_binders,
                hir,
                &mut WorkLimit::new(0)
            )
            .is_err()
        );

        let sibling = facts
            .functions
            .iter()
            .find(|function| function.definition != original.definition)
            .unwrap();
        assert!(
            function(
                original.definition,
                sibling.hir_id.unwrap(),
                &facts.functions,
                &facts.generic_binders,
                hir,
                &mut WorkLimit::new(16384)
            )
            .is_err()
        );

        let identity = owned.values().next().unwrap();
        let mut registry = facts.generic_binders.clone();
        registry.remove(identity);
        assert!(
            function(
                original.definition,
                declaration,
                &facts.functions,
                &registry,
                hir,
                &mut WorkLimit::new(16384)
            )
            .is_err()
        );
        let mut registry = facts.generic_binders.clone();
        registry.get_mut(identity).unwrap().definition = sibling.definition;
        assert!(
            function(
                original.definition,
                declaration,
                &facts.functions,
                &registry,
                hir,
                &mut WorkLimit::new(16384)
            )
            .is_err()
        );

        let mut functions = facts.functions.clone();
        let function_info = functions
            .iter_mut()
            .find(|function| function.definition == original.definition)
            .unwrap();
        function_info.syntax.generics[0].hir_id = function_info.syntax.generics[1].hir_id;
        assert!(
            function(
                original.definition,
                declaration,
                &functions,
                &facts.generic_binders,
                hir,
                &mut WorkLimit::new(16384)
            )
            .is_err()
        );
    }
}
