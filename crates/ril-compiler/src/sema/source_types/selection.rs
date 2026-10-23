//! A generic selection retains a complete graph and its original interpretation.
//! Closed AST witnesses are compatibility projections for unmigrated consumers.
use super::{SourceSchema, SourceTypesError, WorkLimit};
use crate::sema::{
    context::FrozenEnvironment, effect_identity::ArgumentKey, model::SourceTypeWitness,
};
use ril_syntax::ast::TypeExpr;
use std::{collections::BTreeMap, sync::Arc};

#[derive(Debug, Clone)]
pub struct TypeSourceSelection {
    pub(crate) schema: SourceSchema,
    pub(crate) syntax: Arc<TypeExpr>,
    pub(crate) environment: FrozenEnvironment,
    closed: Option<Arc<SourceTypeWitness>>,
    pub(crate) input: Option<SourceSelectionInput>,
}

#[derive(Debug, Clone, Copy)]
pub struct SourceSelectionInput {
    pub invocation: crate::sema::copy_templates::InstanceId,
    pub event: crate::sema::copy_contract::CopyCallEventId,
    pub slot: u32,
    pub observation: usize,
    pub binding: usize,
}

impl TypeSourceSelection {
    pub(crate) fn from_closed(
        witness: Arc<SourceTypeWitness>,
        environment: FrozenEnvironment,
    ) -> Result<Arc<Self>, SourceTypesError> {
        if environment.is_poisoned() || !witness.validate_closed() {
            return Err(SourceTypesError::Unresolved);
        }
        let key =
            crate::static_eval::effects::bounded_argument_key(&witness.syntax, &BTreeMap::new())
                .ok_or(SourceTypesError::BudgetExceeded)?;
        let schema = SourceSchema::import(&key, witness.syntax.hir_id, &mut WorkLimit::new(16384))?;
        Ok(Arc::new(Self {
            schema,
            syntax: Arc::new(witness.syntax.clone()),
            environment,
            closed: Some(witness),
            input: None,
        }))
    }

    pub(crate) fn from_parameter(
        schema: SourceSchema,
        syntax: TypeExpr,
        environment: FrozenEnvironment,
        input: SourceSelectionInput,
    ) -> Result<Arc<Self>, SourceTypesError> {
        if environment.is_poisoned()
            || syntax.hir_id.is_none()
            || schema.original() != syntax.hir_id
        {
            return Err(SourceTypesError::Unresolved);
        }
        crate::static_eval::effects::bounded_argument_key(&syntax, &BTreeMap::new())
            .ok_or(SourceTypesError::BudgetExceeded)?;
        Ok(Arc::new(Self {
            schema,
            syntax: Arc::new(syntax),
            environment,
            input: Some(input),
            closed: None,
        }))
    }

    pub(crate) fn key(&self) -> Result<ArgumentKey, SourceTypesError> {
        self.schema.key()
    }

    pub(crate) fn quantified_syntax_projection(
        &self,
        span: ril_compiler_core::source::Span,
        work: &mut WorkLimit,
        binder: &mut impl FnMut(&str, bool, &mut WorkLimit) -> Result<TypeExpr, SourceTypesError>,
    ) -> Result<TypeExpr, SourceTypesError> {
        work.charge(1)?;
        if self.closed.is_some()
            || self.environment.is_poisoned()
            || self.input.is_none()
            || self.syntax.hir_id.is_none()
            || self.schema.original() != self.syntax.hir_id
        {
            return Err(SourceTypesError::Unresolved);
        }
        self.schema.syntax_projection(span, work, binder)
    }

    pub(crate) fn closed(&self) -> Option<&Arc<SourceTypeWitness>> {
        self.closed.as_ref()
    }

    pub(crate) fn validate_closed(&self) -> bool {
        let Some(witness) = &self.closed else {
            return false;
        };
        if self.environment.is_poisoned()
            || !witness.validate_closed()
            || self.syntax.as_ref() != &witness.syntax
        {
            return false;
        }
        let consistent = || {
            let key = crate::static_eval::effects::bounded_argument_key(
                &witness.syntax,
                &BTreeMap::new(),
            )
            .ok_or(SourceTypesError::Unresolved)?;
            let original =
                SourceSchema::import(&key, witness.syntax.hir_id, &mut WorkLimit::new(16384))?;
            Ok::<_, SourceTypesError>(original.key()? == self.key()?)
        };
        consistent() == Ok(true)
    }
}

impl PartialEq for TypeSourceSelection {
    fn eq(&self, other: &Self) -> bool {
        match (&self.closed, &other.closed) {
            (Some(left), Some(right)) => left == right,
            _ => {
                self.environment.id() == other.environment.id()
                    && self
                        .key()
                        .ok()
                        .zip(other.key().ok())
                        .is_some_and(|(a, b)| a == b)
            }
        }
    }
}
impl Eq for TypeSourceSelection {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn graph_bound_replay_requires_the_complete_original_input_even_without_legacy_certificates() {
        use crate::sema::{
            model::Ty,
            validate::{ValidationIssueKind, solved_facts},
        };
        let source = ril_test::case_source(
            "tests/regressions/source-transport.ril::composed-row-with-array-and-callback",
        );
        let program = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let facts = program.facts();
        let definition = facts
            .functions
            .iter()
            .find(|function| function.syntax.name == "pass")
            .unwrap()
            .definition;
        let bound = facts
            .record_bounds
            .iter()
            .find(|bound| bound.definition == definition)
            .unwrap();
        let (holder, invocation) = facts
            .bindings
            .iter()
            .enumerate()
            .find_map(|(index, binding)| {
                let selected = binding
                    .typing_environment
                    .generic_sources
                    .get(&bound.binder)?;
                let input = selected.input?;
                let call = facts.copy_invocations.get(input.invocation.0 as usize)?;
                (binding.parameter
                    && binding.context.invocation == Some(call.id)
                    && call.target == definition
                    && matches!(
                        call.entry.arguments.first()?.value().ty,
                        Ty::OpenRecord { .. }
                    ))
                .then_some((index, call.id))
            })
            .expect("a bound input must use its canonical graph");
        assert!(
            !facts
                .scoped_source_identities
                .iter()
                .any(|identity| identity.required == bound.id
                    && identity.context.invocation == Some(invocation))
        );
        let mut reordered = facts.clone();
        reordered.invocation_expressions.reverse();
        solved_facts(&reordered).unwrap();
        for mutation in 0..5 {
            let mut changed = facts.clone();
            let mut environment = changed.bindings[holder].typing_environment.thaw();
            let selection =
                Arc::make_mut(environment.generic_sources.get_mut(&bound.binder).unwrap());
            match mutation {
                0 => selection.input = None,
                1 => selection.input.as_mut().unwrap().event.0 = u32::MAX,
                2 => selection.input.as_mut().unwrap().observation += 1,
                3 => selection.environment = selection.environment.thaw().freeze(),
                _ => {
                    let mut key = selection.key().unwrap();
                    let ArgumentKey::Record { fields, .. } = &mut key else {
                        panic!("record")
                    };
                    let ArgumentKey::Array { length, .. } = &mut fields
                        .iter_mut()
                        .find(|(name, _, _)| name == "items")
                        .unwrap()
                        .2
                    else {
                        panic!("array")
                    };
                    *length = Some("const(int:3)".into());
                    selection.schema = SourceSchema::import(
                        &key,
                        selection.schema.original(),
                        &mut WorkLimit::new(16384),
                    )
                    .unwrap();
                }
            }
            changed.bindings[holder].typing_environment = environment.freeze();
            let errors = solved_facts(&changed).unwrap_err();
            assert!(
                errors
                    .iter()
                    .any(|issue| matches!(&issue.kind, ValidationIssueKind::RecordBound(_))),
                "mutation {mutation}: {errors:?}"
            );
        }
    }

    #[test]
    fn captured_generic_graphs_require_their_actual_operand_and_original_environment() {
        let source = ril_test::case_source(
            "tests/regressions/source-transport.ril::open-record-through-generic-identity",
        );
        let program = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let facts = program.facts();
        let (binding, identity) = facts
            .bindings
            .iter()
            .enumerate()
            .find_map(|(index, binding)| {
                binding
                    .typing_environment
                    .generic_sources
                    .iter()
                    .find(|(_, source)| source.input.is_some())
                    .map(|(identity, _)| (index, identity.clone()))
            })
            .expect("the program must retain a complete open generic Source");
        for mutation in 0..5 {
            let mut changed = facts.clone();
            let mut environment = changed.bindings[binding].typing_environment.thaw();
            let selected = Arc::make_mut(environment.generic_sources.get_mut(&identity).unwrap());
            match mutation {
                0 => selected.input = None,
                1 => selected.input.as_mut().unwrap().event.0 = u32::MAX,
                2 => selected.input.as_mut().unwrap().observation += 1,
                3 => selected.environment = selected.environment.thaw().freeze(),
                _ => {
                    let mut key = selected.key().unwrap();
                    let ArgumentKey::Record { fields, .. } = &mut key else {
                        panic!("record view")
                    };
                    let ArgumentKey::Array { length, .. } = &mut fields
                        .iter_mut()
                        .find(|(name, _, _)| name == "items")
                        .unwrap()
                        .2
                    else {
                        panic!("fixed array field")
                    };
                    *length = Some("const(int:3)".into());
                    selected.schema = SourceSchema::import(
                        &key,
                        selected.schema.original(),
                        &mut WorkLimit::new(16384),
                    )
                    .unwrap();
                }
            }
            changed.bindings[binding].typing_environment = environment.freeze();
            assert!(
                crate::sema::source_type_validation::validate(&changed).is_err(),
                "mutation {mutation} issued an unchecked generic view"
            );
        }
    }
}
