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
mod tests {}
