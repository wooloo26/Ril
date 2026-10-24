//! Signature probes consume the elaborated callable type directly. A probe is
//! created by the semantic analyzer; reading a formal does not replay the
//! construction of its environment, heap or invocation history.
use crate::sema::{
    context::FrozenEnvironment,
    source_types::{SourceSchema, SourceTypesError as Error, WorkLimit},
};
use ril_syntax::ast::ParameterMode;
use std::sync::Arc;

#[derive(Debug, Clone)]
pub struct SignatureProbeSource {
    pub(crate) schema: Arc<SourceSchema>,
    pub environment: FrozenEnvironment,
}

impl PartialEq for SignatureProbeSource {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.schema, &other.schema) && self.environment.id() == other.environment.id()
    }
}
impl Eq for SignatureProbeSource {}

impl SignatureProbeSource {
    pub(crate) fn parameter_schema(
        &self,
        slot: usize,
        mode: ParameterMode,
        work: &mut WorkLimit,
    ) -> Result<SourceSchema, Error> {
        if self.environment.is_poisoned() {
            return Err(Error::Unresolved);
        }
        let parameters = self.schema.callable_parameters(work)?;
        let (actual_mode, schema) = parameters.get(slot).ok_or(Error::MissingNode)?;
        if *actual_mode != mode {
            return Err(Error::Unresolved);
        }
        Ok(schema.clone())
    }
}
