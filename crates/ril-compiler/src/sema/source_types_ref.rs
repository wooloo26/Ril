//! Borrow the one live or frozen Source arena. A view and its environment are
//! resolved together under the caller's remaining allowance.
#[cfg(test)]
use super::source_types::SourceTypeIndex;
use super::{
    context::{FrozenEnvId, FrozenEnvironment},
    source_types::{LiveSourceTypes, SourceSchema, SourceTypesError, SourceView, WorkLimit},
};
use ril_compiler_core::ids::TypeExprId;

#[derive(Clone, Copy)]
pub(crate) enum SourceTypesRef<'a> {
    Live(&'a LiveSourceTypes),
    #[cfg(test)]
    Frozen(&'a SourceTypeIndex),
}

impl SourceTypesRef<'_> {
    pub(crate) fn view_schema(
        self,
        view: SourceView,
        original: Option<TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<(SourceSchema, FrozenEnvironment), SourceTypesError> {
        match self {
            Self::Live(types) => types.view_schema(view, original, work),
            #[cfg(test)]
            Self::Frozen(types) => types.view_schema(view, original, work),
        }
    }

    pub(crate) fn environment(
        self,
        id: FrozenEnvId,
        work: &mut WorkLimit,
    ) -> Result<FrozenEnvironment, SourceTypesError> {
        match self {
            Self::Live(types) => types.environment(id, work),
            #[cfg(test)]
            Self::Frozen(types) => types.environment(id, work),
        }
    }
}
