//! Borrow the one live or frozen Source arena. A view and its environment are
//! resolved together under the caller's remaining allowance.
use super::{
    context::{FrozenEnvId, FrozenEnvironment},
    source_types::{
        LiveSourceTypes, SourceSchema, SourceTypeIndex, SourceTypesError, SourceView, WorkLimit,
    },
};
use ril_compiler_core::ids::TypeExprId;

#[derive(Clone, Copy)]
pub(crate) enum SourceTypesRef<'a> {
    Live(&'a LiveSourceTypes),
    Frozen(&'a SourceTypeIndex),
}

impl SourceTypesRef<'_> {
    pub(crate) fn binding_schema(
        self,
        binding: usize,
        work: &mut WorkLimit,
    ) -> Result<Option<(SourceSchema, FrozenEnvironment)>, SourceTypesError> {
        match self {
            Self::Live(types) => types.binding_schema_if_known(binding, None, work),
            Self::Frozen(types) => types.binding_schema_if_known(binding, None, work),
        }
    }

    pub(crate) fn view_schema(
        self,
        view: SourceView,
        original: Option<TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<(SourceSchema, FrozenEnvironment), SourceTypesError> {
        match self {
            Self::Live(types) => types.view_schema(view, original, work),
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
            Self::Frozen(types) => types.environment(id, work),
        }
    }
}
