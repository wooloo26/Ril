//! Immutable source type graphs. Semantic `Ty` is intentionally not an input.
//!
//! These graphs retain type coordinates only. Importing, projecting, replacing
//! a binder or proving absence of Array/Fn coordinates grants no storage,
//! effect, borrowing, resource, constructor or publication authority.
pub(crate) mod builtins;
pub(crate) mod declarations;
mod graph;
mod index;
mod legacy;
pub(crate) mod polymorphic;
mod queries;
pub(crate) mod reception;
mod schema;
pub(crate) mod standard_data;
mod substitution;

pub(crate) use graph::{
    SourceBuilder, SourceContainer, SourceField, SourceLength, SourceNode, SourceScalar,
    SourceTypes, WorkLimit,
};
pub use graph::{SourceTypeId, SourceTypesError};
pub(crate) use index::LiveSourceTypes;
pub use index::{SourceTypeIndex, SourceView};
pub(crate) use legacy::key_is_coordinate_free;
pub(crate) use queries::SourceTypeQueries;
pub use queries::{SourcePath, SourceSensitivity};
pub(crate) use schema::SourceSchema;
pub(crate) use substitution::LegacySourceExport;
pub(crate) use substitution::scalar_name;
pub(crate) use substitution::substitute_key;

pub(crate) fn key_is_coordinate_free_with_declarations(
    key: &crate::sema::effect_identity::ArgumentKey,
    hir: Option<&crate::hir::nodes::HirProgram>,
) -> bool {
    key_is_coordinate_free(key)
        || hir.is_some_and(|hir| {
            matches!(
                declarations::sensitivity(key, hir, &mut WorkLimit::new(4096)),
                SourceSensitivity::Absent { .. }
            )
        })
}
