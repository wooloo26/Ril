//! Immutable source type graphs. Semantic `Ty` is intentionally not an input.
//!
//! These graphs retain type coordinates only. Importing, projecting, replacing
//! a binder or proving absence of Array/Fn coordinates grants no storage,
//! effect, borrowing, resource, constructor or publication authority.
mod graph;
mod index;
mod legacy;
mod queries;
mod substitution;

pub(crate) use graph::{
    SourceBuilder, SourceContainer, SourceField, SourceLength, SourceNode, SourceScalar,
    SourceTypes, WorkLimit,
};
pub use graph::{SourceTypeId, SourceTypesError};
pub(crate) use index::LiveSourceTypes;
pub use index::SourceTypeIndex;
pub(crate) use legacy::{key_is_coordinate_free, project_key};
pub(crate) use queries::SourceTypeQueries;
pub use queries::{SourcePath, SourceSensitivity};
pub(crate) use substitution::LegacySourceExport;
pub(crate) use substitution::substitute_key;
