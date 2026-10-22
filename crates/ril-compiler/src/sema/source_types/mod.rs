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
pub(crate) mod projection_receipts;
mod queries;
pub(crate) mod reception;
mod retained;
mod schema;
mod selection;
pub(crate) mod standard_data;
mod standard_views;
mod substitution;
mod syntax_projection;

pub(crate) use graph::{
    SourceBuilder, SourceContainer, SourceField, SourceLength, SourceNode, SourceScalar,
    SourceTypes, WorkLimit,
};
pub use graph::{SourceTypeId, SourceTypesError};
pub(crate) use index::{LiveSourceTypes, steps_in};
pub use index::{SourceTypeIndex, SourceView};
pub(crate) use queries::SourceTypeQueries;
pub use queries::{SourcePath, SourceSensitivity};
pub(crate) use schema::SourceSchema;
pub use selection::{SourceSelectionInput, TypeSourceSelection};
pub(crate) use substitution::LegacySourceExport;
pub(crate) use substitution::scalar_name;
pub(crate) use substitution::{substitute_key, substitute_key_with};
