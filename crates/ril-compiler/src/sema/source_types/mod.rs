//! Immutable source type graphs. Semantic `Ty` is intentionally not an input.
//!
//! These graphs retain type coordinates only. Importing, projecting, replacing
//! a binder or proving absence of Array/Fn coordinates grants no storage,
//! effect, borrowing, resource, constructor or publication authority.
mod annotation_identity;
pub(crate) mod block_exits;
pub(crate) mod builtins;
pub(crate) mod constants;
pub(crate) mod declarations;
mod graph;
mod index;
pub(crate) mod legacy;
pub(crate) mod numeric;
pub(crate) mod owned_header_binders;
pub(crate) mod polymorphic;
pub(crate) mod projection_receipts;
mod queries;
pub(crate) mod reception;
mod schema;
mod selection;
pub(crate) mod standard_data;
mod standard_views;
mod substitution;
mod syntax_projection;

pub(crate) use graph::{
    CallableRowIdentity, CallableRowOrigin, KeyProjectionOrigin, SourceBuilder, SourceContainer,
    SourceField, SourceLength, SourceNode, SourceScalar, SourceTypes, WorkLimit,
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
pub(crate) use substitution::substitute_key_with;
