//! Original storage views and actual write occurrences. These records carry
//! source-coordinate obligations; they never grant write or sharing authority.
use super::{
    effect_identity::{ArgumentKey, InvocationContext},
    facts::{ScopeId, Slot},
    model::BindingId,
};
use ril_compiler_core::projection::TypeProjection;
use ril_compiler_core::source::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StorageObservation {
    pub expression: usize,
    pub allocation_epoch: usize,
}

#[derive(Debug, Clone)]
pub struct BindingSource {
    pub binding: BindingId,
    pub context: InvocationContext,
    pub activation: ScopeId,
    pub declaration: ril_compiler_core::ids::PatternId,
    pub declared: bool,
    pub initializer: StorageObservation,
    /// Derived from the original HIR introducer. None retains a projection
    /// obligation; the immutable SourceTypeIndex owns the declaration schema.
    pub path: Option<Vec<TypeProjection>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StorageDestination {
    Binding(BindingId),
    Projection {
        receiver: StorageObservation,
        selector: Option<StorageObservation>,
        slot: Slot,
    },
}

#[derive(Debug, Clone)]
pub struct StorageWrite {
    pub target: ril_compiler_core::ids::ExprId,
    pub context: InvocationContext,
    pub activation: ScopeId,
    pub span: Span,
    pub operator: String,
    pub rhs: StorageObservation,
    pub destination: StorageDestination,
    pub expected: Option<ArgumentKey>,
    /// False requires an actual Never receiver or selector observation.
    pub completed: bool,
}
