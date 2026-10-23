//! Storage source obligations retained for diagnostics and tooling.
use super::{Projection, ResumptionContext, SourceTypeId, SourceView};
use ril_compiler_core::projection::TypeProjection;
use ril_compiler_core::source::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StorageObservation {
    pub expression: usize,
    pub allocation_epoch: usize,
}

#[derive(Debug, Clone)]
pub struct BindingSource {
    pub receiver: Option<super::OccurrenceIdentity>,
    pub binding: u32,
    pub context: ResumptionContext,
    pub activation: u32,
    pub declaration: ril_compiler_core::ids::PatternId,
    pub declared: bool,
    pub initializer: StorageObservation,
    pub path: Option<Vec<TypeProjection>>,
    pub root: Option<SourceTypeId>,
}

#[derive(Debug, Clone)]
pub enum StorageDestination {
    Binding(u32),
    Projection {
        receiver: StorageObservation,
        selector: Option<StorageObservation>,
        slot: Projection,
    },
}

#[derive(Debug, Clone)]
pub struct StorageWrite {
    pub target: ril_compiler_core::ids::ExprId,
    pub context: ResumptionContext,
    pub activation: u32,
    pub span: Span,
    pub operator: String,
    pub rhs: StorageObservation,
    pub destination: StorageDestination,
    pub expected: Option<SourceView>,
    pub completed: bool,
}
