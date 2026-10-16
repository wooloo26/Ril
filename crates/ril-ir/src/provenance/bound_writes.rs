//! Historical access and assignment evidence, separate from type identity.
use super::{ConditionalAccess, CopyValueSnapshot, ResumptionContext};
pub use ril_compiler_core::ids::ObservedAccessId;
use ril_compiler_core::{diagnostic::CauseId, source::Span};

#[derive(Debug, Clone)]
pub struct ObservedAccess {
    pub id: ObservedAccessId,
    pub context: ResumptionContext,
    pub activation: u32,
    pub access: ConditionalAccess,
}

#[derive(Debug, Clone)]
pub struct BoundFieldWrite {
    pub projection_index: usize,
    pub rhs_expression: usize,
    pub receiver_expression: usize,
    pub access: ObservedAccessId,
    pub operator: String,
    pub replacement: CopyValueSnapshot,
    pub updated_receiver: CopyValueSnapshot,
    pub cause: CauseId,
    pub span: Span,
}
