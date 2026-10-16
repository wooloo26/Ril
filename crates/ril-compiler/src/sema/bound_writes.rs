//! Historical observations used to replay writes through structural bounds.
//! An observation pins a semantic execution; it does not grant permission.
use super::{
    copy_contract::CopyValueSnapshot, effect_identity::InvocationContext, facts::ScopeId,
    model::AccessFact,
};
use ril_compiler_core::{diagnostic::CauseId, source::Span};

pub use ril_compiler_core::ids::ObservedAccessId;

#[derive(Debug, Clone)]
pub struct ObservedAccess {
    pub id: ObservedAccessId,
    pub context: InvocationContext,
    pub activation: ScopeId,
    /// Frozen at observation, including the original allocation epoch. Frame
    /// footprint normalization must not rewrite this historical observation.
    pub access: AccessFact,
}

#[derive(Debug, Clone)]
pub struct BoundFieldWrite {
    /// The real ValueOnly projection supplies the pre-write receiver and old
    /// member. One observation may discharge several applicable bound views.
    pub projection_index: usize,
    /// Indices in SemanticFacts.invocation_expressions. Source statement
    /// coverage must establish the exact RHS and receiver occurrences; source
    /// spans alone never supply an execution identity.
    pub rhs_expression: usize,
    pub receiver_expression: usize,
    pub access: ObservedAccessId,
    pub operator: String,
    /// After contextual/compound receiving, before the actual store.
    pub replacement: CopyValueSnapshot,
    /// Existing stored graph after the store. No missing member may be filled
    /// by allocating a hypothetical T object during independent replay.
    pub updated_receiver: CopyValueSnapshot,
    pub cause: CauseId,
    pub span: Span,
}
