//! Evidence for actual continuation-answer handoffs. A frozen graph records an
//! observation; it does not imply copying, freshness, or additional permission.
use super::{
    copy_contract::CopyValueSnapshot,
    effect_identity::InvocationContext,
    facts::{LoanId, ScopeId},
};
use ril_compiler_core::{diagnostic::CauseId, source::Span};
use ril_syntax::ast::ParameterMode;

#[derive(Debug, Clone)]
pub struct OperationLoanStart {
    pub loan: LoanId,
    pub activation: ScopeId,
    pub boundary: u32,
    pub handler: usize,
    pub operation: u64,
    pub parameter: u32,
    pub temporary: bool,
    pub context: InvocationContext,
    pub source: CopyValueSnapshot,
    pub allocation_epoch: usize,
    pub span: Span,
    pub cause: CauseId,
}

#[derive(Debug, Clone)]
pub struct OperationReception {
    pub parameter: u32,
    pub mode: ParameterMode,
    pub loan: Option<LoanId>,
}

#[derive(Debug, Clone)]
pub struct ScopeBindingObservation {
    pub binding: usize,
    pub value: super::model::Value,
    pub cell: Option<super::facts::NodeId>,
    pub forwarded: std::collections::BTreeSet<usize>,
    pub alive: bool,
}

#[derive(Debug, Clone)]
pub struct ContinuationScopeExit {
    pub activation: ScopeId,
    pub boundary: u32,
    pub epoch: usize,
    pub binding_frontier: usize,
    pub retired_bindings: std::collections::BTreeSet<usize>,
    pub protected_bindings: std::collections::BTreeSet<usize>,
    pub alive_bindings: std::collections::BTreeSet<usize>,
    pub bindings: Vec<ScopeBindingObservation>,
    /// Linear protection-root observations; no unrelated pairwise relations.
    pub nodes: Vec<super::copy_contract::CopyNode>,
    pub answer_before: CopyValueSnapshot,
    pub answer_received: CopyValueSnapshot,
}
