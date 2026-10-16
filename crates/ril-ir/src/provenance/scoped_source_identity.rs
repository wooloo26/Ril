//! Complete lexical type identity carried without granting access authority.
use super::{
    BoundScope, BoundTypeSelectionStep, ContractSyntax, CopyInstanceId, GenericBoundId,
    RecordBoundKey, ResumptionContext,
};
pub use ril_compiler_core::ids::ScopedSourceIdentityId;
use ril_compiler_core::{diagnostic::CauseId, ids::DefinitionId, source::Span};

/// Selects original formal storage from its frozen invocation entry. The
/// expression index identifies the real formal Name read, not a source span.
#[derive(Debug, Clone)]
pub struct FormalSourceAnchor {
    pub definition: DefinitionId,
    pub invocation: CopyInstanceId,
    pub parameter_index: u32,
    pub type_path: Vec<BoundTypeSelectionStep>,
    pub activation: u32,
    pub binding: u32,
    pub root_expression: usize,
    pub entry_allocation_epoch: u64,
}

#[derive(Debug, Clone)]
pub struct ScopedSourceOccurrence {
    pub argument_index: u32,
    pub selection_path: Vec<BoundTypeSelectionStep>,
    pub formal: FormalSourceAnchor,
}

#[derive(Debug, Clone)]
pub struct ScopedSourceIdentity {
    pub id: ScopedSourceIdentityId,
    pub required: GenericBoundId,
    pub binder: String,
    pub context: ResumptionContext,
    pub syntax: ContractSyntax,
    pub scope: BoundScope,
    pub key: RecordBoundKey,
    pub occurrences: Vec<ScopedSourceOccurrence>,
    pub cause: CauseId,
    pub span: Span,
}
