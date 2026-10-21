//! Complete source identity under genuine lexical binders.
//! This is not a closed SourceTypeWitness and grants no access permission.
use super::{
    context::FrozenEnvironment,
    copy_templates::InstanceId,
    effect_identity::{ArgumentKey, InvocationContext},
    facts::ScopeId,
    model::BindingId,
    record_bounds::{BoundTypeSelectionStep, GenericBoundId},
};
use ril_compiler_core::{diagnostic::CauseId, ids::DefinitionId, source::Span};
use ril_syntax::ast::TypeExpr;

pub use ril_compiler_core::ids::ScopedSourceIdentityId;

/// The original formal's whole entry is the immutable snapshot at
/// `copy_invocations[invocation].arguments[parameter_index]`.
/// `type_path` selects both its original header subterm and existing stored
/// child. It never creates a value for an empty or type-only position.
#[derive(Debug, Clone)]
pub struct FormalSourceAnchor {
    pub definition: DefinitionId,
    pub invocation: InstanceId,
    pub parameter_index: u32,
    pub type_path: Vec<BoundTypeSelectionStep>,
    pub activation: ScopeId,
    pub binding: BindingId,
    /// Physical expression index for an actual Name
    /// read of this original formal. Replay locates that token in the original
    /// function AST and reconstructs its received root independently.
    pub root_expression: usize,
    pub entry_allocation_epoch: usize,
}

/// Select T from the actual callee's whole argument entry, then tie that same
/// object to an original formal/header. Every real T occurrence is covered.
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
    pub context: InvocationContext,
    /// A genuine source header subterm and its actual readonly reception's
    /// complete captured interpretation, shared with the original binding.
    pub syntax: TypeExpr,
    pub typing_environment: FrozenEnvironment,
    /// Complete dimensions, callable modes/qualifications and rigid row IDs.
    /// A symbolic key is not a closed witness or a freshness certificate.
    pub key: ArgumentKey,
    pub occurrences: Vec<ScopedSourceOccurrence>,
    pub cause: CauseId,
    pub span: Span,
}
