//! Original argument observations and default results retained for explanation.
//! These records present verified facts and do not authorize receiving or entry.
use super::{
    ContractSyntax, CopyCallEventId, CopyInstanceId, CopyInvocationStatus, CopyValueSnapshot,
    RecordBoundKey, ResumptionContext,
};
use crate::specialization::DefaultUseId;
use ril_compiler_core::{
    ids::{CallableOwner, DefinitionId},
    source::Span,
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SuppliedArgument {
    /// Original expression index in Graph.values.
    pub expression: usize,
    pub allocation_epoch: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EvaluationRole {
    Callee,
    Piped,
    Written(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ApplicationEvaluation {
    pub role: EvaluationRole,
    pub observation: SuppliedArgument,
}

#[derive(Debug, Clone)]
pub struct InvocationExpression {
    pub context: ResumptionContext,
    pub expression: usize,
    pub argument_of: Option<(CopyCallEventId, u32)>,
}

/// Complete original primitive headers and rows retained for hover and proof
/// explanation. Presentation records never authorize a semantic operation.
#[derive(Debug, Clone)]
pub enum BuiltinDeclaration {
    Syntax(ContractSyntax),
    Generic(ril_compiler_core::builtin_calls::GenericBuiltin),
    Nullary(ril_compiler_core::builtin_calls::NullaryConstructor),
    Numeric(ril_compiler_core::numeric_builtins::NumericBuiltin),
}

#[derive(Debug, Clone)]
pub struct BuiltinSourceObservation {
    pub expression: usize,
    pub context: ResumptionContext,
    pub identity: String,
    pub full_header: BuiltinDeclaration,
    pub environment: super::FrozenEnvironmentId,
    pub concrete_effects: BTreeSet<String>,
    pub written_formals: BTreeSet<u32>,
    pub captures: BTreeSet<u32>,
    pub cause: ril_compiler_core::diagnostic::CauseId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArgumentSource {
    Supplied,
    Default(DefaultUseId),
    Missing,
}

#[derive(Debug, Clone)]
pub struct CallArguments {
    pub source_event: CopyCallEventId,
    pub target: Option<DefinitionId>,
    pub evaluated: Vec<ApplicationEvaluation>,
    pub slots_bound: bool,
    pub slots: Vec<ArgumentSource>,
    pub supplied: BTreeMap<u32, SuppliedArgument>,
    pub evaluation_complete: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefaultOrigin {
    Call(CopyCallEventId),
    DeclarationProbe,
    InvocationFallback(CopyInstanceId),
}

#[derive(Debug, Clone)]
pub struct DefaultStaticArgument {
    pub definition: DefinitionId,
    pub index: u32,
    pub binder: String,
    pub key: Option<RecordBoundKey>,
    pub syntax: Option<ContractSyntax>,
}

#[derive(Debug, Clone)]
pub struct DefaultUse {
    pub id: DefaultUseId,
    pub origin: DefaultOrigin,
    pub target: Option<DefinitionId>,
    pub parameter: u32,
    pub caller: ResumptionContext,
    pub owner: Option<CallableOwner>,
    pub span: Span,
    pub arguments: Vec<DefaultStaticArgument>,
    pub captured_arguments: Vec<DefaultStaticArgument>,
    pub unresolved_captured_binders: BTreeSet<String>,
    pub evaluation_complete: bool,
    pub status: CopyInvocationStatus,
    pub entered: Vec<CopyInstanceId>,
    pub result: Option<CopyValueSnapshot>,
    pub result_expression: Option<usize>,
    pub result_allocation_epoch: Option<u64>,
}
