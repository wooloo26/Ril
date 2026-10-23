//! Evaluation ancestry and original callable inputs retained through Core.
use super::*;
use ril_compiler_core::ids::{ActivationEpochId, EvaluationOccurrenceId, ExprId, TypeExprId};

#[derive(Debug, Clone)]
pub struct ScopeRecord {
    pub id: u32,
    pub parent: Option<u32>,
    pub origin: ScopeOrigin,
}

#[derive(Debug, Clone)]
pub enum ScopeOrigin {
    Module,
    Unresolved,
    Named(CopyInstanceId),
    Closure(u32),
    Operation {
        handler: u32,
        operation: u64,
        body: Option<ExprId>,
        parent: Option<ActivationEpochId>,
        caller_context: ResumptionContext,
        context: ResumptionContext,
        origin: EntryOrigin,
        allocation_epoch: u64,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActivationKind {
    Expression,
    ControlTransfer,
    Emission,
}

#[derive(Debug, Clone)]
pub struct EvaluationActivation {
    pub id: ActivationEpochId,
    pub parent: Option<ActivationEpochId>,
    pub kind: ActivationKind,
    pub source: Option<ExprId>,
    pub scope: u32,
    pub context: ResumptionContext,
    pub start_expression: u64,
    pub end_expression: Option<u64>,
    pub result: Option<EvaluationOccurrenceId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InputOrigin {
    Scope(u32),
    Observed(EvaluationOccurrenceId),
    Widened(EvaluationOccurrenceId),
    Scalar(ScalarInput),
    Copied {
        observation: EvaluationOccurrenceId,
        boundary: CopyBoundaryId,
    },
}

#[derive(Debug, Clone)]
pub struct ScopeInput {
    pub application: CopyCallEventId,
    pub anchor: ActivationEpochId,
    pub node: OriginId,
    pub cause: CauseId,
    pub allocation_epoch: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarInput {
    PositiveInt,
    ByteSuffix(EvaluationOccurrenceId),
    BufferedBytes(EvaluationOccurrenceId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignatureFormal {
    pub slot: u32,
    pub binding: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignatureProbeSource {
    pub source: TypeExprId,
    pub path: Vec<ril_compiler_core::projection::TypeProjection>,
    pub environment: FrozenEnvironmentId,
    pub formals: Vec<SignatureFormal>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EntryOrigin {
    Application(CopyCallEventId),
    Generated {
        anchor: ActivationEpochId,
        callee: EvaluationOccurrenceId,
        inputs: Vec<InputOrigin>,
    },
    DeclarationProbe,
    SignatureProbe(SignatureProbeSource),
    Unresolved,
}

#[derive(Debug, Clone)]
pub struct EntryArgument {
    pub mode: Access,
    pub packet: std::sync::Arc<EvaluatedValue>,
    pub span: Span,
    pub heap: Option<std::sync::Arc<CopyHeapSnapshot>>,
}

#[derive(Debug, Clone)]
pub struct CallableEntry {
    pub parent: Option<ActivationEpochId>,
    pub caller_context: ResumptionContext,
    pub origin: EntryOrigin,
    pub allocation_epoch: u64,
    pub callee: Option<std::sync::Arc<EvaluatedValue>>,
    pub arguments: std::sync::Arc<Vec<EntryArgument>>,
}
