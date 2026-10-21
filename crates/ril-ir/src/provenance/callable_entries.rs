//! Evaluation ancestry and original callable inputs retained through Core.
use super::*;
use ril_compiler_core::ids::{ActivationEpochId, EvaluationOccurrenceId, ExprId};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActivationKind {
    Expression,
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
    Observed(EvaluationOccurrenceId),
    Widened(EvaluationOccurrenceId),
    Scalar(ScalarInput),
    Copied {
        observation: EvaluationOccurrenceId,
        boundary: CopyBoundaryId,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarInput {
    PositiveInt,
    ByteSuffix(EvaluationOccurrenceId),
    BufferedBytes(EvaluationOccurrenceId),
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
    SignatureProbe,
    Unresolved,
}

#[derive(Debug, Clone)]
pub struct CallableEntry<A = Vec<(Access, Value)>> {
    pub parent: Option<ActivationEpochId>,
    pub caller_context: ResumptionContext,
    pub origin: EntryOrigin,
    pub allocation_epoch: u64,
    pub arguments: A,
}
