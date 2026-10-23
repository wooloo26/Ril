//! Complete entry packets. These are retained evidence, never verification flags.
use super::*;
use ril_compiler_core::ids::{
    ActivationEpochId, EvaluationOccurrenceId, ExprId, NumericHoleId, TypeExprId,
};
use std::{collections::BTreeMap, sync::Arc};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OccurrenceIdentity {
    pub source: ExprId,
    pub activation: ActivationEpochId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EvaluationBirthCoordinates {
    pub observation: Option<EvaluationOccurrenceId>,
    pub allocation_epoch: u64,
    pub identity: Option<OccurrenceIdentity>,
    pub context: Option<ResumptionContext>,
    pub environment: Option<FrozenEnvironmentId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceRef {
    pub view: SourceView,
    pub original: Option<TypeExprId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CapturedSource {
    Known(SourceRef),
    Unknown(FrozenEnvironmentId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Construction {
    Opaque,
    Nullary {
        declaration: ril_compiler_core::builtin_calls::NullaryConstructor,
        source: ExprId,
    },
    Array(Vec<Construction>),
    Map(Vec<(Construction, Construction)>),
    Tuple(Vec<Construction>),
    Record(BTreeMap<String, Construction>),
}

/// Preserve the typed failure; missing, pending and failed are distinct states.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceTypesError {
    InvalidEvidence(String),
    BudgetExceeded,
    ForeignIdentity,
    MissingNode,
    SourceNotCaptured,
    SourceViewPending,
    AlreadyDefined,
    DuplicateField,
    InvalidContainer,
    AliasCycle,
    RowCycle,
    NeedsStaticElaboration,
    Unresolved,
    MissingProjection,
    CyclicSubstitution,
    RecursiveLegacyKey,
    IdentityExhausted,
    TransactionOpen,
    InvalidTransaction,
}

#[derive(Debug, Clone)]
pub enum SourceCapture {
    Uncaptured,
    Captured {
        result: Result<CapturedSource, SourceTypesError>,
        fresh: Option<Construction>,
    },
    NumericPending {
        hole: NumericHoleId,
        birth: NumericBirth,
        environment: FrozenEnvironmentId,
        fresh: Option<Construction>,
    },
}

#[derive(Debug, Clone)]
pub enum CurrentValueStep {
    ReadHandle,
    FieldProjection {
        receiver: Arc<EvaluatedValue>,
        slot: Projection,
        cause: CauseId,
    },
    CatalogCallableBound {
        event: CopyCallEventId,
        argument: u32,
        field: Projection,
        span: Span,
    },
}

#[derive(Debug, Clone)]
pub enum CurrentSource {
    Birth,
    Derived {
        input: Arc<EvaluatedValue>,
        step: CurrentValueStep,
        source: SourceRef,
    },
    Numeric {
        hole: NumericHoleId,
        birth: NumericBirth,
        environment: FrozenEnvironmentId,
        resolution: Arc<NumericResolution>,
        source: SourceRef,
    },
    Pending,
    Failed(SourceTypesError),
}

#[derive(Debug, Clone)]
pub struct EvaluatedValue {
    /// The packet's only root value. Heap snapshots contain no second root.
    pub value: Value,
    pub birth: EvaluationBirthCoordinates,
    pub current_epoch: u64,
    pub capture: SourceCapture,
    pub current: CurrentSource,
    /// An obligation marker only; consumers must check the actual evidence.
    pub source_valid: bool,
}

impl EvaluatedValue {
    pub fn value(&self) -> &Value {
        &self.value
    }
}

impl std::ops::Deref for EvaluatedValue {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.value()
    }
}
