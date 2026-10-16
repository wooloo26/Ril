//! Presentation of actual outcome-indexed message obligations. These records
//! retain evidence; constructing them does not authorize an operation.
use super::{CopyValueSnapshot, Projection, ResumptionContext};
use ril_compiler_core::{diagnostic::CauseId, ids::OriginId, source::Span};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ChannelMessageId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ChannelRepetitionId(pub u32);

#[derive(Debug, Clone)]
pub struct ChannelRepetition {
    pub id: ChannelRepetitionId,
    pub parent: Option<ChannelRepetitionId>,
    pub context: ResumptionContext,
    pub activation: u32,
    pub call: Option<super::CopyCallEventId>,
    pub start_sequence: u64,
    pub end_sequence: Option<u64>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ChannelGuardLiteral {
    Optional {
        identity: super::OptionalTagId,
        present: bool,
    },
    Result {
        producer: u32,
        version: u32,
        success: bool,
    },
    Transport {
        event: ChannelMessageId,
        producer: u32,
        version: u32,
        success: bool,
    },
    Boolean {
        evaluation: super::ConditionEvaluationId,
        truth: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChannelGuard {
    pub terms: Vec<Vec<ChannelGuardLiteral>>,
    pub incomplete: bool,
}
impl Default for ChannelGuard {
    fn default() -> Self {
        Self {
            terms: vec![vec![]],
            incomplete: false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum ChannelAnchor {
    Known { channel: OriginId, scope: OriginId },
    Formal { endpoint: OriginId, scope: OriginId },
}

#[derive(Debug, Clone)]
pub struct ChannelBindingPath {
    pub binding: u32,
    pub projection: Vec<Projection>,
}

#[derive(Debug, Clone)]
pub struct ChannelReceiveSource {
    pub guard: ChannelGuard,
    pub send: Option<ChannelMessageId>,
}

#[derive(Debug, Clone)]
pub enum ChannelAction {
    TaskFork {
        child: OriginId,
    },
    TaskJoin {
        child: OriginId,
    },
    Send {
        endpoint: CopyValueSnapshot,
        anchor: ChannelAnchor,
        payload: CopyValueSnapshot,
        transport: CopyValueSnapshot,
        producer_versions: Vec<(u32, u32)>,
        original_owners: Vec<(u32, u32)>,
        dependencies: Vec<ChannelBindingPath>,
    },
    Receive {
        endpoint: CopyValueSnapshot,
        anchor: ChannelAnchor,
        payload: CopyValueSnapshot,
        transport: CopyValueSnapshot,
        producer_versions: Vec<(u32, u32)>,
        sources: Vec<ChannelReceiveSource>,
        dependencies: Vec<ChannelBindingPath>,
    },
    TagTest {
        subject: CopyValueSnapshot,
        success: bool,
        pattern: Span,
        producer_versions: Vec<(u32, u32)>,
    },
    ConditionEvaluated {
        evaluation: super::ConditionEvaluationId,
        subject_expression: usize,
        subject: CopyValueSnapshot,
    },
    Inspect {
        value: CopyValueSnapshot,
        producer_versions: Vec<(u32, u32)>,
    },
    Select {
        evaluation: super::ConditionEvaluationId,
        truth: bool,
    },
    ResultAliases {
        map: Vec<(u32, Vec<u32>)>,
    },
    ResultTransfer {
        from: u32,
        to: u32,
        source: CopyValueSnapshot,
        producers: Vec<u32>,
    },
}

#[derive(Debug, Clone)]
pub struct ChannelMessageFact {
    pub id: ChannelMessageId,
    pub source_event: Option<super::CopyCallEventId>,
    pub repetition: Option<ChannelRepetitionId>,
    pub sequence: u64,
    pub context: ResumptionContext,
    pub task: Option<OriginId>,
    pub activation: u32,
    pub span: Span,
    pub cause: CauseId,
    pub allocation_epoch: u64,
    pub guard: ChannelGuard,
    pub action: ChannelAction,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChannelExitKind {
    Complete,
    Callable,
    Return,
    Receiver,
    Scope,
    Abnormal,
}

#[derive(Debug, Clone)]
pub struct ChannelExitFact {
    pub sequence: u64,
    pub context: ResumptionContext,
    pub activation: u32,
    pub span: Span,
    pub cause: CauseId,
    pub allocation_epoch: u64,
    pub guard: ChannelGuard,
    pub kind: ChannelExitKind,
    pub anchor: Option<ChannelAnchor>,
    pub returned: CopyValueSnapshot,
}
