//! Historical inputs and storage intervals of pattern-generated windows.
use super::*;
use ril_compiler_core::ids::{ActivationEpochId, ConstRef, PatternId};
use std::sync::Arc;

#[derive(Debug, Clone)]
pub struct PatternWindowInfo {
    pub pattern: Option<PatternId>,
    pub constant: Option<ConstRef>,
    pub backing: Vec<OriginId>,
    pub choices: Vec<(u32, Vec<Vec<OriginId>>)>,
    pub lower: Option<u64>,
    pub length: Option<u64>,
    pub span: Span,
    pub cause: CauseId,
}

#[derive(Debug, Clone, Copy)]
pub enum PatternWindowOrigin {
    /// Original creation-arena ordinal, never selected by equal contents.
    Pattern(u64),
    Constant(ConstRef),
}

#[derive(Debug, Clone)]
pub struct PatternWindowInput {
    pub node: OriginId,
    pub origin: PatternWindowOrigin,
    pub info: PatternWindowInfo,
}

#[derive(Debug, Clone)]
pub struct PatternWindowCreation {
    pub allocation: AllocationEventId,
    pub root: PatternId,
    pub rest: PatternId,
    pub anchor: Option<ActivationEpochId>,
    pub context: ResumptionContext,
    pub owner: u32,
    pub input: Arc<EvaluatedValue>,
    pub heap: Arc<CopyHeapSnapshot>,
    pub parents: Vec<PatternWindowInput>,
    pub prefix: u32,
    pub suffix: u32,
    pub output: Arc<EvaluatedValue>,
    pub output_node: CopyNode,
    pub info: PatternWindowInfo,
}
