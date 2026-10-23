//! Actual allocation births and typed original roles, before recency transport.
use super::*;
use ril_compiler_core::ids::{ActivationEpochId, PatternId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct AllocationEventId(pub u32);

#[derive(Debug, Clone)]
pub struct AllocationEvent {
    pub id: AllocationEventId,
    pub site: u32,
    pub recent: OriginId,
    pub remap: Option<(OriginId, OriginId)>,
    pub epoch_before: u64,
    pub cause: CauseId,
    pub owner: u32,
    pub anchor: Option<ActivationEpochId>,
    pub position: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PatternWindowSite {
    pub rest: PatternId,
    pub loop_owner: u32,
    pub site: u32,
}
