//! Allocation births are recorded at the shared heap entry, before recency
//! transport. A frozen node cannot borrow a different birth of the same site.
use super::facts::{NodeId, ScopeId, SiteId};
use ril_compiler_core::{
    diagnostic::CauseId,
    ids::{ActivationEpochId, PatternId},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct AllocationEventId(pub u32);

#[derive(Debug, Clone)]
pub struct AllocationEvent {
    pub id: AllocationEventId,
    pub site: SiteId,
    /// The actual recent node returned by the heap, before later reuse.
    pub recent: NodeId,
    pub remap: Option<(NodeId, NodeId)>,
    pub epoch_before: usize,
    pub cause: CauseId,
    pub owner: ScopeId,
    pub anchor: Option<ActivationEpochId>,
    /// Physical emission cursor at allocation, independent of diagnostic spans.
    pub position: usize,
}
impl AllocationEvent {
    pub fn epoch_after(&self) -> usize {
        self.epoch_before
            .saturating_add(usize::from(self.remap.is_some()))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PatternWindowSite {
    pub rest: PatternId,
    pub loop_owner: ScopeId,
    pub site: SiteId,
}
