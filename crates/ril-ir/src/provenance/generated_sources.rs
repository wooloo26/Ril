//! Checked adapter source recipes retained across the frontend/IR boundary.
use super::{ContractSyntax, CopyCallEventId, Projection, ResumptionContext};
use ril_compiler_core::{
    ids::{ClosureObjectId, ClosureSiteId},
    source::Span,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GeneratedAdapter {
    Indexed,
    Map,
    Filter,
    Take,
}

#[derive(Debug, Clone)]
pub struct GeneratedCapture {
    pub binding: u32,
    pub origin_slot: u32,
    pub path: Vec<Projection>,
}

#[derive(Debug, Clone)]
pub struct GeneratedSource {
    pub id: u32,
    pub origin_event: CopyCallEventId,
    pub origin_context: ResumptionContext,
    pub adapter: GeneratedAdapter,
    pub closure: ClosureObjectId,
    pub site: ClosureSiteId,
    pub signature: ContractSyntax,
    pub body: Span,
    pub captures: Vec<GeneratedCapture>,
}
