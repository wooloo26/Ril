//! Executable metadata needed after semantic analysis. Analysis histories and
//! proof packets remain frontend concerns and never cross this boundary.
use ril_compiler_core::{
    ids::{CallableOwner, ClosureSiteId, DefinitionId, ExprId, HandlerSiteId},
    source::Span,
    target::TargetLayout,
};
use std::collections::BTreeSet;

#[derive(Debug, Clone, Default)]
pub struct ProgramMetadata {
    pub target_layout: Option<TargetLayout>,
    pub generic_templates: BTreeSet<DefinitionId>,
    pub specializations: Vec<crate::specialization::Instance>,
    pub retained_handlers: Vec<RetainedHandler>,
    pub closure_sites: Vec<ClosureSite>,
    pub nonretaining_adapters: Vec<NonRetainingAdapter>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GenericParameter {
    pub declaration: DefinitionId,
    pub index: u32,
}

#[derive(Debug, Clone)]
pub struct RetainedHandler {
    pub callable: Option<CallableOwner>,
    pub span: Span,
    pub definitions: Option<Vec<HandlerSiteId>>,
}

#[derive(Debug, Clone)]
pub struct ClosureSite {
    pub id: ClosureSiteId,
    pub owner: CallableOwner,
    pub source: ExprId,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct NonRetainingAdapter {
    pub owner: CallableOwner,
    pub span: Span,
    pub builtin: NonRetainingBuiltin,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NonRetainingBuiltin {
    ConcurrentFork,
    ConcurrentJoin,
}
