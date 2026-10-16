//! Compiler-generated iterator bodies retain their real source operation.
//! These records are explanatory until their recipe, captures and physical
//! creation/result observations have passed independent validation.
use super::{
    copy_contract::CopyCallEventId, effect_identity::InvocationContext, facts::Slot,
    model::BindingId,
};
use ril_compiler_core::ids::ClosureSiteId;
use ril_syntax::ast::Expr;
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct GeneratedSourceId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneratedCapture {
    pub binding: BindingId,
    pub origin_slot: u32,
    pub path: Vec<Slot>,
}

#[derive(Debug, Clone)]
pub struct GeneratedSource {
    pub id: GeneratedSourceId,
    pub origin_event: CopyCallEventId,
    pub origin_context: InvocationContext,
    pub adapter: super::IterAdapterKind,
    pub closure: usize,
    pub site: ClosureSiteId,
    pub syntax: Arc<Expr>,
    pub captures: Vec<GeneratedCapture>,
}
