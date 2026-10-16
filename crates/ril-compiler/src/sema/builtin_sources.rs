//! Original primitive source contracts, attached to physical observations.
//! The raw annotations remain available for explanation. They are not a
//! closed source witness or a proof that a receiving bound is satisfied.
use super::{effect_identity::InvocationContext, model::BindingId};
use ril_compiler_core::diagnostic::CauseId;
use ril_syntax::ast::TypeExpr;
use std::collections::BTreeSet;

#[derive(Debug, Clone)]
pub struct BuiltinSourceObservation {
    pub expression: usize,
    pub context: InvocationContext,
    pub identity: String,
    pub full_header: TypeExpr,
    pub concrete_effects: BTreeSet<String>,
    pub written_formals: BTreeSet<u32>,
    pub captures: BTreeSet<BindingId>,
    pub cause: CauseId,
}
