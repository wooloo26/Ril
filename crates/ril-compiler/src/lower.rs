//! Lowering from semantically verified HIR to structured Core IR.
use ril_compiler_core::phase::{NotImplemented, Stage};

pub fn lower_core(
    _program: &crate::hir::VerifiedProgram,
) -> Result<ril_ir::core::Program, NotImplemented> {
    Err(NotImplemented::new(
        Stage::Lowering,
        "verified HIR to structured Core IR",
    ))
}
