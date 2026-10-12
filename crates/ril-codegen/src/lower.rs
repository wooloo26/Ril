//! Native representations are selected after the shared Core IR boundary.
use ril_compiler_core::phase::{NotImplemented, Stage};

pub fn lower_native(
    _program: &ril_ir::core::Program,
) -> Result<ril_ir::native::Module, NotImplemented> {
    Err(NotImplemented::new(
        Stage::Lowering,
        "monomorphization, closures, effects, GC roots and native layout",
    ))
}
