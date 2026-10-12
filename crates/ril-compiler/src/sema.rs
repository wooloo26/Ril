//! Semantic checking entry point. Individual phases are implemented here as needed.
use crate::hir::VerifiedProgram;
use ril_compiler_core::phase::{NotImplemented, Stage};

pub fn analyze(_syntax: &ril_syntax::SyntaxNode) -> Result<VerifiedProgram, NotImplemented> {
    Err(NotImplemented::new(
        Stage::Resolution,
        "name resolution and semantic verification",
    ))
}
