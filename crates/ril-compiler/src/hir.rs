//! Frontend definitions and the semantic verification boundary.
use ril_compiler_core::{ids::DefinitionId, source::Span};

#[derive(Debug, Clone)]
pub struct Definition {
    pub id: DefinitionId,
    pub span: Span,
}

/// Construction is private to the compiler; IR data alone does not imply verification.
#[derive(Debug)]
pub struct VerifiedProgram {
    definitions: Vec<Definition>,
}
impl VerifiedProgram {
    pub fn definitions(&self) -> &[Definition] {
        &self.definitions
    }
}
