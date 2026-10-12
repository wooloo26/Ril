//! Backend contracts do not expose concrete code generator types.
use crate::{
    artifact::{ObjectArtifact, SourceArtifact},
    target::TargetSpec,
};
use ril_compiler_core::phase::NotImplemented;

#[derive(Debug, thiserror::Error)]
pub enum BackendError {
    #[error(transparent)]
    NotImplemented(#[from] NotImplemented),
    #[error("unsupported or invalid target: {0}")]
    Target(String),
    #[error("invalid native IR: {0}")]
    InvalidIr(String),
    #[error("code generation failed: {0}")]
    Codegen(String),
}

pub trait NativeBackend {
    fn emit(
        &self,
        module: &ril_ir::native::Module,
        target: &TargetSpec,
    ) -> Result<ObjectArtifact, BackendError>;
}
pub trait SourceBackend {
    fn emit(&self, program: &ril_ir::core::Program) -> Result<SourceArtifact, BackendError>;
}
