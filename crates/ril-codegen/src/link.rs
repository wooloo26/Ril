//! Platform linking is independent from object emission.
use crate::{backend::BackendError, target::TargetSpec};
use std::path::PathBuf;

/// Linkers receive an explicit argument vector; drivers must not concatenate a shell command.
#[derive(Debug, Clone)]
pub struct LinkRequest {
    pub target: TargetSpec,
    pub objects: Vec<PathBuf>,
    pub runtime_library: PathBuf,
    pub output: PathBuf,
}
pub trait Linker {
    fn link(&self, request: &LinkRequest) -> Result<PathBuf, BackendError>;
}
