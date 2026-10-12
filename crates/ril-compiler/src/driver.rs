//! Filesystem and target selection boundary for compilation requests.
use crate::{CompilationOutcome, Session};
use std::path::Path;

#[derive(Debug, thiserror::Error)]
pub enum DriverError {
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Target(#[from] ril_codegen::target::UnsupportedTarget),
    #[error("source exceeds the supported size")]
    SourceTooLarge,
}

pub fn check_path(path: &Path, target: &str) -> Result<CompilationOutcome, DriverError> {
    ril_codegen::target::TargetSpec::native(target)?;
    let bytes = std::fs::read(path)?;
    if bytes.len() > u32::MAX as usize {
        return Err(DriverError::SourceTooLarge);
    }
    tracing::debug!(path = %path.display(), target, "checking compilation input");
    Ok(Session::new(bytes).check())
}

/// The build path cannot create artifacts before successful semantic analysis.
pub fn build_path(path: &Path, target: &str) -> Result<CompilationOutcome, DriverError> {
    check_path(path, target)
}
