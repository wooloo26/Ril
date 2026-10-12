//! Backend output data, independent of the chosen emitter.
use crate::target::{ObjectFormat, TargetSpec};
use std::path::PathBuf;

#[derive(Debug, Clone)]
pub struct ObjectArtifact {
    pub target: TargetSpec,
    pub format: ObjectFormat,
    pub bytes: Vec<u8>,
    pub runtime_contract_version: u32,
}
#[derive(Debug, Clone)]
pub struct SourceArtifact {
    pub language: String,
    pub files: Vec<(PathBuf, String)>,
}
