//! Shared stage identities and explicit incomplete-stage outcomes.
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Stage {
    Syntax,
    Resolution,
    Types,
    Effects,
    Provenance,
    Termination,
    StaticEvaluation,
    Lowering,
    Codegen,
    Linking,
    Runtime,
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error, Serialize, Deserialize)]
#[error("{stage:?} is not implemented: {detail}")]
pub struct NotImplemented {
    pub stage: Stage,
    pub detail: String,
}

impl NotImplemented {
    pub fn new(stage: Stage, detail: impl Into<String>) -> Self {
        Self {
            stage,
            detail: detail.into(),
        }
    }
}
