use crate::Unavailable;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TaskId(pub u64);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LanguagePanic {
    pub message: String,
    pub operation: Option<u64>,
}
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum TaskOutcome {
    ReturnedUnit,
    ReturnedOk,
    ReturnedErr,
    Panicked(LanguagePanic),
    Cancelled,
    DoubleFault,
}

/// Scoped cleanup is an execution operation, never a GC finalizer.
pub trait ExecutionBoundary {
    fn finish_task(&mut self, task: TaskId, outcome: TaskOutcome) -> Result<(), Unavailable>;
    fn run_cleanup(&mut self, action: u64) -> Result<(), Unavailable>;
}
