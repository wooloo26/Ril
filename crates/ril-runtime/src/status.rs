use crate::api;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RuntimeStatus {
    pub contract_version: u32,
    pub tracing_gc: bool,
    pub task_scheduler: bool,
}
pub const STATUS: RuntimeStatus = RuntimeStatus {
    contract_version: api::CONTRACT_VERSION,
    tracing_gc: false,
    task_scheduler: false,
};
