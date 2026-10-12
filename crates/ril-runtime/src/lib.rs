//! Native runtime reservation. There is no collector or scheduler yet.
pub use ril_runtime_api as api;
mod status;
pub use status::{RuntimeStatus, STATUS};
