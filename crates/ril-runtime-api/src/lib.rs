//! Logical runtime contracts, not a frozen binary ABI or object layout.
mod error;
pub mod execution;
pub mod gc;

pub const CONTRACT_VERSION: u32 = 1;
pub use error::Unavailable;
pub use execution::{ExecutionBoundary, LanguagePanic, TaskId, TaskOutcome};
pub use gc::{ManagedHeap, ObjectId, RootId, TypeDescriptorId};
