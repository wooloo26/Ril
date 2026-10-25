//! Logical runtime contracts, not a frozen binary ABI or object layout.
pub mod abi;
pub mod builtins;
mod error;
pub mod execution;
pub mod foreign;
pub mod gc;

// Entry validation requires the compiler and static library to share this ABI.
pub const CONTRACT_VERSION: u32 = abi::ABI_VERSION;
pub use error::Unavailable;
pub use execution::{ExecutionBoundary, LanguagePanic, TaskId, TaskOutcome};
pub use gc::{ManagedHeap, ObjectId, RootId, TypeDescriptorId};
