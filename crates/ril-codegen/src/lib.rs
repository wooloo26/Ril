//! Code generation contracts, target descriptions, and native lowering.
pub mod artifact;
pub mod backend;
pub mod link;
pub mod lower;
pub mod target;

pub use artifact::{ObjectArtifact, SourceArtifact};
pub use backend::{BackendError, NativeBackend, SourceBackend};
pub use link::{LinkRequest, Linker};
