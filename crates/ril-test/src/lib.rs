//! Test containers and adapter contracts. This crate never interprets Ril.
mod annotations;
mod bundle;
mod corpus;
mod error;
mod outcome;
mod registry;
pub use bundle::*;
pub use corpus::*;
pub(crate) use error::require;
pub use error::{Error, Result};
pub use outcome::*;
pub use registry::*;
