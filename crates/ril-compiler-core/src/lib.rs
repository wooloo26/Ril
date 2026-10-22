//! Shared compiler data without parser, query-engine, or backend dependencies.
pub mod builtin_calls;
pub mod builtin_types;
pub mod diagnostic;
pub mod ids;
pub mod numeric_builtins;
pub mod phase;
pub mod projection;
pub mod source;
pub mod target;
