//! Shared Ril frontend and compilation orchestration.
pub mod db;
pub mod driver;
pub mod hir;
pub mod lower;
pub mod modules;
mod normalize;
pub mod numeric_literals;
mod provenance_lower;
pub mod sema;
pub mod session;
pub mod static_eval;
mod syntax_sites;
pub mod termination;
mod type_identity_lower;

pub use db::{Database, SourceFacts, SourceInput, source_facts};
pub use driver::{BuildOptions, DriverError, build_path, check_path, check_path_with};
pub use session::{
    CheckOptions, CompilationOutcome, ProjectError, ProjectSource, Session, UnitKind,
};
