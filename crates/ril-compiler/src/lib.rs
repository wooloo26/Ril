//! Ril source frontend.
pub mod ast;
pub mod diagnostic;
pub mod frontend;
pub mod hir;
mod lexer;
pub mod library;
mod parse;
pub mod source;
mod syntax_kind;
pub mod text;
mod validation;

pub use parse::Parse;
pub use syntax_kind::{RilLanguage, SyntaxKind};

pub type SyntaxNode = rowan::SyntaxNode<RilLanguage>;
