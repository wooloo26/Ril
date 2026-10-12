//! Lossless syntax storage; language tokenization and parsing are not implemented.
pub mod ast;
mod parse;
mod syntax_kind;
mod tree;

pub use parse::parse;
pub use syntax_kind::{RilLanguage, SyntaxKind};
pub use tree::{SyntaxNode, unparsed_tree};
