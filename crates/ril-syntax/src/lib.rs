//! Lossless Rowan syntax and owned, unresolved Ril syntax trees.
pub mod ast;
mod lexer;
mod parse;
mod syntax_kind;
mod tree;
mod validation;

pub use parse::{ExpressionParse, Parse, parse, parse_expression, parse_expression_at, parse_file};
pub use syntax_kind::{RilLanguage, SyntaxKind};
pub use tree::{SyntaxNode, unparsed_tree};

/// Check declaration roles in an unresolved owned program before resolution
/// introduces compiler-generated names. Parsing diagnostics remain separate.
pub fn validate_program(program: &ast::Program) -> Vec<ril_compiler_core::diagnostic::Diagnostic> {
    validation::validate(program)
}

pub fn is_reserved_identifier(text: &str) -> bool {
    lexer::keyword(text)
}
