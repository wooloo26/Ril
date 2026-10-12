use crate::SyntaxNode;
/// Typed AST nodes will be constructible only from a completed parser.
pub trait AstNode: Sized {
    fn cast(node: SyntaxNode) -> Option<Self>;
    fn syntax(&self) -> &SyntaxNode;
}
