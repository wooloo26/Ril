use crate::{RilLanguage, SyntaxKind};
use rowan::{GreenNode, GreenNodeBuilder, Language};

pub type SyntaxNode = rowan::SyntaxNode<RilLanguage>;

/// An unparsed envelope preserves trivia and text without claiming syntax validity.
pub fn unparsed_tree(text: &str) -> GreenNode {
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(RilLanguage::kind_to_raw(SyntaxKind::Root));
    builder.token(RilLanguage::kind_to_raw(SyntaxKind::Unparsed), text);
    builder.finish_node();
    builder.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;
    #[test]
    fn envelope_is_lossless_but_not_a_successful_parse() {
        let text = "-- comment\r\nlet 文 = \"unterminated";
        assert_eq!(SyntaxNode::new_root(unparsed_tree(text)).to_string(), text);
        assert!(parse(text).is_err());
    }
}
