use rowan::Language;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u16)]
pub enum SyntaxKind {
    Root,
    Unparsed,
    Whitespace,
    Newline,
    Comment,
    Identifier,
    Keyword,
    Integer,
    Float,
    String,
    RawString,
    Bytes,
    Punctuation,
    Invalid,
    Statement,
    Declaration,
    Block,
    Expression,
    TypeExpression,
    Pattern,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RilLanguage {}
impl Language for RilLanguage {
    type Kind = SyntaxKind;
    fn kind_from_raw(raw: rowan::SyntaxKind) -> SyntaxKind {
        match raw.0 {
            0 => SyntaxKind::Root,
            1 => SyntaxKind::Unparsed,
            2 => SyntaxKind::Whitespace,
            3 => SyntaxKind::Newline,
            4 => SyntaxKind::Comment,
            5 => SyntaxKind::Identifier,
            6 => SyntaxKind::Keyword,
            7 => SyntaxKind::Integer,
            8 => SyntaxKind::Float,
            9 => SyntaxKind::String,
            10 => SyntaxKind::RawString,
            11 => SyntaxKind::Bytes,
            12 => SyntaxKind::Punctuation,
            13 => SyntaxKind::Invalid,
            14 => SyntaxKind::Statement,
            15 => SyntaxKind::Declaration,
            16 => SyntaxKind::Block,
            17 => SyntaxKind::Expression,
            18 => SyntaxKind::TypeExpression,
            19 => SyntaxKind::Pattern,
            _ => panic!("invalid Ril syntax kind"),
        }
    }
    fn kind_to_raw(kind: SyntaxKind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind as u16)
    }
}
