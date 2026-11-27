//! Lossless concrete syntax token stream (`CstFile`) preserving every source byte,
//! including whitespace and line comments, for `ril fmt` and IDE refactoring.

use ril_source::{
    diag::Diagnostic,
    span::{SourceFile, Span},
};

use crate::lexer::{self, Kind, Token, Trivia};

/// A single concrete element in source order: either a semantic [`Token`] or [`Trivia`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CstElement {
    Token(Token),
    Trivia(Trivia),
}

impl CstElement {
    pub const fn span(self) -> Span {
        match self {
            Self::Token(token) => token.span,
            Self::Trivia(trivia) => trivia.span,
        }
    }

    pub fn text(self, source: &SourceFile) -> &str {
        let span = self.span();
        source.text().get(span.start..span.end).unwrap_or_default()
    }
}

/// Lossless concrete syntax representation of a Ril source file.
#[derive(Clone, Debug)]
pub struct CstFile {
    pub elements: Vec<CstElement>,
    pub diagnostics: Vec<Diagnostic>,
}

impl CstFile {
    /// Lexes `source` with full error recovery and merges semantic tokens with all
    /// trivia into a single byte-exact ordered stream.
    pub fn lex(source: &SourceFile) -> Self {
        let lexed = lexer::lex_with_recovery(source);
        let mut elements = Vec::with_capacity(lexed.tokens.len() + lexed.trivia.len());
        let mut t_idx = 0usize;
        let mut tr_idx = 0usize;
        let mut cursor = 0usize;

        while t_idx < lexed.tokens.len() || tr_idx < lexed.trivia.len() {
            let next_tok = lexed.tokens.get(t_idx).copied();
            let next_triv = lexed.trivia.get(tr_idx).copied();

            let take_trivia = match (next_tok, next_triv) {
                (Some(tok), Some(triv)) => {
                    if tok.kind == Kind::Eof {
                        true
                    } else {
                        triv.span.start < tok.span.start
                    }
                }
                (None, Some(_)) => true,
                (Some(_), None) | (None, None) => false,
            };

            if take_trivia {
                if let Some(triv) = next_triv {
                    if triv.span.start >= cursor && triv.span.end > triv.span.start {
                        elements.push(CstElement::Trivia(triv));
                        cursor = triv.span.end;
                    }
                    tr_idx += 1;
                }
            } else if let Some(tok) = next_tok {
                if tok.kind == Kind::Eof {
                    elements.push(CstElement::Token(tok));
                    t_idx += 1;
                } else {
                    if tok.span.start >= cursor && tok.span.end >= tok.span.start {
                        elements.push(CstElement::Token(tok));
                        cursor = tok.span.end;
                    }
                    t_idx += 1;
                }
            }
        }

        Self {
            elements,
            diagnostics: lexed.diagnostics,
        }
    }

    /// Reconstructs the exact source text from the concrete syntax stream.
    ///
    /// For any lexically valid Ril file, `CstFile::lex(&src).reconstruct(&src) == src.text()`.
    pub fn reconstruct(&self, source: &SourceFile) -> String {
        let mut out = String::with_capacity(source.text().len());
        let mut cursor = 0usize;
        for &elem in &self.elements {
            let span = elem.span();
            if span.start > cursor
                && let Some(gap) = source.text().get(cursor..span.start)
            {
                out.push_str(gap);
            }
            if span.end > span.start {
                out.push_str(elem.text(source));
                cursor = span.end;
            }
        }
        if cursor < source.text().len()
            && let Some(tail) = source.text().get(cursor..)
        {
            out.push_str(tail);
        }
        out
    }
}
