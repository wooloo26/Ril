mod decl;
mod expr;
mod pattern;
mod types;

use ril_base::{
    diag::{Code, Diagnostic},
    span::{SourceFile, Span},
};

use crate::{
    lexer::{Kind, Token, Word},
    syntax::{Ast, Mode, Name, Path, Segment, Spanned, Storage},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FileKind {
    Module,
    Interface,
    Executable,
    Foreign,
    Snippet,
}

pub fn parse(file: &SourceFile, tokens: &[Token], kind: FileKind) -> Result<Ast> {
    let mut parser = Parser {
        file,
        tokens,
        pos: 0,
        split: 0,
        ast: Ast::default(),
        delimiters: Vec::new(),
        last: file.span(0, 0),
        kind,
        depth: 0,
    };
    parser.ast.items = parser.sequence(
        None,
        if kind == FileKind::Snippet {
            decl::Context::Snippet
        } else {
            decl::Context::Module
        },
    )?;
    Ok(parser.ast)
}

type Result<T> = std::result::Result<T, Diagnostic>;

#[derive(Clone, Copy)]
enum Layout {
    List,
    Block,
}

#[derive(Clone, Copy)]
struct Delimiter {
    close: &'static str,
    opening: Span,
    layout: Layout,
}

struct Parser<'a> {
    file: &'a SourceFile,
    tokens: &'a [Token],
    pos: usize,
    split: usize,
    ast: Ast,
    delimiters: Vec<Delimiter>,
    last: Span,
    kind: FileKind,
    depth: usize,
}

impl Parser<'_> {
    fn current(&self) -> Token {
        let mut token = self.tokens.get(self.pos).copied().unwrap_or(Token {
            kind: Kind::Eof,
            span: self
                .file
                .span(self.file.text().len(), self.file.text().len()),
            tight_left: false,
        });
        token.span.start += self.split;
        token.tight_left |= self.split != 0;
        if self.split != 0
            && token.text(self.file) == "="
            && self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|next| next.tight_left && next.text(self.file).starts_with('='))
        {
            token.span.end += 1;
        }
        token
    }

    fn text(&self) -> &str {
        self.current().text(self.file)
    }

    fn next_text(&self) -> &str {
        self.tokens
            .get(self.pos + 1)
            .map(|token| token.text(self.file))
            .unwrap_or_default()
    }

    fn is(&self, text: &str) -> bool {
        self.text() == text
            && !matches!(
                self.current().kind,
                Kind::StringChunk | Kind::InterpolationEnd
            )
    }

    fn tight(&self, text: &str) -> bool {
        self.is(text) && self.current().tight_left
    }

    fn bump(&mut self) -> Token {
        let token = self.current();
        if token.kind != Kind::Eof {
            self.last = token.span;
            self.advance_to(token.span.end);
        }
        token
    }

    fn advance_to(&mut self, end: usize) {
        self.split = 0;
        while let Some(token) = self.tokens.get(self.pos) {
            if end < token.span.end {
                self.split = end - token.span.start;
                break;
            }
            self.pos += 1;
            if end == token.span.end {
                break;
            }
        }
    }

    fn consume_prefix(&mut self) {
        let span = self.current().span;
        self.last = Span::new(span.file, span.start, span.start + 1);
        self.advance_to(self.last.end);
    }

    fn eat(&mut self, text: &str) -> bool {
        if self.is(text) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn skip_lines(&mut self) {
        while self.current().kind == Kind::Newline {
            self.bump();
        }
    }

    fn layout(&mut self) {
        if self
            .delimiters
            .last()
            .is_some_and(|d| matches!(d.layout, Layout::List))
        {
            self.skip_lines();
        }
    }

    fn continue_lines(&mut self, accepts: impl Fn(&str) -> bool) {
        if self.current().kind != Kind::Newline {
            return;
        }
        if self
            .tokens
            .get(self.pos..)
            .and_then(|tokens| tokens.iter().find(|tok| tok.kind != Kind::Newline))
            .is_some_and(|tok| accepts(tok.text(self.file)))
        {
            self.skip_lines();
        }
    }

    fn separators(&mut self) -> bool {
        let initial = self.pos;
        while self.eat(";") || self.current().kind == Kind::Newline {
            if self.current().kind == Kind::Newline {
                self.bump();
            }
        }
        self.pos != initial
    }

    fn error(&self, code: Code, span: Span, message: impl Into<String>) -> Diagnostic {
        Diagnostic::error(code, span, message)
    }

    fn unexpected(&self, message: impl Into<String>) -> Diagnostic {
        let tok = self.current();
        if tok.kind == Kind::Eof {
            if let Some(delimiter) = self.delimiters.last() {
                return self.error(
                    Code::E0122,
                    delimiter.opening,
                    format!("unclosed delimiter, expected {}", delimiter.close),
                );
            }
            return self.error(Code::E0121, tok.span, message);
        }
        if matches!(self.text(), ")" | "]" | "}")
            && self
                .delimiters
                .last()
                .is_none_or(|d| d.close != self.text())
            && tok.kind != Kind::InterpolationEnd
        {
            return self.error(
                Code::E0123,
                tok.span,
                format!("mismatched closing delimiter {}", self.text()),
            );
        }
        self.error(Code::E0120, tok.span, message)
    }

    fn require(&mut self, text: &str) -> Result<Token> {
        if self.is(text) {
            return Ok(self.bump());
        }
        let message = format!("expected {text:?}");
        let unexpected = self.unexpected(&message);
        if unexpected.code == Some(Code::E0120) && matches!(text, "->" | "=" | ":") {
            return Err(self.error(Code::E0124, self.current().span, message));
        }
        Err(unexpected)
    }

    fn open(&mut self, text: &str, close: &'static str, layout: Layout) -> Result<Span> {
        let opening = self.require(text)?.span;
        self.delimiters.push(Delimiter {
            close,
            opening,
            layout,
        });
        Ok(opening)
    }

    fn at_end(&self, close: &str) -> bool {
        if close == ">" {
            self.text().starts_with('>')
        } else {
            self.is(close)
        }
    }

    fn close(&mut self, close: &str) -> Result<()> {
        if close == ">" && self.text().starts_with('>') && self.text().len() > 1 {
            self.consume_prefix();
        } else {
            self.require(close)?;
        }
        self.delimiters.pop();
        Ok(())
    }

    fn list<T>(
        &mut self,
        close: &str,
        mut item: impl FnMut(&mut Self) -> Result<T>,
    ) -> Result<Vec<T>> {
        let mut out = Vec::new();
        self.skip_lines();
        while !self.at_end(close) {
            out.push(item(self)?);
            self.skip_lines();
            if !self.eat(",") {
                break;
            }
            self.skip_lines();
        }
        self.close(close)?;
        Ok(out)
    }

    fn nested<T>(&mut self, parse: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        if self.depth == 96 {
            return Err(self.unexpected("source nesting exceeds the parser limit"));
        }
        self.depth += 1;
        let result = parse(self);
        self.depth -= 1;
        result
    }

    fn name(&mut self, role: Option<Word>, wildcard: bool) -> Result<Name> {
        let token = self.current();
        let Kind::Word(kind) = token.kind else {
            return Err(self.unexpected("expected identifier"));
        };
        if matches!(kind, Word::Keyword | Word::Primitive) {
            return Err(self.error(Code::E0113, token.span, "reserved identifier"));
        }
        if !(role.is_none_or(|role| role == kind) && kind != Word::Wildcard
            || wildcard && kind == Word::Wildcard)
        {
            return Err(self.error(
                Code::E0101,
                token.span,
                "identifier casing does not match its declaration",
            ));
        }
        self.bump();
        Ok(self.owned(token))
    }

    fn owned(&self, token: Token) -> Name {
        Spanned::new(token.text(self.file).into(), token.span)
    }

    fn path(&mut self, angle: Angle, primitive: bool) -> Result<Path> {
        let start = self.current().span;
        let mut segments = Vec::new();
        loop {
            let name = if primitive && matches!(self.current().kind, Kind::Word(Word::Primitive)) {
                let token = self.bump();
                self.owned(token)
            } else {
                self.name(None, false)?
            };
            let arguments = if self.is("<")
                && match angle {
                    Angle::Type => true,
                    Angle::Expression => self.current().tight_left && self.matching_angle(),
                    Angle::None => false,
                } {
                self.generic_args()?
            } else {
                Vec::new()
            };
            segments.push(Segment { name, arguments });
            self.continue_lines(|token| token == "::");
            if !self.eat("::") {
                break;
            }
            self.skip_lines();
        }
        Ok(Path {
            segments,
            span: start.join(self.last),
        })
    }

    fn matching_angle(&self) -> bool {
        let Some(tokens) = self.tokens.get(self.pos..) else {
            return false;
        };
        let mut depth: usize = 0;
        let mut groups = Vec::new();
        for &token in tokens {
            match token.text(self.file) {
                "(" => groups.push(")"),
                "[" => groups.push("]"),
                ".{" | "{" => groups.push("}"),
                ")" | "]" | "}" => {
                    if groups.pop() != Some(token.text(self.file)) {
                        break;
                    }
                }
                _ if !groups.is_empty() => {}
                "<" | "!<" => depth += 1,
                ">" | ">>" | ">=" | ">>=" => {
                    let count = token
                        .text(self.file)
                        .bytes()
                        .take_while(|&byte| byte == b'>')
                        .count();
                    if count >= depth {
                        return true;
                    }
                    depth -= count;
                }
                ";" => break,
                _ => {}
            }
        }
        false
    }

    fn mode(&mut self, allowed: &[Mode]) -> Mode {
        let mode = match self.text() {
            "mut" => Mode::Mut,
            "ref" => Mode::Ref,
            "^mut" => Mode::Shared,
            "new" => Mode::New,
            "via" => Mode::Via,
            "infer" => Mode::Infer,
            _ => Mode::Plain,
        };
        if mode != Mode::Plain && allowed.contains(&mode) {
            self.bump();
            mode
        } else {
            Mode::Plain
        }
    }

    fn storage(&mut self, paths: bool) -> Result<Storage> {
        self.eat("let");
        let variable = self.eat("var");
        let mode = self.mode(&[Mode::Mut, Mode::Shared, Mode::Ref, Mode::Via]);
        let is_path = matches!(
            self.current().kind,
            Kind::Word(Word::Pascal | Word::Constant)
        ) && self.next_text() != ":"
            && self.next_text() != "}";
        let mode_path = if paths && mode == Mode::Plain && is_path {
            Some(self.path(Angle::None, false)?)
        } else {
            None
        };
        Ok(Storage {
            variable,
            mode,
            mode_path,
        })
    }
}

#[derive(Clone, Copy)]
enum Angle {
    Type,
    Expression,
    None,
}
