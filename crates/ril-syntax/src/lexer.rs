use ril_source::{
    diag::{Code, Diagnostic},
    span::{SourceFile, Span},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Word {
    Value,
    Pascal,
    Constant,
    Wildcard,
    Keyword,
    Primitive,
}

const KEYWORDS: &[&str] = &[
    "as", "break", "continue", "eff", "else", "false", "fn", "for", "if", "infer", "let", "match",
    "meta", "mut", "new", "pkg", "pub", "ref", "return", "sub", "true", "type", "typeof", "use",
    "var", "via", "where", "while", "with",
];

const PRIMITIVES: &[&str] = &["bool", "int", "f64", "str", "bytes", "never"];

pub fn word_kind(word: &str) -> Option<Word> {
    if KEYWORDS.contains(&word) {
        return Some(Word::Keyword);
    }
    if PRIMITIVES.contains(&word) {
        return Some(Word::Primitive);
    }
    if word == "_" {
        return Some(Word::Wildcard);
    }
    let content = word.strip_prefix('_').unwrap_or(word);
    let first = content.as_bytes().first()?;
    if first.is_ascii_lowercase()
        && content.split('_').all(|part| {
            !part.is_empty()
                && part
                    .bytes()
                    .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit())
        })
    {
        return Some(Word::Value);
    }
    if !word.as_bytes().first()?.is_ascii_uppercase() {
        return None;
    }
    if word.len() > 1
        && word.split('_').all(|part| {
            !part.is_empty()
                && part
                    .bytes()
                    .all(|b| b.is_ascii_uppercase() || b.is_ascii_digit())
        })
    {
        return Some(Word::Constant);
    }
    if word.len() == 1 {
        return Some(Word::Pascal);
    }
    let mut previous_upper = false;
    let mut seen_lower = false;
    for (index, byte) in word.bytes().enumerate() {
        if byte.is_ascii_uppercase() {
            if previous_upper || (index != 0 && !seen_lower) {
                return None;
            }
            previous_upper = true;
        } else if byte.is_ascii_lowercase() || byte.is_ascii_digit() {
            seen_lower |= byte.is_ascii_lowercase();
            previous_upper = false;
        } else {
            return None;
        }
    }
    seen_lower.then_some(Word::Pascal)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Kind {
    Word(Word),
    Int,
    Float,
    TupleIndex,
    StringStart,
    StringChunk,
    StringEnd,
    InterpolationStart,
    InterpolationEnd,
    RawString,
    Bytes,
    RawBytes,
    Punctuation,
    Newline,
    Unknown,
    Eof,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Token {
    pub kind: Kind,
    pub span: Span,
    pub tight_left: bool,
}

impl Token {
    pub fn text(self, source: &SourceFile) -> &str {
        source
            .text()
            .get(self.span.start..self.span.end)
            .unwrap_or_default()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TriviaKind {
    Whitespace,
    LineComment,
    BlockComment,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Trivia {
    pub kind: TriviaKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct LexOutput {
    pub tokens: Vec<Token>,
    pub trivia: Vec<Trivia>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn lex(source: &SourceFile) -> Result<Vec<Token>, Diagnostic> {
    let output = lex_with_recovery(source);
    if let Some(first) = output.diagnostics.into_iter().next() {
        Err(first)
    } else {
        Ok(output.tokens)
    }
}

pub fn lex_with_recovery(source: &SourceFile) -> LexOutput {
    let mut lexer = Lexer {
        source,
        pos: 0,
        tokens: Vec::new(),
        trivia: Vec::new(),
        modes: Vec::new(),
    };
    let mut diagnostics = Vec::new();
    while !lexer.rest().is_empty() {
        let before = lexer.pos;
        let step = if matches!(lexer.modes.last(), Some(Mode::String { .. })) {
            lexer.string()
        } else {
            lexer.code()
        };
        if let Err(diag) = step {
            diagnostics.push(diag);
            // Recover safely while guaranteeing strict forward progress.
            if matches!(lexer.modes.last(), Some(Mode::String { .. })) {
                if lexer.first().is_none_or(|c| matches!(c, '\n' | '\r')) {
                    lexer.modes.pop();
                } else if lexer.pos == before {
                    lexer.bump();
                }
            } else if matches!(lexer.modes.last(), Some(Mode::Interpolation { .. })) {
                if lexer.first().is_none_or(|c| matches!(c, '\n' | '\r')) {
                    lexer.modes.pop();
                    if matches!(lexer.modes.last(), Some(Mode::String { .. })) {
                        lexer.modes.pop();
                    }
                    lexer.bump();
                } else if lexer.pos == before {
                    lexer.bump();
                }
            } else {
                if lexer.pos == before {
                    lexer.bump();
                }
                lexer.emit(Kind::Unknown, before);
            }
        }
    }
    while let Some(mode) = lexer.modes.pop() {
        let (code, start, message) = match mode {
            Mode::String { start } => (Code::E0107, start, "unterminated string"),
            Mode::Interpolation { start, .. } => (Code::E0112, start, "unclosed interpolation"),
        };
        diagnostics.push(lexer.error(code, start, message));
    }
    lexer.emit(Kind::Eof, lexer.pos);
    LexOutput {
        tokens: lexer.tokens,
        trivia: lexer.trivia,
        diagnostics,
    }
}

enum Mode {
    String {
        start: usize,
    },
    Interpolation {
        start: usize,
        braces: usize,
        nonempty: bool,
    },
}

struct Lexer<'a> {
    source: &'a SourceFile,
    pos: usize,
    tokens: Vec<Token>,
    trivia: Vec<Trivia>,
    modes: Vec<Mode>,
}

impl Lexer<'_> {
    fn rest(&self) -> &str {
        self.source.text().get(self.pos..).unwrap_or_default()
    }

    fn first(&self) -> Option<char> {
        self.rest().chars().next()
    }

    fn bump(&mut self) -> Option<char> {
        let ch = self.first()?;
        self.pos += ch.len_utf8();
        Some(ch)
    }

    fn take(&mut self, text: &str) -> bool {
        if self.rest().starts_with(text) {
            self.pos += text.len();
            true
        } else {
            false
        }
    }

    fn emit(&mut self, kind: Kind, start: usize) {
        let tight_left = self
            .tokens
            .last()
            .is_some_and(|prev| prev.span.end == start && prev.kind != Kind::Newline);
        self.tokens.push(Token {
            kind,
            span: self.source.span(start, self.pos),
            tight_left,
        });
    }

    fn error(&self, code: Code, start: usize, message: &str) -> Diagnostic {
        Diagnostic::error(code, self.source.span(start, self.pos), message)
    }

    fn code(&mut self) -> Result<(), Diagnostic> {
        let start = self.pos;
        let Some(ch) = self.first() else {
            return Ok(());
        };
        match ch {
            ' ' | '\t' | '\r' => {
                while self.first().is_some_and(|c| matches!(c, ' ' | '\t' | '\r')) {
                    self.bump();
                }
                self.trivia.push(Trivia {
                    kind: TriviaKind::Whitespace,
                    span: self.source.span(start, self.pos),
                });
                return Ok(());
            }
            '\n' => {
                self.check_literal_newline()?;
                self.pos += 1;
                self.emit(Kind::Newline, start);
                return Ok(());
            }
            _ => {}
        }
        if self.take("--") {
            self.pos += self.rest().find('\n').unwrap_or(self.rest().len());
            self.trivia.push(Trivia {
                kind: TriviaKind::LineComment,
                span: self.source.span(start, self.pos),
            });
            return Ok(());
        }
        if self.take("{-") {
            let result = self.comment(start);
            self.trivia.push(Trivia {
                kind: TriviaKind::BlockComment,
                span: self.source.span(start, self.pos),
            });
            return result;
        }
        if matches!(ch, '\0'..='\u{1f}' | '\u{7f}' | '\u{202a}'..='\u{202e}' | '\u{2066}'..='\u{2069}')
        {
            self.bump();
            return Err(self.error(Code::E0105, start, "disallowed source character"));
        }
        if let Some(Mode::Interpolation {
            start: opening,
            braces,
            nonempty,
        }) = self.modes.last_mut()
        {
            if ch == '}' && *braces == 0 {
                let (opening, nonempty) = (*opening, *nonempty);
                self.pos += 1;
                if !nonempty {
                    return Err(self.error(Code::E0112, opening, "empty interpolation"));
                }
                self.modes.pop();
                self.emit(Kind::InterpolationEnd, start);
                return Ok(());
            }
            *nonempty = true;
            match ch {
                '}' => *braces -= 1,
                '{' => *braces += 1,
                _ if self
                    .source
                    .text()
                    .get(start..)
                    .is_some_and(|text| text.starts_with(".{")) =>
                {
                    *braces += 1;
                }
                _ => {}
            }
        }
        if ch.is_ascii_digit() {
            return self.number(start);
        }
        if ch.is_ascii_alphabetic() || ch == '_' {
            if let Some(rest) = self.rest().strip_prefix("bytes") {
                let hashes = leading_hashes(rest);
                if rest.get(hashes..).is_some_and(|s| s.starts_with('"')) {
                    self.pos += 6 + hashes;
                    return if hashes == 0 {
                        self.bytes(start)
                    } else {
                        self.raw(start, hashes, true)
                    };
                }
            }
            self.bump();
            while self
                .first()
                .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
            {
                self.bump();
            }
            let word = self.source.text().get(start..self.pos).unwrap_or_default();
            let kind = word_kind(word)
                .ok_or_else(|| self.error(Code::E0102, start, "malformed identifier"))?;
            self.emit(Kind::Word(kind), start);
            return Ok(());
        }
        let hashes = leading_hashes(self.rest());
        if hashes > 0
            && self
                .rest()
                .get(hashes..)
                .is_some_and(|s| s.starts_with('"'))
        {
            self.pos += hashes + 1;
            return self.raw(start, hashes, false);
        }
        if self.take("\"") {
            self.emit(Kind::StringStart, start);
            self.modes.push(Mode::String { start });
            return Ok(());
        }
        const OPERATORS: &[&str] = &[
            ">>=", "<<=", "...", "..=", "?.", "??", "::", "->", ".{", "!<", "..", "==", "!=", "<=",
            ">=", "<<", ">>", "&&", "||", "|>", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=",
        ];
        if self
            .rest()
            .strip_prefix("^mut")
            .is_some_and(|rest| !rest.starts_with(|c: char| c.is_ascii_alphanumeric() || c == '_'))
        {
            self.pos += 4;
            self.emit(Kind::Punctuation, start);
        } else if OPERATORS.iter().any(|operator| self.take(operator)) {
            self.emit(Kind::Punctuation, start);
        } else {
            self.bump();
            let kind = if "()[]{}<>,:;.=+-*/%~!&|^?@\\".contains(ch) {
                Kind::Punctuation
            } else {
                Kind::Unknown
            };
            self.emit(kind, start);
        }
        Ok(())
    }

    fn comment(&mut self, start: usize) -> Result<(), Diagnostic> {
        let mut depth = 1;
        while self.first().is_some() {
            if self.take("{-") {
                depth += 1;
            } else if self.take("-}") {
                depth -= 1;
                if depth == 0 {
                    return Ok(());
                }
            } else {
                let offset = self.pos;
                if self.bump() == Some('\n') {
                    self.check_literal_newline()?;
                    self.emit(Kind::Newline, offset);
                }
            }
        }
        Err(self.error(Code::E0106, start, "unterminated block comment"))
    }

    fn check_literal_newline(&self) -> Result<(), Diagnostic> {
        if let Some(Mode::Interpolation { start, .. }) = self.modes.last() {
            return Err(self.error(Code::E0112, *start, "interpolation crosses a line boundary"));
        }
        Ok(())
    }

    fn number(&mut self, start: usize) -> Result<(), Diagnostic> {
        if self
            .tokens
            .last()
            .is_some_and(|tok| matches!(tok.text(self.source), "." | "?."))
        {
            self.pos += self.rest().bytes().take_while(u8::is_ascii_digit).count();
            self.emit(Kind::TupleIndex, start);
            return Ok(());
        }
        let base = match self.rest().get(..2) {
            Some("0x" | "0X") => 16,
            Some("0o" | "0O") => 8,
            Some("0b" | "0B") => 2,
            _ => 10,
        };
        if base != 10 {
            self.pos += 2;
        }
        let digits = self.digits(base, start)?;
        let mut float = false;
        if base == 10
            && self
                .rest()
                .strip_prefix('.')
                .is_some_and(|rest| rest.starts_with(|c: char| c.is_ascii_digit()))
        {
            self.pos += 1;
            self.digits(10, start)?;
            float = true;
        }
        if base == 10 && (self.take("e") || self.take("E")) {
            if !self.take("+") {
                self.take("-");
            }
            if !self.digits(10, start)? {
                return Err(self.error(Code::E0111, start, "missing exponent digits"));
            }
            float = true;
        }
        if !digits
            || self
                .first()
                .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
        {
            while self
                .first()
                .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
            {
                self.bump();
            }
            return Err(self.error(Code::E0111, start, "malformed numeric literal"));
        }
        self.emit(if float { Kind::Float } else { Kind::Int }, start);
        Ok(())
    }

    fn digits(&mut self, base: u32, start: usize) -> Result<bool, Diagnostic> {
        let mut found = false;
        while self.first().is_some_and(|c| c.is_digit(base)) {
            self.bump();
            found = true;
            if self.take("_") && !self.first().is_some_and(|c| c.is_digit(base)) {
                return Err(self.error(Code::E0111, start, "underscore must separate digits"));
            }
        }
        Ok(found)
    }

    fn raw(&mut self, start: usize, hashes: usize, bytes: bool) -> Result<(), Diagnostic> {
        let end = format!("\"{}", "#".repeat(hashes));
        while let Some(ch) = self.first() {
            if self.take(&end) {
                self.emit(
                    if bytes {
                        Kind::RawBytes
                    } else {
                        Kind::RawString
                    },
                    start,
                );
                return Ok(());
            }
            let offset = self.pos;
            self.bump();
            if ch == '\n' {
                self.check_literal_newline()?;
            }
            if bytes && !matches!(ch, '\t' | '\n' | ' '..='~') {
                return Err(self.error(Code::E0110, offset, "invalid raw byte character"));
            }
        }
        Err(self.error(Code::E0107, start, "unterminated raw literal"))
    }

    fn bytes(&mut self, start: usize) -> Result<(), Diagnostic> {
        loop {
            let offset = self.pos;
            match self.bump() {
                Some('"') => {
                    self.emit(Kind::Bytes, start);
                    return Ok(());
                }
                Some('\n' | '\r') | None => {
                    return Err(self.error(Code::E0107, start, "unterminated byte literal"));
                }
                Some('\\') => self.escape(offset, true)?,
                Some(' '..='~') => {}
                _ => return Err(self.error(Code::E0110, offset, "invalid byte character")),
            }
        }
    }

    fn string(&mut self) -> Result<(), Diagnostic> {
        let chunk = self.pos;
        while let Some(ch) = self.first() {
            let offset = self.pos;
            match ch {
                '\n' | '\r' => break,
                '"' => {
                    self.emit_chunk(chunk);
                    self.pos += 1;
                    self.emit(Kind::StringEnd, offset);
                    self.modes.pop();
                    return Ok(());
                }
                '\\' => {
                    self.pos += 1;
                    self.escape(offset, false)?;
                }
                '{' if !self.take("{{") => {
                    self.emit_chunk(chunk);
                    self.pos += 1;
                    self.emit(Kind::InterpolationStart, offset);
                    self.modes.push(Mode::Interpolation {
                        start: offset,
                        braces: 0,
                        nonempty: false,
                    });
                    return Ok(());
                }
                '}' if !self.take("}}") => {
                    self.pos += 1;
                    return Err(self.error(Code::E0112, offset, "unmatched interpolation brace"));
                }
                '{' | '}' => {}
                _ => {
                    self.bump();
                }
            }
        }
        let start = match self.modes.last() {
            Some(Mode::String { start }) => *start,
            _ => chunk,
        };
        Err(self.error(Code::E0107, start, "unterminated string"))
    }

    fn emit_chunk(&mut self, start: usize) {
        if start < self.pos {
            self.emit(Kind::StringChunk, start);
        }
    }

    fn escape(&mut self, start: usize, bytes: bool) -> Result<(), Diagnostic> {
        let code = if bytes { Code::E0110 } else { Code::E0108 };
        match self.bump() {
            Some('\\' | '"' | 'n' | 'r' | 't' | '0') => Ok(()),
            Some('x') if bytes => {
                for _ in 0..2 {
                    if !self.first().is_some_and(|c| c.is_ascii_hexdigit()) {
                        return Err(self.error(code, start, "byte escape needs two hex digits"));
                    }
                    self.pos += 1;
                }
                Ok(())
            }
            Some('u') if !bytes && self.take("{") => {
                let digits = self
                    .rest()
                    .bytes()
                    .take_while(u8::is_ascii_hexdigit)
                    .count();
                let hex = self.rest().get(..digits).unwrap_or_default();
                let value = (1..=6)
                    .contains(&digits)
                    .then(|| u32::from_str_radix(hex, 16).ok())
                    .flatten();
                self.pos += digits;
                if !self.take("}") || value.and_then(char::from_u32).is_none() {
                    return Err(self.error(Code::E0109, start, "invalid Unicode scalar escape"));
                }
                Ok(())
            }
            _ => Err(self.error(code, start, "invalid escape")),
        }
    }
}

fn leading_hashes(text: &str) -> usize {
    text.bytes().take_while(|&byte| byte == b'#').count()
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use ril_source::span::FileId;

    use super::*;

    #[test]
    fn lex_with_recovery_collects_multiple_errors_and_preserves_trivia() {
        let src = SourceFile::from_bytes(
            FileId(1),
            PathBuf::from("pkg/recover.ril"),
            b"-- header comment\nlet bad_One = 1\n{- block -}\nlet bad_Two = 2\n",
        )
        .unwrap_or_else(|e| ril_source::ice!("{e:?}"));
        let output = lex_with_recovery(&src);
        assert_eq!(output.diagnostics.len(), 2);
        assert!(
            output
                .diagnostics
                .iter()
                .all(|d| d.code == Some(Code::E0102))
        );
        assert!(
            output
                .trivia
                .iter()
                .any(|t| t.kind == TriviaKind::LineComment)
        );
        assert!(
            output
                .trivia
                .iter()
                .any(|t| t.kind == TriviaKind::BlockComment)
        );
        assert!(
            output
                .trivia
                .iter()
                .any(|t| t.kind == TriviaKind::Whitespace)
        );
    }
}
