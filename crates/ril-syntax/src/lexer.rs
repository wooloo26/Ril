use crate::SyntaxKind;
use ril_compiler_core::{
    diagnostic::{Diagnostic, Label, Severity},
    source::{FileId, Span},
};

#[derive(Debug, Clone, Copy)]
pub(crate) struct Token {
    pub kind: SyntaxKind,
    pub start: usize,
    pub end: usize,
}

pub(crate) fn diagnostic(
    file: FileId,
    start: usize,
    end: usize,
    code: &str,
    message: &str,
) -> Diagnostic {
    Diagnostic {
        code: code.into(),
        severity: Severity::Error,
        message: message.into(),
        labels: vec![Label {
            span: Span {
                file,
                start: start as u32,
                end: end as u32,
            },
            message: message.into(),
        }],
        causes: vec![],
    }
}

pub(crate) fn keyword(text: &str) -> bool {
    matches!(
        text,
        "as" | "capture"
            | "eff"
            | "else"
            | "false"
            | "fn"
            | "for"
            | "halt"
            | "if"
            | "in"
            | "is"
            | "keyof"
            | "last"
            | "let"
            | "loop"
            | "match"
            | "meta"
            | "module"
            | "mut"
            | "never"
            | "next"
            | "opaque"
            | "pub"
            | "resume"
            | "return"
            | "scoped"
            | "true"
            | "type"
            | "typeof"
            | "use"
            | "var"
            | "view"
            | "where"
            | "while"
            | "with"
    )
}

pub(crate) struct Lexed {
    pub tokens: Vec<Token>,
    pub diagnostics: Vec<Diagnostic>,
    pub incomplete: bool,
}

pub(crate) fn lex(text: &str, file: FileId, base: usize) -> Lexed {
    let mut lexer = Lexer {
        text,
        file,
        base,
        pos: 0,
        diagnostics: vec![],
        regions: vec![],
        depth: 0,
        incomplete: false,
    };
    let mut tokens = vec![];
    while lexer.pos < text.len() {
        let start = lexer.pos;
        let c = lexer.character();
        let kind = if c == '\n' || c == '\r' {
            lexer.advance();
            if c == '\r' && lexer.character() == '\n' {
                lexer.advance();
            }
            SyntaxKind::Newline
        } else if c == ' ' || c == '\t' {
            while matches!(lexer.character(), ' ' | '\t') {
                lexer.advance();
            }
            SyntaxKind::Whitespace
        } else if lexer.starts("--") {
            while lexer.pos < text.len() && !matches!(lexer.character(), '\n' | '\r') {
                lexer.advance();
            }
            SyntaxKind::Comment
        } else if lexer.starts("{-") {
            lexer.comment();
            SyntaxKind::Comment
        } else if lexer.starts("b\"") {
            lexer.pos += 1;
            lexer.string(true);
            SyntaxKind::Bytes
        } else if c == '"' {
            lexer.string(false);
            SyntaxKind::String
        } else if c == '`' {
            lexer.raw();
            SyntaxKind::RawString
        } else if c.is_ascii_digit() {
            let mut float = false;
            lexer.advance();
            while lexer.pos < text.len() {
                let current = lexer.character();
                if current.is_ascii_alphanumeric() || current == '_' {
                    lexer.advance();
                } else if current == '.'
                    && lexer
                        .text
                        .as_bytes()
                        .get(lexer.pos + 1)
                        .is_some_and(u8::is_ascii_digit)
                {
                    float = true;
                    lexer.advance();
                } else if float
                    && matches!(current, '+' | '-')
                    && lexer
                        .text
                        .as_bytes()
                        .get(lexer.pos.wrapping_sub(1))
                        .is_some_and(|c| matches!(*c, b'e' | b'E'))
                {
                    lexer.advance();
                } else {
                    break;
                }
            }
            if !valid_number(&text[start..lexer.pos], float) {
                lexer.error(start, "E0111", "malformed numeric literal");
            }
            if float {
                SyntaxKind::Float
            } else {
                SyntaxKind::Integer
            }
        } else if c.is_alphabetic() || c == '_' {
            lexer.advance();
            while lexer.character().is_alphanumeric() || lexer.character() == '_' {
                lexer.advance();
            }
            let word = &text[start..lexer.pos];
            if !valid_identifier(word) {
                lexer.error(start, "E0102", "malformed identifier spelling");
            }
            if keyword(word) {
                SyntaxKind::Keyword
            } else {
                SyntaxKind::Identifier
            }
        } else {
            let operators = [
                "+%=", "-%=", "*%=", "<<=", ">>=", "..=", "^mut", "::", "->", "?.", "?[", "??",
                "|>", "!>", "/?", "%?", "+%", "-%", "*%", "<<", ">>", "<=", ">=", "==", "!=", "&&",
                "||", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "..",
            ];
            if let Some(operator) = operators.iter().find(|op| lexer.starts(op)) {
                lexer.pos += operator.len();
                SyntaxKind::Punctuation
            } else if "(){}[],:;.=+-*/%&^|!~?<>@\\".contains(c) {
                lexer.advance();
                SyntaxKind::Punctuation
            } else {
                lexer.advance();
                lexer.error(
                    start,
                    "E0105",
                    "character is not admitted by a source token",
                );
                SyntaxKind::Invalid
            }
        };
        tokens.push(Token {
            kind,
            start,
            end: lexer.pos,
        });
    }
    Lexed {
        tokens,
        diagnostics: lexer.diagnostics,
        incomplete: lexer.incomplete,
    }
}

fn digit_sequence(text: &str, radix: u32) -> bool {
    !text.is_empty()
        && !text.starts_with('_')
        && !text.ends_with('_')
        && !text.contains("__")
        && text.chars().all(|c| c == '_' || c.is_digit(radix))
}

/// Shared by tokenization and the public owned-source-AST boundary.
pub(crate) fn valid_identifier(word: &str) -> bool {
    word.as_bytes()
        .first()
        .is_some_and(|first| first.is_ascii_alphabetic() || *first == b'_')
        && word
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        && !word.contains("__")
        && (word.len() == 1 || !word.ends_with('_'))
}

fn valid_number(text: &str, float: bool) -> bool {
    let suffixes: &[&str] = if float {
        &["f32", "f64"]
    } else {
        &[
            "bigint", "int", "i16", "i32", "i64", "u16", "u32", "u64", "i8", "u8",
        ]
    };
    let mut body = text;
    if let Some(suffix) = suffixes.iter().find(|suffix| text.ends_with(**suffix)) {
        body = &text[..text.len() - suffix.len()];
        if body.ends_with('_') {
            body = &body[..body.len() - 1];
        }
    }
    if float {
        let (mantissa, exponent) = if let Some(i) = body.find(['e', 'E']) {
            (&body[..i], Some(&body[i + 1..]))
        } else {
            (body, None)
        };
        let Some((whole, fraction)) = mantissa.split_once('.') else {
            return false;
        };
        digit_sequence(whole, 10)
            && digit_sequence(fraction, 10)
            && exponent.is_none_or(|e| {
                let e = e.strip_prefix(['+', '-']).unwrap_or(e);
                !e.is_empty() && e.bytes().all(|c| c.is_ascii_digit())
            })
    } else if body.starts_with("0x") || body.starts_with("0X") {
        digit_sequence(&body[2..], 16)
    } else if body.starts_with("0o") || body.starts_with("0O") {
        digit_sequence(&body[2..], 8)
    } else if body.starts_with("0b") || body.starts_with("0B") {
        digit_sequence(&body[2..], 2)
    } else {
        digit_sequence(body, 10)
    }
}

struct Lexer<'a> {
    text: &'a str,
    file: FileId,
    base: usize,
    pos: usize,
    diagnostics: Vec<Diagnostic>,
    regions: Vec<StringRegion>,
    depth: usize,
    incomplete: bool,
}

pub(crate) struct StringRegion {
    pub owner: usize,
    pub start: usize,
    pub expression_end: usize,
    pub format: Option<usize>,
    pub end: usize,
}
pub(crate) fn string_regions(text: &str) -> Vec<StringRegion> {
    let mut lexer = Lexer {
        text,
        file: FileId(0),
        base: 0,
        pos: 0,
        diagnostics: vec![],
        regions: vec![],
        depth: 0,
        incomplete: false,
    };
    lexer.string(false);
    let mut regions: Vec<_> = lexer
        .regions
        .into_iter()
        .filter(|region| region.owner == 0)
        .collect();
    regions.sort_by_key(|region| region.start);
    regions
}

impl Lexer<'_> {
    fn character(&self) -> char {
        self.text[self.pos..].chars().next().unwrap_or('\0')
    }
    fn advance(&mut self) {
        if self.pos < self.text.len() {
            self.pos += self.character().len_utf8();
        }
    }
    fn starts(&self, text: &str) -> bool {
        self.text[self.pos..].starts_with(text)
    }
    fn error(&mut self, start: usize, code: &str, message: &str) {
        if self.incomplete {
            return;
        }
        self.diagnostics.push(diagnostic(
            self.file,
            self.base + start,
            self.base + self.pos,
            code,
            message,
        ));
    }
    fn comment(&mut self) {
        let start = self.pos;
        self.pos += 2;
        let mut depth = 1;
        while self.pos < self.text.len() && depth > 0 {
            if self.starts("{-") {
                depth += 1;
                self.pos += 2;
            } else if self.starts("-}") {
                depth -= 1;
                self.pos += 2;
            } else {
                self.advance();
            }
        }
        if depth > 0 {
            self.error(start, "E0106", "unterminated nested block comment");
        }
    }
    fn raw(&mut self) {
        let start = self.pos;
        self.advance();
        while self.pos < self.text.len() && self.character() != '`' {
            self.advance();
        }
        if self.pos == self.text.len() {
            self.error(start, "E0107", "unterminated raw string");
        } else {
            self.advance();
        }
    }
    fn string(&mut self, bytes: bool) {
        self.depth += 1;
        if self.depth > 64 {
            self.incomplete = true;
            self.pos = self.text.len();
            self.depth -= 1;
            return;
        }
        self.string_inner(bytes);
        self.depth -= 1;
    }
    fn string_inner(&mut self, bytes: bool) {
        let start = self.pos;
        self.advance();
        while self.pos < self.text.len() {
            match self.character() {
                '"' => {
                    self.advance();
                    return;
                }
                '\\' => {
                    let escape = self.pos;
                    self.advance();
                    if bytes {
                        if self.character() == 'x' {
                            self.advance();
                            for _ in 0..2 {
                                if self.character().is_ascii_hexdigit() {
                                    self.advance();
                                } else {
                                    self.error(
                                        escape,
                                        "E0110",
                                        "byte escape requires exactly two hexadecimal digits",
                                    );
                                    break;
                                }
                            }
                        } else {
                            self.advance();
                            self.error(
                                escape,
                                "E0110",
                                "only hexadecimal escapes are admitted in byte strings",
                            );
                        }
                    } else if matches!(self.character(), 'n' | 'r' | 't' | '0' | '\\' | '"') {
                        self.advance();
                    } else if self.character() == 'u' {
                        self.advance();
                        if self.character() != '{' {
                            self.error(escape, "E0108", "Unicode escape requires braces");
                            continue;
                        }
                        self.advance();
                        let digits = self.pos;
                        while self.character().is_ascii_hexdigit() {
                            self.advance();
                        }
                        let value = u32::from_str_radix(&self.text[digits..self.pos], 16);
                        if self.character() != '}' || digits == self.pos {
                            self.error(escape, "E0108", "malformed Unicode escape");
                        } else {
                            self.advance();
                            if value.ok().and_then(char::from_u32).is_none() {
                                self.error(escape, "E0109", "Unicode escape is not a scalar value");
                            }
                        }
                    } else {
                        self.advance();
                        self.error(escape, "E0108", "unsupported string escape");
                    }
                }
                '{' if !bytes => {
                    if self.starts("{{") {
                        self.pos += 2;
                    } else {
                        self.interpolation(start);
                    }
                }
                '}' if !bytes => {
                    if self.starts("}}") {
                        self.pos += 2;
                    } else {
                        let brace = self.pos;
                        self.advance();
                        self.error(brace, "E0112", "unmatched interpolation closing brace");
                    }
                }
                c if bytes && !c.is_ascii() => {
                    let bad = self.pos;
                    self.advance();
                    self.error(bad, "E0110", "byte string contains a non-ASCII character");
                }
                _ => self.advance(),
            }
        }
        self.error(start, "E0107", "unterminated string literal");
    }
    fn interpolation(&mut self, owner: usize) {
        let start = self.pos;
        self.advance();
        let content = self.pos;
        let mut braces = 1;
        let mut parens = 0usize;
        let mut brackets = 0usize;
        let mut format = None;
        while self.pos < self.text.len() {
            if self.starts("{-") {
                self.comment();
                continue;
            }
            if self.starts("--") {
                while self.pos < self.text.len() && !matches!(self.character(), '\n' | '\r') {
                    self.advance();
                }
                continue;
            }
            match self.character() {
                '"' => self.string(false),
                '`' => self.raw(),
                '{' => {
                    braces += 1;
                    self.advance();
                }
                '}' => {
                    braces -= 1;
                    if braces == 0 {
                        let end = format.unwrap_or(self.pos);
                        if self.text[content..end].trim().is_empty() {
                            self.error(start, "E0112", "interpolation requires an expression");
                        }
                        if let Some(colon) = format
                            && !valid_format(&self.text[colon + 1..self.pos])
                        {
                            self.error(start, "E0112", "malformed interpolation format");
                        }
                        self.regions.push(StringRegion {
                            owner,
                            start,
                            expression_end: end,
                            format,
                            end: self.pos,
                        });
                        self.advance();
                        return;
                    }
                    self.advance();
                }
                '(' => {
                    parens += 1;
                    self.advance();
                }
                ')' => {
                    parens = parens.saturating_sub(1);
                    self.advance();
                }
                '[' => {
                    brackets += 1;
                    self.advance();
                }
                ']' => {
                    brackets = brackets.saturating_sub(1);
                    self.advance();
                }
                ':' if braces == 1 && parens == 0 && brackets == 0 && !self.starts("::") => {
                    format = Some(self.pos);
                    self.advance();
                }
                ':' if self.starts("::") => {
                    self.pos += 2;
                }
                _ => self.advance(),
            }
        }
        self.error(start, "E0112", "interpolation lacks its closing brace");
    }
}

fn valid_format(text: &str) -> bool {
    ril_text_format::FormatSpec::parse(text, 64).is_ok()
}
