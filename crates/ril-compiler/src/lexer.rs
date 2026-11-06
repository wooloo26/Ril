use crate::SyntaxKind;
use crate::{
    diagnostic::{Diagnostic, Label, Severity},
    source::{FileId, Span},
    text::FormatSpec,
};
use std::collections::BTreeMap;

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
        "as" | "eff"
            | "else"
            | "false"
            | "fn"
            | "for"
            | "halt"
            | "if"
            | "is"
            | "keyof"
            | "last"
            | "let"
            | "loop"
            | "match"
            | "meta"
            | "modeof"
            | "new"
            | "ref"
            | "sub"
            | "mut"
            | "next"
            | "pub"
            | "resume"
            | "return"
            | "true"
            | "type"
            | "typeof"
            | "use"
            | "var"
            | "where"
            | "while"
            | "with"
    )
}

pub(crate) fn primitive(text: &str) -> bool {
    matches!(
        text,
        "never"
            | "bool"
            | "str"
            | "bytes"
            | "bigint"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "f32"
            | "f64"
    )
}

pub(crate) struct Lexed {
    pub tokens: Vec<Token>,
    pub interpolations: BTreeMap<usize, Vec<StringRegion>>,
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
        interpolations: BTreeMap::new(),
        depth: 0,
        incomplete: false,
    };
    let mut tokens = vec![];
    let mut after_dot = false;
    while lexer.pos < text.len() {
        let token = lexer.token(after_dot);
        if !token.is_trivia() {
            after_dot = matches!(&text[token.start..token.end], "." | "?.");
        }
        tokens.push(token);
    }
    Lexed {
        tokens,
        interpolations: lexer.interpolations,
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
            "bigint", "i16", "i32", "i64", "u16", "u32", "u64", "i8", "u8",
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
    interpolations: BTreeMap<usize, Vec<StringRegion>>,
    depth: usize,
    incomplete: bool,
}

/// The raw region lives in the enclosing source. Tokens cover the embedded
/// expression and any suffix that the lexer could not separate on its own.
pub(crate) struct StringRegion {
    pub start: usize,
    pub end: usize,
    pub format: Option<usize>,
    pub tokens: Vec<Token>,
    pub diagnostics: Vec<Diagnostic>,
}

impl Token {
    pub(crate) fn is_trivia(self) -> bool {
        matches!(
            self.kind,
            SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::Comment
        )
    }
}

impl Lexer<'_> {
    fn token(&mut self, after_dot: bool) -> Token {
        let start = self.pos;
        let c = self.character();
        let kind = if c == '\n' || c == '\r' {
            self.advance();
            if c == '\r' && self.character() == '\n' {
                self.advance();
            }
            SyntaxKind::Newline
        } else if c == ' ' || c == '\t' {
            while matches!(self.character(), ' ' | '\t') {
                self.advance();
            }
            SyntaxKind::Whitespace
        } else if self.starts("--") {
            while self.pos < self.text.len() && !matches!(self.character(), '\n' | '\r') {
                self.advance();
            }
            SyntaxKind::Comment
        } else if self.starts("{-") {
            self.comment();
            SyntaxKind::Comment
        } else if self.starts("b\"") {
            self.pos += 1;
            self.string(true);
            SyntaxKind::Bytes
        } else if c == '"' {
            self.string(false);
            SyntaxKind::String
        } else if c == '`' {
            self.raw();
            SyntaxKind::RawString
        } else if c.is_ascii_digit() && after_dot {
            while self.character().is_ascii_digit() {
                self.advance();
            }
            SyntaxKind::Integer
        } else if c.is_ascii_digit() {
            let mut float = false;
            self.advance();
            while self.pos < self.text.len() {
                let current = self.character();
                if current.is_ascii_alphanumeric() || current == '_' {
                    self.advance();
                } else if current == '.'
                    && self
                        .text
                        .as_bytes()
                        .get(self.pos + 1)
                        .is_some_and(u8::is_ascii_digit)
                {
                    float = true;
                    self.advance();
                } else if float
                    && matches!(current, '+' | '-')
                    && self
                        .text
                        .as_bytes()
                        .get(self.pos.wrapping_sub(1))
                        .is_some_and(|c| matches!(*c, b'e' | b'E'))
                {
                    self.advance();
                } else {
                    break;
                }
            }
            if !valid_number(&self.text[start..self.pos], float) {
                self.error(start, "E0111", "malformed numeric literal");
            }
            if float {
                SyntaxKind::Float
            } else {
                SyntaxKind::Integer
            }
        } else if c.is_ascii_alphabetic() || c == '_' {
            self.advance();
            while self.character().is_ascii_alphanumeric() || self.character() == '_' {
                self.advance();
            }
            let word = &self.text[start..self.pos];
            if !valid_identifier(word) {
                self.error(start, "E0102", "malformed identifier spelling");
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
            if let Some(operator) = operators.iter().find(|op| {
                self.starts(op)
                    && (**op != "^mut"
                        || !self
                            .text
                            .as_bytes()
                            .get(self.pos + 4)
                            .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_'))
            }) {
                self.pos += operator.len();
                SyntaxKind::Punctuation
            } else if "(){}[],:;.=+-*/%&^|!~?<>@\\".contains(c) {
                self.advance();
                SyntaxKind::Punctuation
            } else {
                self.advance();
                self.error(
                    start,
                    "E0105",
                    "character is not admitted by a source token",
                );
                SyntaxKind::Invalid
            }
        };
        Token {
            kind,
            start,
            end: self.pos,
        }
    }

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
                        if !self.interpolation(start) && self.pos == self.text.len() {
                            return;
                        }
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
    fn interpolation(&mut self, owner: usize) -> bool {
        let start = self.pos;
        self.advance();
        let diagnostics_start = self.diagnostics.len();
        let mut tokens = vec![];
        let mut braces = 0usize;
        let mut parens = 0usize;
        let mut brackets = 0usize;
        let mut has_lambda = false;
        let mut after_dot = false;
        let mut after_value = false;
        let mut format = None;
        while self.pos < self.text.len() {
            if braces == 0 && self.starts("}") {
                let end = self.pos;
                let diagnostics = self.diagnostics.split_off(diagnostics_start);
                self.interpolations
                    .entry(owner)
                    .or_default()
                    .push(StringRegion {
                        start,
                        end,
                        format,
                        tokens,
                        diagnostics,
                    });
                self.advance();
                return true;
            }
            let outermost = braces == 0 && parens == 0 && brackets == 0;
            if outermost && self.starts("\"") && after_value {
                break;
            }
            if outermost
                && self.starts(":")
                && let Some(end) = self.format_candidate(has_lambda)
            {
                format = Some(self.pos);
                self.pos = end;
                if self.starts("}") {
                    continue;
                }
                break;
            }

            let token = self.token(after_dot);
            let text = &self.text[token.start..token.end];
            match text {
                "{" => braces += 1,
                "}" => braces -= 1,
                "(" => parens += 1,
                ")" => parens = parens.saturating_sub(1),
                "[" | "?[" => brackets += 1,
                "]" => brackets = brackets.saturating_sub(1),
                "\\" if outermost => has_lambda = true,
                _ => {}
            }
            if !token.is_trivia() {
                after_dot = matches!(text, "." | "?.");
                after_value = matches!(
                    token.kind,
                    SyntaxKind::Identifier
                        | SyntaxKind::Integer
                        | SyntaxKind::Float
                        | SyntaxKind::String
                        | SyntaxKind::RawString
                        | SyntaxKind::Bytes
                ) || matches!(
                    text,
                    ")" | "]" | "}" | "?" | "true" | "false" | "last" | "next" | "return"
                );
            }
            tokens.push(token);
        }
        self.error(start, "E0112", "interpolation lacks its closing brace");
        false
    }

    fn format_candidate(&self, has_lambda: bool) -> Option<usize> {
        let start = self.pos + 1;
        let suffix = &self.text[start..];
        let explicit_fill = suffix
            .as_bytes()
            .get(1)
            .is_some_and(|byte| matches!(byte, b'<' | b'^' | b'>'));
        let qualified = suffix.starts_with(':');
        if qualified && !explicit_fill {
            return None;
        }
        let quote_fill = suffix.starts_with('"') && explicit_fill;
        let search = start + usize::from(quote_fill);
        let end = self.text[search..]
            .find(['}', '"'])
            .map_or(self.text.len(), |offset| search + offset);
        // A single colon outside delimiters can be an anonymous parameter
        // annotation. Leave ambiguous suffixes in that case to the parser.
        (qualified
            || !has_lambda
            || self.text[end..].starts_with('}')
                && FormatSpec::parse(&self.text[start..end]).is_some())
        .then_some(end)
    }
}
