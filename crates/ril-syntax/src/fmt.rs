//! Canonical comment-preserving, idempotent Ril source formatter (`ril fmt`).

use ril_source::{diag::Diagnostic, span::SourceFile};

use crate::{
    cst::{CstElement, CstFile},
    lexer::{self, Kind, Token, TriviaKind, Word},
    parser::{self, FileKind},
};

/// Formats a Ril source file canonically while preserving all comments, strings,
/// and exact Ril tight-left token semantics (`Ok(x)`, `User.{ ... }`, `a::b`, etc.).
///
/// Refuses to format files with lexer or parser errors, returning those diagnostics.
pub fn format_source(source: &SourceFile, kind: FileKind) -> Result<String, Vec<Diagnostic>> {
    let lexed = lexer::lex_with_recovery(source);
    if !lexed.diagnostics.is_empty() {
        return Err(lexed.diagnostics);
    }
    let parsed = parser::parse_with_recovery(source, &lexed.tokens, kind);
    if !parsed.diagnostics.is_empty() {
        return Err(parsed.diagnostics);
    }
    let cst = CstFile::lex(source);
    Ok(format_cst(source, &cst))
}

#[derive(Clone, Copy)]
enum Item<'a> {
    Tok(Token, &'a str),
    LineComment(&'a str),
    BlockComment(&'a str),
}

fn format_cst(source: &SourceFile, cst: &CstFile) -> String {
    // Group concrete elements into logical lines (split on `Kind::Newline`),
    // stripping pure whitespace trivia while keeping all tokens and comments.
    let mut lines: Vec<Vec<Item<'_>>> = vec![Vec::new()];
    for &elem in &cst.elements {
        match elem {
            CstElement::Token(tok) if tok.kind == Kind::Eof => {}
            CstElement::Token(tok) if tok.kind == Kind::Newline => {
                lines.push(Vec::new());
            }
            CstElement::Token(tok) => {
                if let Some(line) = lines.last_mut() {
                    line.push(Item::Tok(tok, tok.text(source)));
                }
            }
            CstElement::Trivia(triv) => match triv.kind {
                TriviaKind::Whitespace => {}
                TriviaKind::LineComment => {
                    if let Some(line) = lines.last_mut() {
                        line.push(Item::LineComment(
                            source
                                .text()
                                .get(triv.span.start..triv.span.end)
                                .unwrap_or_default()
                                .trim_end(),
                        ));
                    }
                }
                TriviaKind::BlockComment => {
                    if let Some(line) = lines.last_mut() {
                        line.push(Item::BlockComment(
                            source
                                .text()
                                .get(triv.span.start..triv.span.end)
                                .unwrap_or_default(),
                        ));
                    }
                }
            },
        }
    }

    let mut out = String::with_capacity(source.text().len());
    let mut indent = 0usize;
    let mut blank_run = 0usize;
    let mut emitted_any = false;

    for line in &lines {
        if line.is_empty() {
            if emitted_any {
                blank_run += 1;
            }
            continue;
        }
        if emitted_any {
            if blank_run > 0 {
                out.push('\n');
            }
            out.push('\n');
        }
        blank_run = 0;
        emitted_any = true;

        // Leading closing delimiters dedent the current line before rendering.
        let mut leading_closes = 0usize;
        for item in line {
            if let Item::Tok(tok, text) = item
                && tok.kind == Kind::Punctuation
                && matches!(*text, "}" | "]" | ")")
            {
                leading_closes += 1;
            } else {
                break;
            }
        }
        let line_indent = indent.saturating_sub(leading_closes);
        for _ in 0..line_indent {
            out.push_str("    ");
        }

        render_line(line, &mut out);

        // Update running block/bracket indentation for subsequent lines.
        for item in line {
            if let Item::Tok(tok, text) = item
                && tok.kind == Kind::Punctuation
            {
                match *text {
                    "{" | ".{" | "[" | "(" => indent += 1,
                    "}" | "]" | ")" => indent = indent.saturating_sub(1),
                    _ => {}
                }
            }
        }
    }

    if !out.is_empty() {
        out.push('\n');
    }
    out
}

fn render_line(items: &[Item<'_>], out: &mut String) {
    let mut prev: Option<Item<'_>> = None;
    for &item in items {
        if let Some(before) = prev
            && needs_space(before, item)
        {
            out.push(' ');
        }
        match item {
            Item::Tok(_, text) | Item::LineComment(text) | Item::BlockComment(text) => {
                out.push_str(text);
            }
        }
        prev = Some(item);
    }
}

fn is_string_left_inside(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::StringStart | Kind::StringChunk | Kind::InterpolationStart | Kind::InterpolationEnd
    )
}

fn is_string_right_inside(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::StringChunk | Kind::StringEnd | Kind::InterpolationStart | Kind::InterpolationEnd
    )
}

fn needs_space(left: Item<'_>, right: Item<'_>) -> bool {
    match (left, right) {
        (_, Item::LineComment(_) | Item::BlockComment(_)) | (Item::BlockComment(_), _) => true,
        (Item::LineComment(_), _) => false,
        (Item::Tok(lt, ltext), Item::Tok(rt, rtext)) => {
            if is_string_left_inside(lt.kind) || is_string_right_inside(rt.kind) {
                return false;
            }
            // Never split Ril's syntactically tight-left constructs:
            // `Ok(42)`, `User.{ ... }`, `arr[0]`, `x?`, `a.b`, `a::b`, `x: T`, `a, b`, `a; b`.
            if rt.tight_left && matches!(rtext, "(" | ".{" | "[" | "?" | "?.") {
                return false;
            }
            if matches!(rtext, "," | ";" | ":" | ")" | "]" | "::" | "." | "?.") {
                return false;
            }
            if rtext == ".." && !matches!(ltext, "{" | ".{") {
                return false;
            }
            if matches!(
                ltext,
                "(" | "[" | "::" | "." | "?." | "\\" | "^" | "!" | "!<" | "~" | ".."
            ) {
                return false;
            }
            if ltext == "@" && rtext != "->" {
                return false;
            }
            // Keep array type prefix `[]T` tight when originally tight.
            if ltext == "]" && rt.tight_left {
                return false;
            }
            // Preserve tight `<T>` / `!<T, E>` / `!<(), E<T>>` generic brackets when originally tight.
            if (rtext == "<" || ltext == "<" || rtext == ">" || rtext == ">>") && rt.tight_left {
                return false;
            }
            // Keep `&mut`, `&^mut`, `&return`, `&up`, `&capture` tight when originally tight.
            if ltext == "&" && rt.tight_left {
                return false;
            }
            // Keep unary `-x` tight when originally tight.
            if ltext == "-" && rt.tight_left {
                return false;
            }
            // Keep path imports `use pkg/math/util` tight around `/`.
            if (ltext == "/" || rtext == "/") && rt.tight_left {
                return false;
            }
            // Empty braces `{}` / `.{}` stay tight.
            if matches!(ltext, "{" | ".{") && rtext == "}" {
                return false;
            }
            // Prefix `?T` optional type stays tight when `?` precedes a type or word tightly.
            if ltext == "?" && rt.tight_left {
                return false;
            }
            // Space after `:` or `,` or `;` or `{` or `.{`, and before `{` or `}`.
            if matches!(ltext, ":" | "," | ";" | "{" | ".{") || matches!(rtext, "{" | "}") {
                return true;
            }
            // Space around binary operators, arrows, keywords, and words.
            if matches!(
                ltext,
                "=" | "=="
                    | "!="
                    | "<="
                    | ">="
                    | "<"
                    | ">"
                    | "+"
                    | "-"
                    | "*"
                    | "/"
                    | "%"
                    | "&&"
                    | "||"
                    | "->"
                    | "=>"
                    | "|>"
                    | "|"
                    | "+="
                    | "-="
                    | "*="
                    | "/="
                    | "%="
            ) || matches!(
                rtext,
                "=" | "=="
                    | "!="
                    | "<="
                    | ">="
                    | "<"
                    | ">"
                    | "+"
                    | "-"
                    | "*"
                    | "/"
                    | "%"
                    | "&&"
                    | "||"
                    | "->"
                    | "=>"
                    | "|>"
                    | "|"
                    | "+="
                    | "-="
                    | "*="
                    | "/="
                    | "%="
            ) {
                return true;
            }
            // Space between adjacent words/literals (e.g. `fn main`, `let mut x`, `pub type`).
            matches!(
                lt.kind,
                Kind::Word(
                    Word::Keyword
                        | Word::Value
                        | Word::Pascal
                        | Word::Constant
                        | Word::Primitive
                        | Word::Wildcard
                )
            ) || !rt.tight_left
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use ril_source::span::{FileId, SourceFile};

    use super::format_source;
    use crate::parser::FileKind;

    #[test]
    fn format_preserves_spaces_before_and_after_string_literals() {
        let input = concat!(
            "fn demo(msg: str = \"hello\") -> str {\n",
            "    let a = \"x\"\n",
            "    if a == \"x\" {\n",
            "        let pair = (\"a\", \"b\")\n",
            "        let _ = pair\n",
            "        \"{msg}:ok\"\n",
            "    } else {\n",
            "        \"fallback\"\n",
            "    }\n",
            "}\n",
        );
        let source = SourceFile::from_bytes(
            FileId(1),
            PathBuf::from("pkg/fmt_strings.ril"),
            input.as_bytes(),
        )
        .expect("valid utf-8");
        let formatted = format_source(&source, FileKind::Module).expect("formats cleanly");
        assert_eq!(formatted, input);
    }

    #[test]
    fn format_preserves_tight_nominal_wrap_syntax() {
        let input = concat!(
            "use Option::(Some, None)\n",
            "type UserId(int)\n",
            "type Point(int, int)\n",
            "type User(.{ id: int })\n",
            "opaque type Conn<S>(.{ fd: int })\n",
            "fn demo() -> () {\n",
            "    let id = UserId::(42)\n",
            "    let pt = Point::((1, 2))\n",
            "    let u = User::(.{ id: 1 })\n",
            "    let c = Conn<int>::(.{ fd: 3 })\n",
            "    let User::(.{ id: n }) = u\n",
            "    let _ = (id, pt, c, n)\n",
            "}\n",
        );
        let source = SourceFile::from_bytes(
            FileId(2),
            PathBuf::from("pkg/fmt_wrap.ril"),
            input.as_bytes(),
        )
        .expect("valid utf-8");
        let formatted = format_source(&source, FileKind::Module).expect("formats cleanly");
        assert_eq!(formatted, input);
    }
}
