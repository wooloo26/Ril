//! Lossless monotonic comment store for `ril fmt`.
//!
//! Guarantees an exact bijection between input `--` comments and emitted `--` comments
//! (`debug_assert_eq!(cursor, comments.len())`), preserving comment text verbatim.

use ril_source::span::{SourceFile, Span};

use crate::{
    directive::is_lint_directive_comment,
    fmt::doc::{DocArena, DocId},
    lexer::{Kind, Token, Trivia, TriviaKind},
};

#[derive(Clone, Copy, Debug)]
pub(super) struct Comment<'src> {
    pub(super) span: Span,
    pub(super) text: &'src str,
    pub(super) line: usize,
    pub(super) is_trailing: bool,
    pub(super) is_lint_directive: bool,
    pub(super) blank_before: bool,
    pub(super) blank_after: bool,
}

pub(super) struct CommentStore<'src> {
    comments: Vec<Comment<'src>>,
    cursor: usize,
}

impl<'src> CommentStore<'src> {
    pub(super) fn build(source: &'src SourceFile, tokens: &[Token], trivia: &[Trivia]) -> Self {
        // Precompute the set of 1-based lines that contain at least one non-newline code token.
        let mut code_lines = Vec::new();
        for tok in tokens {
            if matches!(tok.kind, Kind::Newline | Kind::Eof) {
                continue;
            }
            if let Some(loc) = source.location(tok.span.start)
                && code_lines.last() != Some(&loc.line)
            {
                code_lines.push(loc.line);
            }
            if let Some(end_loc) =
                source.location(tok.span.end.saturating_sub(1).max(tok.span.start))
                && code_lines.last() != Some(&end_loc.line)
            {
                code_lines.push(end_loc.line);
            }
        }
        code_lines.sort_unstable();
        code_lines.dedup();

        let src = source.text();
        let mut comments = Vec::new();
        for triv in trivia {
            if triv.kind != TriviaKind::LineComment {
                continue;
            }
            let raw = src
                .get(triv.span.start..triv.span.end)
                .unwrap_or_default()
                .trim_end_matches([' ', '\t', '\r']);
            let line = source.location(triv.span.start).map_or(1, |loc| loc.line);
            let is_trailing = code_lines.binary_search(&line).is_ok();
            let is_lint_directive = is_lint_directive_comment(raw.trim_start());
            let blank_before = has_blank_line_before(src, triv.span.start);
            let blank_after = has_blank_line_after(src, triv.span.end);
            comments.push(Comment {
                span: triv.span,
                text: raw,
                line,
                is_trailing,
                is_lint_directive,
                blank_before,
                blank_after,
            });
        }

        Self {
            comments,
            cursor: 0,
        }
    }

    pub(super) fn peek(&self) -> Option<Comment<'src>> {
        self.comments.get(self.cursor).copied()
    }

    pub(super) fn has_comment_in(&self, start_byte: usize, end_byte: usize) -> bool {
        let mut i = self.cursor;
        while let Some(c) = self.comments.get(i) {
            if c.span.start >= end_byte {
                return false;
            }
            if c.span.start >= start_byte {
                return true;
            }
            i += 1;
        }
        false
    }

    /// Consumes and formats all leading (non-trailing) comments before `before_byte`.
    /// Returns `(doc, had_comments)`.
    pub(super) fn emit_leading(
        &mut self,
        arena: &mut DocArena<'src>,
        before_byte: usize,
        allow_initial_blank: bool,
    ) -> (DocId, bool) {
        let mut parts = Vec::new();
        let mut count = 0usize;
        let mut last_blank_after = false;

        while let Some(c) = self.peek() {
            if c.span.start >= before_byte {
                break;
            }
            self.cursor += 1;
            if count > 0 {
                if c.blank_before {
                    parts.push(arena.blank_line());
                } else {
                    parts.push(arena.hard_line());
                }
            } else if allow_initial_blank && c.blank_before {
                parts.push(arena.blank_line());
            }
            parts.push(arena.text(c.text));
            last_blank_after = c.blank_after;
            count += 1;
        }

        if count == 0 {
            return (arena.empty(), false);
        }
        if last_blank_after {
            parts.push(arena.blank_line());
        } else {
            parts.push(arena.hard_line());
        }
        (arena.concat(&parts), true)
    }

    /// If the next unconsumed comment is a trailing inline comment on `node_end_line`
    /// (and starts before `limit_byte`), consumes it and returns `LineSuffix(" " + comment)`.
    pub(super) fn emit_trailing_on_line(
        &mut self,
        arena: &mut DocArena<'src>,
        node_end_line: usize,
        limit_byte: usize,
    ) -> Option<DocId> {
        let c = self.peek()?;
        if !c.is_trailing || c.line != node_end_line || c.span.start >= limit_byte {
            return None;
        }
        self.cursor += 1;
        let space = arena.text(" ");
        let body = arena.text(c.text);
        let merged = arena.concat(&[space, body]);
        Some(arena.line_suffix(merged))
    }

    /// If the node's own line ends with a trailing `-- ril:` lint directive AND the node will wrap
    /// across multiple lines, hoists the directive cleanly above the node so it never detaches.
    pub(super) fn take_trailing_directive_on_line(
        &mut self,
        node_end_line: usize,
        limit_byte: usize,
    ) -> Option<Comment<'src>> {
        let c = self.peek()?;
        if c.is_trailing
            && c.is_lint_directive
            && c.line == node_end_line
            && c.span.start < limit_byte
        {
            self.cursor += 1;
            return Some(c);
        }
        None
    }

    /// Consumes all remaining comments before `before_byte` (e.g. dangling comments before `}`, `]`, `)`, or EOF).
    pub(super) fn emit_dangling(
        &mut self,
        arena: &mut DocArena<'src>,
        before_byte: usize,
        has_preceding_items: bool,
    ) -> (DocId, bool) {
        let mut parts = Vec::new();
        let mut count = 0usize;

        while let Some(c) = self.peek() {
            if c.span.start >= before_byte {
                break;
            }
            self.cursor += 1;
            if count == 0 {
                if has_preceding_items {
                    if c.blank_before {
                        parts.push(arena.blank_line());
                    } else {
                        parts.push(arena.hard_line());
                    }
                }
            } else if c.blank_before {
                parts.push(arena.blank_line());
            } else {
                parts.push(arena.hard_line());
            }
            parts.push(arena.text(c.text));
            count += 1;
        }

        if count == 0 {
            return (arena.empty(), false);
        }
        (arena.concat(&parts), true)
    }

    pub(super) fn assert_exhausted(&self) {
        debug_assert_eq!(
            self.cursor,
            self.comments.len(),
            "formatter failed to emit all comments ({} of {})",
            self.cursor,
            self.comments.len()
        );
    }
}

fn has_blank_line_before(src: &str, start: usize) -> bool {
    let prefix = src.get(..start).unwrap_or("");
    let mut nl = 0usize;
    for ch in prefix.chars().rev() {
        if ch == '\n' {
            nl += 1;
            if nl >= 2 {
                return true;
            }
        } else if ch != ' ' && ch != '\t' && ch != '\r' {
            return false;
        }
    }
    false
}

fn has_blank_line_after(src: &str, end: usize) -> bool {
    let suffix = src.get(end..).unwrap_or("");
    let mut nl = 0usize;
    for ch in suffix.chars() {
        if ch == '\n' {
            nl += 1;
            if nl >= 2 {
                return true;
            }
        } else if ch != ' ' && ch != '\t' && ch != '\r' {
            return false;
        }
    }
    false
}
