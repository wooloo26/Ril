//! Lossless token index for recovering purely syntactic surface hints omitted by `Ast`.

use ril_source::span::{SourceFile, Span};

use crate::{
    lexer::{Kind, Token},
    syntax::ExprId,
};

pub(super) struct TokenIndex<'src> {
    source: &'src SourceFile,
    code_tokens: Vec<Token>,
    starts: Vec<usize>,
    matching_close: Vec<Option<usize>>,
}

impl<'src> TokenIndex<'src> {
    pub(super) fn build(source: &'src SourceFile, tokens: &[Token]) -> Self {
        let code_tokens: Vec<Token> = tokens
            .iter()
            .copied()
            .filter(|t| !matches!(t.kind, Kind::Newline | Kind::Eof))
            .collect();
        let starts: Vec<usize> = code_tokens.iter().map(|t| t.span.start).collect();
        let mut matching_close = vec![None; code_tokens.len()];

        // Match standard bracket pairs `( )`, `[ ]`, `{ }`, `.{ }`.
        let mut stack: Vec<(usize, &'static str)> = Vec::new();
        for (idx, tok) in code_tokens.iter().enumerate() {
            if tok.kind != Kind::Punctuation {
                continue;
            }
            match tok.text(source) {
                "(" => stack.push((idx, ")")),
                "[" => stack.push((idx, "]")),
                "{" | ".{" => stack.push((idx, "}")),
                close @ (")" | "]" | "}") => {
                    if let Some((open_idx, expected)) = stack.last().copied()
                        && expected == close
                    {
                        stack.pop();
                        if let Some(slot) = matching_close.get_mut(open_idx) {
                            *slot = Some(idx);
                        }
                    }
                }
                _ => {}
            }
        }

        Self {
            source,
            code_tokens,
            starts,
            matching_close,
        }
    }

    pub(super) fn text(&self, idx: usize) -> &'src str {
        self.code_tokens
            .get(idx)
            .map_or("", |t| t.text(self.source))
    }

    /// Index of the first code token starting at or after `byte_offset`.
    pub(super) fn first_at_or_after(&self, byte_offset: usize) -> usize {
        self.starts.partition_point(|&s| s < byte_offset)
    }

    /// Index of the last code token ending at or before `byte_end`.
    pub(super) fn last_ending_at_or_before(&self, byte_end: usize) -> Option<usize> {
        let pos = self.starts.partition_point(|&s| s < byte_end);
        if pos == 0 {
            return None;
        }
        let mut idx = pos - 1;
        loop {
            if let Some(tok) = self.code_tokens.get(idx)
                && tok.span.end <= byte_end
            {
                return Some(idx);
            }
            if idx == 0 {
                return None;
            }
            idx -= 1;
        }
    }

    /// Exact number of redundant outer parenthesizations wrapping `span`.
    /// When `self_is_parens` is true (e.g. `Unit`, `Tuple`, `TupleAny`), the innermost `(...)`
    /// belongs to the node itself and is not counted.
    pub(super) fn paren_depth(&self, span: Span, self_is_parens: bool) -> usize {
        let mut lo = self.first_at_or_after(span.start);
        let Some(mut hi) = self.last_ending_at_or_before(span.end) else {
            return 0;
        };
        let mut depth = 0usize;
        while lo < hi
            && self.text(lo) == "("
            && self.matching_close.get(lo).copied().flatten() == Some(hi)
        {
            depth += 1;
            lo += 1;
            hi -= 1;
        }
        if self_is_parens {
            depth.saturating_sub(1)
        } else {
            depth
        }
    }

    /// Returns true if the delimited list starting at/after `search_start` (with opener `open_str`)
    /// and ending at/before `limit_end` has a trailing comma before its closing delimiter.
    pub(super) fn has_trailing_comma_in(
        &self,
        search_start: usize,
        limit_end: usize,
        open_str: &str,
    ) -> bool {
        let mut idx = self.first_at_or_after(search_start);
        while let Some(tok) = self.code_tokens.get(idx) {
            if tok.span.start >= limit_end {
                return false;
            }
            if tok.kind == Kind::Punctuation && tok.text(self.source) == open_str {
                if matches!(open_str, "<" | "!<") {
                    return self.angle_has_trailing_comma(idx, limit_end);
                }
                if let Some(close_idx) = self.matching_close.get(idx).copied().flatten() {
                    return close_idx > idx + 1 && self.text(close_idx - 1) == ",";
                }
                return false;
            }
            idx += 1;
        }
        false
    }

    /// Checks whether a `<...>` or `!<...>` list starting at `open_idx` ends with `,` before `>`.
    fn angle_has_trailing_comma(&self, open_idx: usize, limit_end: usize) -> bool {
        let mut depth = 0usize;
        let mut idx = open_idx;
        let mut prev_comma = false;
        while let Some(tok) = self.code_tokens.get(idx) {
            if tok.span.start > limit_end {
                break;
            }
            let t = tok.text(self.source);
            match t {
                "<" | "!<" => {
                    depth += 1;
                    prev_comma = false;
                }
                ">" | ">>" | ">=" | ">>=" if depth > 0 => {
                    let count = t.bytes().take_while(|&b| b == b'>').count();
                    if count >= depth {
                        return prev_comma;
                    }
                    depth -= count;
                    prev_comma = false;
                }
                "," => prev_comma = depth == 1,
                _ => prev_comma = false,
            }
            idx += 1;
        }
        false
    }

    /// Returns the `(open_byte, close_byte)` of the first bracket `open_str` at or after `start`.
    pub(super) fn find_bracket_span(
        &self,
        search_start: usize,
        limit_end: usize,
        open_str: &str,
    ) -> Option<(usize, usize)> {
        let mut idx = self.first_at_or_after(search_start);
        while let Some(tok) = self.code_tokens.get(idx) {
            if tok.span.start >= limit_end {
                return None;
            }
            if tok.kind == Kind::Punctuation && tok.text(self.source) == open_str {
                let close_idx = self.matching_close.get(idx).copied().flatten()?;
                let close_tok = self.code_tokens.get(close_idx)?;
                return Some((tok.span.start, close_tok.span.end));
            }
            idx += 1;
        }
        None
    }

    pub(super) fn has_newline_in_span(&self, span: Span) -> bool {
        self.source
            .text()
            .get(span.start..span.end)
            .is_some_and(|s| s.contains('\n'))
    }

    /// True if there is at least one blank line (two newlines with only horizontal whitespace
    /// between them) in the byte range `prev_end..next_start`.
    pub(super) fn has_blank_line_between(&self, prev_end: usize, next_start: usize) -> bool {
        if prev_end >= next_start {
            return false;
        }
        let Some(slice) = self.source.text().get(prev_end..next_start) else {
            return false;
        };
        let mut nl_count = 0usize;
        for ch in slice.chars() {
            if ch == '\n' {
                nl_count += 1;
                if nl_count >= 2 {
                    return true;
                }
            } else if ch != ' ' && ch != '\t' && ch != '\r' {
                nl_count = 0;
            }
        }
        false
    }

    /// True if the last argument of `Expr::Call` was written as a trailing closure (`f(a) \x -> ...`
    /// or `f \x -> ...`) rather than inside `(...)`.
    pub(super) fn has_trailing_closure(&self, last_arg_start: usize) -> bool {
        let idx = self.first_at_or_after(last_arg_start);
        if idx == 0 {
            return false;
        }
        let prev = self.text(idx - 1);
        self.text(idx) == "\\" && prev != "," && prev != "("
    }

    /// True if a `Call` with trailing closure also wrote empty `()` right before `\` (`f() \x -> ...`).
    pub(super) fn has_empty_parens_before_trailing_closure(
        &self,
        callee_end: usize,
        closure_start: usize,
    ) -> bool {
        let idx = self.first_at_or_after(callee_end);
        let close_idx = self.first_at_or_after(closure_start);
        close_idx >= idx + 2 && self.text(idx) == "(" && self.text(idx + 1) == ")"
    }

    /// Recovers exact `meta(...)` attribute groupings from `[stmt_start .. decl_start]`.
    pub(super) fn meta_attr_groups<'a>(
        &self,
        stmt_start: usize,
        limit_end: usize,
        attrs: &'a [ExprId],
        ast_expr_span: impl Fn(ExprId) -> Span,
    ) -> Vec<(usize, usize, &'a [ExprId])> {
        if attrs.is_empty() {
            return Vec::new();
        }
        let mut groups = Vec::new();
        let mut attr_cursor = 0usize;
        let mut idx = self.first_at_or_after(stmt_start);
        while attr_cursor < attrs.len() {
            let Some(tok) = self.code_tokens.get(idx) else {
                break;
            };
            if tok.span.start >= limit_end {
                break;
            }
            if tok.text(self.source) == "meta"
                && self.text(idx + 1) == "("
                && let Some(close_idx) = self.matching_close.get(idx + 1).copied().flatten()
                && let Some(close_tok) = self.code_tokens.get(close_idx)
            {
                let group_start = tok.span.start;
                let group_end = close_tok.span.end;
                let start_attr = attr_cursor;
                while let Some(&expr_id) = attrs.get(attr_cursor) {
                    if ast_expr_span(expr_id).end <= group_end {
                        attr_cursor += 1;
                    } else {
                        break;
                    }
                }
                if let Some(slice) = attrs.get(start_attr..attr_cursor) {
                    groups.push((group_start, group_end, slice));
                }
                idx = close_idx + 1;
                continue;
            }
            idx += 1;
        }
        if attr_cursor < attrs.len()
            && let Some(rest) = attrs.get(attr_cursor..)
        {
            groups.push((stmt_start, limit_end, rest));
        }
        groups
    }

    /// True if `use M::(foo)` wrote parentheses around a single imported item.
    pub(super) fn import_list_is_parenthesized(&self, stmt_span: Span) -> bool {
        let mut idx = self.first_at_or_after(stmt_span.start);
        while let Some(tok) = self.code_tokens.get(idx) {
            if tok.span.start >= stmt_span.end {
                return false;
            }
            if tok.text(self.source) == "(" {
                return true;
            }
            idx += 1;
        }
        false
    }

    /// True if a sum variant with `Type::Unit` payload was written `Foo()` (empty parens) rather than `Foo(())`.
    pub(super) fn variant_has_empty_parens(&self, variant_name_end: usize) -> bool {
        let idx = self.first_at_or_after(variant_name_end);
        self.text(idx) == "(" && self.text(idx + 1) == ")"
    }

    /// True if `type Point(int, int)` wrote a multi-arg tuple payload directly inside `type Name(...)`
    /// rather than double-wrapped `type Point((int, int))`.
    pub(super) fn nominal_tuple_is_unwrapped(&self, open_paren_search: usize) -> bool {
        let mut idx = self.first_at_or_after(open_paren_search);
        while let Some(tok) = self.code_tokens.get(idx) {
            if tok.text(self.source) == "(" {
                return self.text(idx + 1) != "(";
            }
            idx += 1;
        }
        false
    }

    /// True if an open record tail in `span_start..span_end` wrote `..let R` instead of `..R`.
    pub(super) fn tail_has_let(&self, search_start: usize, search_end: usize) -> bool {
        let mut idx = self.first_at_or_after(search_start);
        while let Some(tok) = self.code_tokens.get(idx) {
            if tok.span.start >= search_end {
                return false;
            }
            if tok.text(self.source) == ".." {
                return self.text(idx + 1) == "let";
            }
            idx += 1;
        }
        false
    }

    /// True if the source between `start..end` wrote a literal `...` range token or starts with
    /// an identifier. Used for exact token inspection around `String` / `RawString`.
    pub(super) fn raw_slice(&self, span: Span) -> &'src str {
        self.source
            .text()
            .get(span.start..span.end)
            .unwrap_or_default()
    }
}
