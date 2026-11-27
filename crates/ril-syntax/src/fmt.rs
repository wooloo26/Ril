//! Zero-config canonical AST + Doc-IR formatter for Ril (`ril fmt`).
//!
//! Guarantees:
//! - Purely syntactic layout (zero semantic edits, zero import reordering, zero paren stripping).
//! - Fixed canonical style: 4-space indent, 100-column target width, Zig-style trailing-comma
//!   layout signal, verbatim `--` comment preservation, LF line endings, single trailing newline.
//! - Refuses files with lex/parse errors and is strictly idempotent (`fmt(fmt(src)) == fmt(src)`).

mod comments;
mod doc;
mod printer;
mod tokens;

use ril_source::{diag::Diagnostic, span::SourceFile};

use crate::{
    lexer::{self, LexOutput},
    parser::{self, FileKind},
};

/// Formats a Ril source file canonically while preserving all comments, strings,
/// and exact Ril tight-left token semantics (`Ok(x)`, `User.{ ... }`, `a::b`, etc.).
///
/// Refuses to format files with lexer or parser errors, returning those diagnostics.
pub fn format_source(source: &SourceFile, kind: FileKind) -> Result<String, Vec<Diagnostic>> {
    let lexed = lexer::lex_with_recovery(source);
    format_source_with_lex(source, kind, lexed)
}

/// Formats a Ril source file using an already-lexed [`LexOutput`] (single-lex fast path).
pub fn format_source_with_lex(
    source: &SourceFile,
    kind: FileKind,
    lexed: LexOutput,
) -> Result<String, Vec<Diagnostic>> {
    if !lexed.diagnostics.is_empty() {
        return Err(lexed.diagnostics);
    }
    let parsed = parser::parse_with_recovery(source, &lexed.tokens, kind);
    if !parsed.diagnostics.is_empty() {
        return Err(parsed.diagnostics);
    }
    let token_index = tokens::TokenIndex::build(source, &lexed.tokens);
    let comment_store = comments::CommentStore::build(source, &lexed.tokens, &lexed.trivia);
    let mut printer = printer::Printer::new(source, &parsed.ast, token_index, comment_store);
    let root = printer.print_file();
    Ok(doc::render(&printer.arena, root))
}

/// Formats a Ril source file while inferring [`FileKind`] from its top-level token stream.
pub fn format_source_auto(source: &SourceFile) -> Result<String, Vec<Diagnostic>> {
    let lexed = lexer::lex_with_recovery(source);
    if !lexed.diagnostics.is_empty() {
        return Err(lexed.diagnostics);
    }
    let kind = parser::infer_file_kind(source, &lexed.tokens);
    format_source_with_lex(source, kind, lexed)
}

/// Generates a compact unified diff between `original` and `revised` with 3 lines of context.
pub fn unified_diff(label: &str, original: &str, revised: &str) -> String {
    if original == revised {
        return String::new();
    }
    let old: Vec<&str> = original.lines().collect();
    let new: Vec<&str> = revised.lines().collect();

    // Trim common prefix and suffix to keep DP linear for localized edits.
    let mut prefix = 0usize;
    while prefix < old.len() && prefix < new.len() && old.get(prefix) == new.get(prefix) {
        prefix += 1;
    }
    let mut suffix = 0usize;
    while prefix + suffix < old.len()
        && prefix + suffix < new.len()
        && old.get(old.len() - 1 - suffix) == new.get(new.len() - 1 - suffix)
    {
        suffix += 1;
    }

    let old_mid = old.get(prefix..old.len() - suffix).unwrap_or(&[]);
    let new_mid = new.get(prefix..new.len() - suffix).unwrap_or(&[]);

    #[derive(Clone, Copy)]
    enum Op<'a> {
        Equal(&'a str),
        Delete(&'a str),
        Insert(&'a str),
    }

    let mut ops: Vec<Op<'_>> = Vec::with_capacity(old.len() + new.len());
    for &line in old.get(..prefix).unwrap_or(&[]) {
        ops.push(Op::Equal(line));
    }

    if old_mid.len().saturating_mul(new_mid.len()) <= 250_000 {
        let m = old_mid.len();
        let n = new_mid.len();
        let stride = n + 1;
        let mut dp = vec![0u32; (m + 1) * stride];
        for i in (0..m).rev() {
            for j in (0..n).rev() {
                let val = if old_mid.get(i) == new_mid.get(j) {
                    dp.get((i + 1) * stride + (j + 1)).copied().unwrap_or(0) + 1
                } else {
                    let down = dp.get((i + 1) * stride + j).copied().unwrap_or(0);
                    let right = dp.get(i * stride + (j + 1)).copied().unwrap_or(0);
                    down.max(right)
                };
                if let Some(slot) = dp.get_mut(i * stride + j) {
                    *slot = val;
                }
            }
        }
        let (mut i, mut j) = (0usize, 0usize);
        while i < m && j < n {
            if old_mid.get(i) == new_mid.get(j) {
                if let Some(&l) = old_mid.get(i) {
                    ops.push(Op::Equal(l));
                }
                i += 1;
                j += 1;
            } else {
                let down = dp.get((i + 1) * stride + j).copied().unwrap_or(0);
                let right = dp.get(i * stride + (j + 1)).copied().unwrap_or(0);
                if down >= right {
                    if let Some(&l) = old_mid.get(i) {
                        ops.push(Op::Delete(l));
                    }
                    i += 1;
                } else {
                    if let Some(&l) = new_mid.get(j) {
                        ops.push(Op::Insert(l));
                    }
                    j += 1;
                }
            }
        }
        while i < m {
            if let Some(&l) = old_mid.get(i) {
                ops.push(Op::Delete(l));
            }
            i += 1;
        }
        while j < n {
            if let Some(&l) = new_mid.get(j) {
                ops.push(Op::Insert(l));
            }
            j += 1;
        }
    } else {
        for &l in old_mid {
            ops.push(Op::Delete(l));
        }
        for &l in new_mid {
            ops.push(Op::Insert(l));
        }
    }

    for &line in old.get(old.len() - suffix..).unwrap_or(&[]) {
        ops.push(Op::Equal(line));
    }

    // Group non-equal ops into unified diff hunks with 3 lines of context.
    let context = 3usize;
    let changed: Vec<usize> = ops
        .iter()
        .enumerate()
        .filter_map(|(idx, op)| (!matches!(op, Op::Equal(_))).then_some(idx))
        .collect();
    if changed.is_empty() {
        return String::new();
    }

    let mut out = format!("--- a/{label}\n+++ b/{label}\n");
    let mut hunks: Vec<(usize, usize)> = Vec::new();
    for idx in changed {
        let start = idx.saturating_sub(context);
        let end = (idx + context + 1).min(ops.len());
        if let Some(last) = hunks.last_mut()
            && start <= last.1
        {
            last.1 = end;
        } else {
            hunks.push((start, end));
        }
    }

    for (h_start, h_end) in hunks {
        let mut old_line = 1usize;
        let mut new_line = 1usize;
        for op in ops.get(..h_start).unwrap_or(&[]) {
            match op {
                Op::Equal(_) => {
                    old_line += 1;
                    new_line += 1;
                }
                Op::Delete(_) => old_line += 1,
                Op::Insert(_) => new_line += 1,
            }
        }
        let mut old_count = 0usize;
        let mut new_count = 0usize;
        for op in ops.get(h_start..h_end).unwrap_or(&[]) {
            match op {
                Op::Equal(_) => {
                    old_count += 1;
                    new_count += 1;
                }
                Op::Delete(_) => old_count += 1,
                Op::Insert(_) => new_count += 1,
            }
        }
        out.push_str(&format!(
            "@@ -{old_line},{old_count} +{new_line},{new_count} @@\n"
        ));
        for op in ops.get(h_start..h_end).unwrap_or(&[]) {
            match op {
                Op::Equal(l) => {
                    out.push(' ');
                    out.push_str(l);
                    out.push('\n');
                }
                Op::Delete(l) => {
                    out.push('-');
                    out.push_str(l);
                    out.push('\n');
                }
                Op::Insert(l) => {
                    out.push('+');
                    out.push_str(l);
                    out.push('\n');
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use ril_source::span::{FileId, SourceFile};

    use super::{format_source, unified_diff};
    use crate::parser::FileKind;

    fn fmt(src: &str) -> String {
        let source =
            SourceFile::from_bytes(FileId(1), PathBuf::from("pkg/fmt_test.ril"), src.as_bytes())
                .expect("valid utf-8");
        let out1 = format_source(&source, FileKind::Module).expect("formats cleanly");
        let source2 = SourceFile::from_bytes(
            FileId(1),
            PathBuf::from("pkg/fmt_test.ril"),
            out1.as_bytes(),
        )
        .expect("valid utf-8");
        let out2 = format_source(&source2, FileKind::Module).expect("reformats cleanly");
        assert_eq!(out1, out2, "formatter must be strictly idempotent");
        out1
    }

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
        assert_eq!(fmt(input), input);
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
        assert_eq!(fmt(input), input);
    }

    #[test]
    fn format_fixes_bitwise_xor_and_binary_operators() {
        let input = "fn bits(a: int, b: int) -> int {\n    (a^b) + (a<<1) + (b>>1)\n}\n";
        let expected = "fn bits(a: int, b: int) -> int {\n    (a ^ b) + (a << 1) + (b >> 1)\n}\n";
        assert_eq!(fmt(input), expected);
    }

    #[test]
    fn format_zig_trailing_comma_signal() {
        let expanded = "fn f(\n    a: int,\n    b: int,\n) -> int {\n    a + b\n}\n";
        assert_eq!(fmt(expanded), expanded);
        let collapsed = "fn f(\n    a: int,\n    b: int\n) -> int {\n    a + b\n}\n";
        assert_eq!(
            fmt(collapsed),
            "fn f(a: int, b: int) -> int {\n    a + b\n}\n"
        );
    }

    #[test]
    fn format_preserves_comments_and_meta_expr_space() {
        let input = concat!(
            "-- Doc comment.\n",
            "-- ril: allow(unused_binding)\n",
            "fn f() -> int {\n",
            "    let x = meta (1 + 2) -- inline note\n",
            "    x\n",
            "}\n",
        );
        assert_eq!(fmt(input), input);
    }

    #[test]
    fn unified_diff_reports_hunks() {
        let diff = unified_diff("pkg/a.ril", "a\nb\nc\n", "a\nB\nc\n");
        assert!(diff.contains("--- a/pkg/a.ril"));
        assert!(diff.contains("-b\n+B\n"));
    }
}
