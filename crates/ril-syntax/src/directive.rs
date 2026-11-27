//! Shared helpers for Ril comment-based tool directives (`-- ril:`, `--! ril:`, `-- @suite`).

/// Returns `true` if `trimmed_line` is a Ril lint directive comment (`-- ril:` or `--! ril:`).
///
/// Used by `ril-syntax::fmt`, `ril-lint`, `ril-lsp::protocol::extract_doc_comment`, and
/// doc-comment checks so directive lines never break or pollute `--` documentation comments.
pub fn is_lint_directive_comment(trimmed_line: &str) -> bool {
    let rest = if let Some(after) = trimmed_line.strip_prefix("--!") {
        after
    } else if let Some(after) = trimmed_line.strip_prefix("--") {
        after
    } else {
        return false;
    };
    rest.trim_start().starts_with("ril:")
}

/// Returns `true` if `text` is a Ril conformance test suite file (`-- @suite` on first non-empty line).
pub fn is_suite_file(text: &str) -> bool {
    text.lines()
        .find(|line| !line.trim().is_empty())
        .is_some_and(|first| first.trim_start().starts_with("-- @suite"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recognizes_lint_directives_and_suite_headers() {
        assert!(is_lint_directive_comment("-- ril: allow(unused_binding)"));
        assert!(is_lint_directive_comment(
            "--! ril: allow(missing_doc_comment)"
        ));
        assert!(is_lint_directive_comment(
            "--   ril: expect(redundant_clone) -- reason"
        ));
        assert!(!is_lint_directive_comment("-- ril is a language"));
        assert!(!is_lint_directive_comment("-- @suite foo"));
        assert!(is_suite_file("\n  -- @suite syntax\n"));
        assert!(!is_suite_file("-- normal doc\nfn main() -> () {}\n"));
    }
}
