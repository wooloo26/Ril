//! Parser and AST-scope binder for `-- ril: allow(...)` / `-- ril: expect(...)` / `--! ril:` directives.

use std::str::FromStr;

use ril_source::span::{SourceFile, Span};
use ril_syntax::{
    lexer::{Kind, Token, Trivia, TriviaKind},
    syntax::Ast,
};

use crate::{
    config::LintCategory,
    registry::{self, LintDescriptor},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DirectiveAction {
    Allow,
    Expect,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DirectiveTarget {
    All,
    Category(LintCategory),
    Rule(String),
}

impl DirectiveTarget {
    pub fn matches(&self, rule: &LintDescriptor) -> bool {
        match self {
            Self::All => true,
            Self::Category(cat) => rule.category == *cat,
            Self::Rule(id) => rule.id == id,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ParsedDirective {
    pub span: Span,
    pub action: DirectiveAction,
    pub targets: Vec<DirectiveTarget>,
    /// Covered byte range in the file (whole file for `--! ril:`, attached `Stmt` span or line span).
    pub scope: (usize, usize),
    pub fulfilled: bool,
}

#[derive(Clone, Debug)]
pub struct DirectiveIssue {
    pub rule: &'static LintDescriptor,
    pub span: Span,
    pub message: String,
    pub help: Option<String>,
}

#[derive(Clone, Debug, Default)]
pub struct FileDirectives {
    pub directives: Vec<ParsedDirective>,
    pub issues: Vec<DirectiveIssue>,
}

impl FileDirectives {
    pub fn parse(source: &SourceFile, tokens: &[Token], trivia: &[Trivia], ast: &Ast) -> Self {
        let mut out = Self::default();
        let src = source.text();

        let first_code_byte = tokens
            .iter()
            .find(|t| !matches!(t.kind, Kind::Newline | Kind::Eof))
            .map_or(src.len(), |t| t.span.start);

        // Precompute code lines for trailing-vs-leading classification.
        let mut code_lines = Vec::new();
        for tok in tokens {
            if matches!(tok.kind, Kind::Newline | Kind::Eof) {
                continue;
            }
            if let Some(loc) = source.location(tok.span.start) {
                code_lines.push(loc.line);
            }
        }
        code_lines.sort_unstable();
        code_lines.dedup();

        // Collect all statement spans sorted by start byte for leading/trailing attachment.
        let mut stmt_spans: Vec<Span> = ast.statements().map(|s| s.span).collect();
        stmt_spans.sort_by_key(|s| (s.start, std::cmp::Reverse(s.end)));

        for triv in trivia {
            if triv.kind != TriviaKind::LineComment {
                continue;
            }
            let raw = src.get(triv.span.start..triv.span.end).unwrap_or("");
            let trimmed = raw.trim_start();
            if !ril_syntax::directive::is_lint_directive_comment(trimmed) {
                continue;
            }

            let is_file_wide = trimmed.starts_with("--!");
            let after_prefix = if is_file_wide {
                trimmed.strip_prefix("--!").unwrap_or("")
            } else {
                trimmed.strip_prefix("--").unwrap_or("")
            };
            let body = after_prefix
                .trim_start()
                .strip_prefix("ril:")
                .unwrap_or("")
                .trim();

            if is_file_wide && triv.span.start > first_code_byte {
                out.issues.push(DirectiveIssue {
                    rule: &registry::MALFORMED_LINT_DIRECTIVE,
                    span: triv.span,
                    message: "file-wide `--! ril:` directive must appear before the first item"
                        .to_owned(),
                    help: Some("move `--! ril:` to the top of the file".to_owned()),
                });
                continue;
            }

            let (action, rest) = if let Some(r) = body.strip_prefix("allow") {
                (DirectiveAction::Allow, r.trim_start())
            } else if let Some(r) = body.strip_prefix("expect") {
                (DirectiveAction::Expect, r.trim_start())
            } else {
                out.issues.push(DirectiveIssue {
                    rule: &registry::MALFORMED_LINT_DIRECTIVE,
                    span: triv.span,
                    message: "expected `allow(...)` or `expect(...)` after `ril:`".to_owned(),
                    help: Some("example: `-- ril: allow(unused_binding) -- reason`".to_owned()),
                });
                continue;
            };

            let Some(after_open) = rest.strip_prefix('(') else {
                out.issues.push(DirectiveIssue {
                    rule: &registry::MALFORMED_LINT_DIRECTIVE,
                    span: triv.span,
                    message: "expected `(` after lint directive action".to_owned(),
                    help: None,
                });
                continue;
            };
            let Some((inside, after_close)) = after_open.split_once(')') else {
                out.issues.push(DirectiveIssue {
                    rule: &registry::MALFORMED_LINT_DIRECTIVE,
                    span: triv.span,
                    message: "unclosed `(` in lint directive".to_owned(),
                    help: None,
                });
                continue;
            };

            // Trailing text after `)` must be empty or start with `--` reason comment.
            let tail = after_close.trim();
            if !tail.is_empty() && !tail.starts_with("--") {
                out.issues.push(DirectiveIssue {
                    rule: &registry::MALFORMED_LINT_DIRECTIVE,
                    span: triv.span,
                    message: "unexpected trailing text after `)` (prefix reasons with `--`)"
                        .to_owned(),
                    help: None,
                });
                continue;
            }

            let mut targets = Vec::new();
            for raw_item in inside.split(',') {
                let item = raw_item.trim();
                if item.is_empty() {
                    continue;
                }
                if registry::is_compiler_error_code(item) {
                    out.issues.push(DirectiveIssue {
                        rule: &registry::CANNOT_SUPPRESS_ERROR,
                        span: triv.span,
                        message: format!(
                            "compiler error `{item}` cannot be suppressed by lint directives"
                        ),
                        help: None,
                    });
                    continue;
                }
                if item == "all" {
                    targets.push(DirectiveTarget::All);
                } else if let Ok(cat) = LintCategory::from_str(item) {
                    targets.push(DirectiveTarget::Category(cat));
                } else if registry::find_rule(item).is_some() {
                    targets.push(DirectiveTarget::Rule(item.to_owned()));
                } else {
                    let help = registry::suggest_rule(item).map(|s| format!("did you mean `{s}`?"));
                    out.issues.push(DirectiveIssue {
                        rule: &registry::UNKNOWN_LINT_RULE,
                        span: triv.span,
                        message: format!("unknown lint rule or category `{item}`"),
                        help,
                    });
                }
            }

            if targets.is_empty() {
                continue;
            }

            let line = source.location(triv.span.start).map_or(1, |loc| loc.line);
            let is_trailing = !is_file_wide && code_lines.binary_search(&line).is_ok();

            let scope = if is_file_wide {
                (0, src.len())
            } else if is_trailing {
                // Attach to the innermost statement ending on this line, or this line's byte range.
                let line_start = src
                    .get(..triv.span.start)
                    .and_then(|p| p.rfind('\n'))
                    .map_or(0, |i| i + 1);
                let line_end = triv.span.end;
                stmt_spans
                    .iter()
                    .filter(|s| s.start <= line_end && s.end >= line_start && s.end <= line_end)
                    .min_by_key(|s| s.end.saturating_sub(s.start))
                    .map_or((line_start, line_end), |s| (s.start, s.end))
            } else {
                // Leading item/statement directive: walk forward across contiguous comment lines
                // (no blank line allowed!) to the next statement span.
                if let Some(next_stmt) = stmt_spans.iter().find(|s| s.start >= triv.span.end) {
                    if has_blank_line_between_comments(src, triv.span.end, next_stmt.start) {
                        out.issues.push(DirectiveIssue {
                            rule: &registry::MALFORMED_LINT_DIRECTIVE,
                            span: triv.span,
                            message: "lint directive is separated from the next item by a blank line"
                                .to_owned(),
                            help: Some(
                                "remove the blank line, or use `--! ril:` for a file-wide directive"
                                    .to_owned(),
                            ),
                        });
                        continue;
                    }
                    (next_stmt.start, next_stmt.end)
                } else {
                    out.issues.push(DirectiveIssue {
                        rule: &registry::MALFORMED_LINT_DIRECTIVE,
                        span: triv.span,
                        message: "floating lint directive has no following item".to_owned(),
                        help: None,
                    });
                    continue;
                }
            };

            out.directives.push(ParsedDirective {
                span: triv.span,
                action,
                targets,
                scope,
                fulfilled: false,
            });
        }

        out
    }

    /// Checks whether a finding at `span` for `rule` is suppressed by an `allow` or `expect`
    /// directive, marking matching `expect` directives as fulfilled.
    pub fn check_and_mark(&mut self, rule: &LintDescriptor, span: Span) -> bool {
        let mut suppressed = false;
        for dir in &mut self.directives {
            if span.start >= dir.scope.0
                && span.start <= dir.scope.1
                && dir.targets.iter().any(|t| t.matches(rule))
            {
                dir.fulfilled = true;
                suppressed = true;
            }
        }
        suppressed
    }
}

fn has_blank_line_between_comments(src: &str, start: usize, end: usize) -> bool {
    let Some(slice) = src.get(start..end) else {
        return false;
    };
    let mut nl = 0usize;
    for ch in slice.chars() {
        if ch == '\n' {
            nl += 1;
            if nl >= 2 {
                return true;
            }
        } else if ch != ' ' && ch != '\t' && ch != '\r' {
            nl = 0;
        }
    }
    false
}
