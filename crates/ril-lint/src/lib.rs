#![forbid(unsafe_code)]
#![deny(clippy::indexing_slicing)]

//! Read-only static linter (`ril lint`) for Ril.
//!
//! Operates strictly over existing frontend/sema artifacts (`SourceMap`, `Ast`, `hir::Program`,
//! `TypedProgram`, `Analysis`) without repeating spec-normative `E0xxx` compiler checks.
//! Emits [`LintDiagnostic`] items with structured [`ril_source::fix::Fix`] edits consumed by
//! `ril fix` and `ril lsp`.

pub mod config;
pub mod directive;
pub mod passes;
pub mod registry;
mod render;

use std::collections::{BTreeMap, BTreeSet};

use ril_hir as hir;
use ril_sema::{access::Analysis, ty::TypedProgram};
use ril_source::{
    diag::SecondaryLabel,
    fix::{DiagnosticTag, Fix},
    span::{FileId, SourceMap, Span},
};
use ril_syntax::{
    lexer::{self, LexOutput},
    parser::{self, FileKind},
    syntax::Ast,
};
use serde::{Deserialize, Serialize};

pub use config::{CliOverride, CliTarget, LintCategory, LintConfig, LintLevel, LintOptions};
pub use registry::{ALL_LINTS, LintDescriptor, LintStage, find_rule};

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct LintDiagnostic {
    pub rule: String,
    pub category: LintCategory,
    pub level: LintLevel,
    pub primary: Span,
    pub message: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub labels: Vec<SecondaryLabel>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub notes: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub help: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub tags: Vec<DiagnosticTag>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub fixes: Vec<Fix>,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct LintReport {
    pub diagnostics: Vec<LintDiagnostic>,
    pub warning_count: usize,
    pub deny_count: usize,
}

impl LintReport {
    pub fn has_denied(&self) -> bool {
        self.deny_count > 0
    }
}

pub struct SyntaxFileData {
    pub lexed: LexOutput,
    pub ast: Ast,
}

struct RawFinding {
    rule: &'static LintDescriptor,
    primary: Span,
    message: String,
    labels: Vec<SecondaryLabel>,
    notes: Vec<String>,
    help: Vec<String>,
    tags: Vec<DiagnosticTag>,
    fixes: Vec<Fix>,
}

pub struct LintContext<'a> {
    pub sources: &'a SourceMap,
    pub config: &'a LintConfig,
    pub target_files: &'a BTreeSet<FileId>,
    pub syntax_files: &'a BTreeMap<FileId, SyntaxFileData>,
    pub hir: Option<&'a hir::Program>,
    pub typed: Option<&'a TypedProgram>,
    pub analysis: Option<&'a Analysis>,
    directives: BTreeMap<FileId, directive::FileDirectives>,
    raw_findings: Vec<RawFinding>,
}

impl<'a> LintContext<'a> {
    pub fn report(
        &mut self,
        rule: &'static LintDescriptor,
        span: Span,
        message: impl Into<String>,
    ) -> FindingBuilder<'_, 'a> {
        let idx = self.raw_findings.len();
        self.raw_findings.push(RawFinding {
            rule,
            primary: span,
            message: message.into(),
            labels: Vec::new(),
            notes: Vec::new(),
            help: Vec::new(),
            tags: rule.tags.to_vec(),
            fixes: Vec::new(),
        });
        FindingBuilder { ctx: self, idx }
    }

    /// Returns true if `rule` could fire (either enabled by config/CLI or targeted by an inline `expect`).
    pub fn may_fire(&self, rule: &'static LintDescriptor) -> bool {
        if self.config.effective_level(rule, false) != LintLevel::Allow {
            return true;
        }
        self.directives.values().any(|fd| {
            fd.directives.iter().any(|d| {
                d.action == directive::DirectiveAction::Expect
                    && d.targets.iter().any(|t| t.matches(rule))
            })
        })
    }

    pub fn is_target_file(&self, file: FileId) -> bool {
        self.target_files.contains(&file)
    }

    pub fn source_text(&self, file: FileId) -> &'a str {
        self.sources.get(file).map_or("", |f| f.text())
    }

    pub fn slice(&self, span: Span) -> &'a str {
        self.source_text(span.file)
            .get(span.start..span.end)
            .unwrap_or("")
    }

    /// True if `span` lies strictly inside an untaken branch of a statically evaluated `meta if`
    /// or `meta match` in `typed`.
    pub fn is_in_pruned_meta_branch(&self, span: Span) -> bool {
        let Some(typed) = self.typed else {
            return false;
        };
        let file = typed.hir.file(span.file);
        for (&if_span, &taken_yes) in &typed.meta_if_decisions {
            if if_span.file != span.file || span.start < if_span.start || span.end > if_span.end {
                continue;
            }
            for node in file.ast.expressions() {
                if node.span == if_span
                    && let ril_syntax::syntax::Expr::If { yes, no, .. } = node.value
                {
                    let pruned = if taken_yes {
                        no.map(|n| file.ast.expr(n).span)
                    } else {
                        Some(file.ast.expr(yes).span)
                    };
                    if let Some(ps) = pruned
                        && span.start >= ps.start
                        && span.end <= ps.end
                    {
                        return true;
                    }
                }
            }
        }
        for (&match_span, &taken_idx) in &typed.meta_match_decisions {
            if match_span.file != span.file
                || span.start < match_span.start
                || span.end > match_span.end
            {
                continue;
            }
            for node in file.ast.expressions() {
                if node.span == match_span
                    && let ril_syntax::syntax::Expr::Match { arms, .. } = &node.value
                {
                    for (idx, arm) in arms.iter().enumerate() {
                        if idx == taken_idx {
                            continue;
                        }
                        let body_span = file.ast.expr(arm.body).span;
                        if span.start >= body_span.start && span.end <= body_span.end {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    fn finalize(mut self) -> LintReport {
        // 1. Emit directive parse issues first (e.g. `cannot_suppress_error`, `unknown_lint_rule`).
        let issues: Vec<directive::DirectiveIssue> = self
            .directives
            .values()
            .flat_map(|fd| fd.issues.iter().cloned())
            .collect();
        for issue in issues {
            let mut b = self.report(issue.rule, issue.span, issue.message);
            if let Some(h) = issue.help {
                b = b.with_help(h);
            }
            let _ = b;
        }

        // 2. Resolve inline suppressions and effective levels for every raw finding.
        let mut diagnostics = Vec::new();
        for raw in std::mem::take(&mut self.raw_findings) {
            if !self.target_files.contains(&raw.primary.file) {
                continue;
            }
            let inline_allowed = self
                .directives
                .get_mut(&raw.primary.file)
                .is_some_and(|fd| fd.check_and_mark(raw.rule, raw.primary));
            let level = self.config.effective_level(raw.rule, inline_allowed);
            if level == LintLevel::Allow {
                continue;
            }
            diagnostics.push(LintDiagnostic {
                rule: raw.rule.id.to_owned(),
                category: raw.rule.category,
                level,
                primary: raw.primary,
                message: raw.message,
                labels: raw.labels,
                notes: raw.notes,
                help: raw.help,
                tags: raw.tags,
                fixes: raw.fixes,
            });
        }

        // 3. Emit `unfulfilled_expect` for any `-- ril: expect(...)` that matched 0 findings.
        let unfulfilled: Vec<(Span, String)> = self
            .directives
            .values()
            .flat_map(|fd| fd.directives.iter())
            .filter(|d| d.action == directive::DirectiveAction::Expect && !d.fulfilled)
            .map(|d| {
                let names: Vec<String> = d
                    .targets
                    .iter()
                    .map(|t| match t {
                        directive::DirectiveTarget::All => "all".to_owned(),
                        directive::DirectiveTarget::Category(c) => c.as_str().to_owned(),
                        directive::DirectiveTarget::Rule(r) => r.clone(),
                    })
                    .collect();
                (
                    d.span,
                    format!(
                        "`expect({})` was not fulfilled by any lint finding",
                        names.join(", ")
                    ),
                )
            })
            .collect();

        for (span, msg) in unfulfilled {
            let level = self
                .config
                .effective_level(&registry::UNFULFILLED_EXPECT, false);
            if level != LintLevel::Allow {
                diagnostics.push(LintDiagnostic {
                    rule: registry::UNFULFILLED_EXPECT.id.to_owned(),
                    category: registry::UNFULFILLED_EXPECT.category,
                    level,
                    primary: span,
                    message: msg,
                    labels: Vec::new(),
                    notes: Vec::new(),
                    help: vec!["remove this stale `expect(...)` directive".to_owned()],
                    tags: Vec::new(),
                    fixes: Vec::new(),
                });
            }
        }

        // Deterministic sort by (file_id, start, end, rule).
        diagnostics.sort_by(|a, b| {
            (a.primary.file, a.primary.start, a.primary.end, &a.rule).cmp(&(
                b.primary.file,
                b.primary.start,
                b.primary.end,
                &b.rule,
            ))
        });
        diagnostics.dedup_by(|a, b| a.rule == b.rule && a.primary == b.primary);

        let mut warning_count = 0usize;
        let mut deny_count = 0usize;
        for d in &diagnostics {
            match d.level {
                LintLevel::Deny => deny_count += 1,
                LintLevel::Warn => warning_count += 1,
                LintLevel::Allow => {}
            }
        }

        LintReport {
            diagnostics,
            warning_count,
            deny_count,
        }
    }
}

pub struct FindingBuilder<'ctx, 'a> {
    ctx: &'ctx mut LintContext<'a>,
    idx: usize,
}

impl FindingBuilder<'_, '_> {
    pub fn with_label(self, span: Span, message: impl Into<String>) -> Self {
        if let Some(raw) = self.ctx.raw_findings.get_mut(self.idx) {
            raw.labels.push(SecondaryLabel {
                span,
                message: message.into(),
            });
        }
        self
    }

    pub fn with_note(self, note: impl Into<String>) -> Self {
        if let Some(raw) = self.ctx.raw_findings.get_mut(self.idx) {
            raw.notes.push(note.into());
        }
        self
    }

    pub fn with_help(self, help: impl Into<String>) -> Self {
        if let Some(raw) = self.ctx.raw_findings.get_mut(self.idx) {
            raw.help.push(help.into());
        }
        self
    }

    pub fn with_fix(self, fix: Fix) -> Self {
        if let Some(raw) = self.ctx.raw_findings.get_mut(self.idx) {
            raw.fixes.push(fix);
        }
        self
    }
}

/// Runs all applicable lint passes up to the highest available analysis stage.
pub fn run_partial(
    sources: &SourceMap,
    target_files: &BTreeSet<FileId>,
    typed: Option<&TypedProgram>,
    analysis: Option<&Analysis>,
    config: &LintConfig,
) -> LintReport {
    let mut syntax_files = BTreeMap::new();
    let mut directives = BTreeMap::new();

    for &file_id in target_files {
        let Some(source) = sources.get(file_id) else {
            continue;
        };
        let lexed = lexer::lex_with_recovery(source);
        let ast = if let Some(typed) = typed
            && let Some(hir_file) = typed.hir.files().find(|f| f.id == file_id)
        {
            (*hir_file.ast).clone()
        } else {
            let kind = parser::infer_file_kind(source, &lexed.tokens);
            parser::parse_with_recovery(source, &lexed.tokens, kind).ast
        };
        let parsed_dirs =
            directive::FileDirectives::parse(source, &lexed.tokens, &lexed.trivia, &ast);
        directives.insert(file_id, parsed_dirs);
        syntax_files.insert(file_id, SyntaxFileData { lexed, ast });
    }

    let hir = typed.map(|t| &t.hir);
    let mut ctx = LintContext {
        sources,
        config,
        target_files,
        syntax_files: &syntax_files,
        hir,
        typed,
        analysis,
        directives,
        raw_findings: Vec::new(),
    };

    passes::run_all(&mut ctx);
    ctx.finalize()
}

/// Convenience helper for linting a single source snippet/file without a package.
pub fn lint_source(
    source: &ril_source::span::SourceFile,
    kind: FileKind,
    config: &LintConfig,
) -> LintReport {
    let mut sources = SourceMap::default();
    let Ok(id) = sources.add_with_id(
        source.id(),
        source.path().to_path_buf(),
        source.text().as_bytes(),
    ) else {
        return LintReport::default();
    };
    let lexed = lexer::lex_with_recovery(source);
    let parsed = parser::parse_with_recovery(source, &lexed.tokens, kind);
    let mut targets = BTreeSet::new();
    targets.insert(id);
    if !lexed.diagnostics.is_empty() || !parsed.diagnostics.is_empty() {
        return run_partial(&sources, &targets, None, None, config);
    }
    let file = hir::File::new(source.clone(), kind, parsed.ast, lexed.tokens);
    let (hir_prog, hir_diags) = hir::lower_partial(vec![file], id);
    let (typed, ty_diags) = ril_sema::ty::check_partial(hir_prog, None);
    let analysis = if hir_diags.is_empty() && ty_diags.is_empty() {
        Some(ril_sema::access::check_partial(&typed).0)
    } else {
        None
    };
    run_partial(&sources, &targets, Some(&typed), analysis.as_ref(), config)
}
