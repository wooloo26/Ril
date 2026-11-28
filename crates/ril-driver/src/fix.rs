//! Multi-pass semantic auto-fix engine (`ril fix`) and fix-hint projection (`ril inspect --include fix_hints`).

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

use ril_hir::{DefinitionId, DefinitionKind, Program, Resolution};
use ril_sema::{
    access::{Access, AnalysisMode, InferredReturnMode},
    ty::TypedProgram,
};
use ril_source::{
    diag::{Code, Diagnostic, Severity},
    fix::{CapabilityDelta, Fix, FixKind, FixSafety, TextEdit},
    span::{FileId, SourceFile, SourceMap, Span},
};
use ril_syntax::{
    lexer,
    parser::FileKind,
    syntax::{Ast, Function, Mode, StateKind, StmtKind, Visibility},
};
use ril_test::{Unit, VirtualPackage};
use serde::Serialize;

use crate::{Compiler, PartialAnalysis, incremental::sha256, load_package_with_paths};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum FixFilter {
    #[default]
    All,
    Errors,
    Lints,
    Sigs,
}

#[derive(Clone, Debug)]
pub struct FixOptions {
    pub filter: FixFilter,
    pub codes: BTreeSet<String>,
    pub no_sigs: bool,
    pub allow_api_change: bool,
    pub allow_unsafe: bool,
    pub dry_run: bool,
    pub fmt_after: bool,
    pub max_passes: usize,
}

impl Default for FixOptions {
    fn default() -> Self {
        Self {
            filter: FixFilter::All,
            codes: BTreeSet::new(),
            no_sigs: false,
            allow_api_change: false,
            allow_unsafe: false,
            dry_run: false,
            fmt_after: false,
            max_passes: 12,
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct AppliedFix {
    pub file: String,
    pub code: String,
    pub title: String,
    pub safety: FixSafety,
    pub kind: FixKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub capability_delta: Option<CapabilityDelta>,
    pub pass: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct SkippedFix {
    pub file: String,
    pub code: String,
    pub title: String,
    pub safety: FixSafety,
    pub reason: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub capability_delta: Option<CapabilityDelta>,
}

#[derive(Clone, Debug, Serialize)]
pub struct FileDiff {
    pub path: String,
    pub original: String,
    pub updated: String,
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct FixReport {
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub syntax_errors: Vec<String>,
    pub passes: usize,
    pub converged: bool,
    pub oscillated: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub applied: Vec<AppliedFix>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub skipped: Vec<SkippedFix>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub remaining_errors: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub remaining_warnings: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub modified_files: Vec<FileDiff>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub capability_deltas: Vec<CapabilityDelta>,
}

impl FixReport {
    pub fn has_capability_widening(&self) -> bool {
        self.capability_deltas.iter().any(|d| !d.added.is_empty())
    }

    pub fn format_capability_banner(&self) -> Option<String> {
        if self.capability_deltas.is_empty() {
            return None;
        }
        let mut out = String::new();
        out.push_str("Capability changes applied:\n");
        for delta in &self.capability_deltas {
            let mut parts = Vec::new();
            for item in &delta.added {
                parts.push(format!("+{item}"));
            }
            for item in &delta.removed {
                parts.push(format!("-{item}"));
            }
            let vis = if delta.visibility == "private" {
                String::new()
            } else {
                format!("{} ", delta.visibility)
            };
            let cause = if delta.causal_chain.len() > 1 {
                format!(" (via {})", delta.causal_chain.join(" -> "))
            } else {
                String::new()
            };
            out.push_str(&format!(
                "  {vis}fn {}: {}{cause}\n",
                delta.symbol,
                parts.join(", ")
            ));
        }
        Some(out)
    }
}

/// Candidate fix with source provenance for sorting, filtering, and reporting.
#[derive(Clone, Debug)]
pub struct CandidateFix {
    pub code: String,
    pub priority: u8,
    pub fix: Fix,
}

/// Collects all fix hints (compiler fixes + signature sync + lint fixes) for read-only consumers
/// such as `ril inspect --include fix_hints`.
pub fn collect_fix_hints(
    partial: &PartialAnalysis,
    lint_config: &ril_lint::LintConfig,
) -> Vec<CandidateFix> {
    let mut out = Vec::new();
    let all_opts = FixOptions {
        allow_api_change: true,
        allow_unsafe: true,
        ..FixOptions::default()
    };
    collect_compiler_fixes(partial, &mut out);
    if partial.analysis.is_some() {
        let (sig_fixes, _) = synthesize_signature_fixes(partial, &all_opts);
        out.extend(sig_fixes);
    }
    let target_files: BTreeSet<FileId> = partial
        .typed
        .as_ref()
        .map(|typed| {
            typed
                .hir
                .files()
                .filter(|f| !typed.hir.is_stdlib_file(f.id) && !f.is_interface())
                .map(|f| f.id)
                .collect()
        })
        .unwrap_or_default();
    let lint_report = ril_lint::run_partial(
        &partial.sources,
        &target_files,
        partial.typed.as_deref(),
        partial.analysis.as_deref(),
        lint_config,
    );
    for diag in &lint_report.diagnostics {
        let code = diag.rule.clone();
        for fix in &diag.fixes {
            out.push(CandidateFix {
                code: code.clone(),
                priority: 2,
                fix: fix.clone(),
            });
        }
    }
    out
}

/// Runs `ril fix` against a package on disk, atomically writing modified `pkg/` files unless `dry_run`.
pub fn fix_package_files(
    compiler: &Compiler,
    path: &Path,
    unit: Unit,
    options: &FixOptions,
    lint_config: &ril_lint::LintConfig,
) -> Result<FixReport, String> {
    let (mut pkg, disk_paths) = load_package_with_paths(path, unit)?;
    let report = fix_virtual_package(compiler, &mut pkg, options, lint_config);
    if !options.dry_run && report.syntax_errors.is_empty() {
        for diff in &report.modified_files {
            let vpath = PathBuf::from(&diff.path);
            let Some(disk_path) = disk_paths.get(&vpath) else {
                continue;
            };
            write_atomic(disk_path, diff.updated.as_bytes())
                .map_err(|err| format!("{}: {err}", disk_path.display()))?;
        }
    }
    Ok(report)
}

fn write_atomic(path: &Path, bytes: &[u8]) -> std::io::Result<()> {
    let Some(parent) = path.parent() else {
        return fs::write(path, bytes);
    };
    let file_name = path
        .file_name()
        .and_then(std::ffi::OsStr::to_str)
        .unwrap_or("ril");
    let tmp = parent.join(format!(".{file_name}.ril-fix-tmp.{}", std::process::id()));
    fs::write(&tmp, bytes)?;
    match fs::rename(&tmp, path) {
        Ok(()) => Ok(()),
        Err(_) => {
            let _ = fs::remove_file(&tmp);
            fs::write(path, bytes)
        }
    }
}

/// Runs the multi-pass fix engine in-memory on a `VirtualPackage`.
pub fn fix_virtual_package(
    compiler: &Compiler,
    pkg: &mut VirtualPackage,
    options: &FixOptions,
    lint_config: &ril_lint::LintConfig,
) -> FixReport {
    let mut report = FixReport::default();

    // Snapshot original LF-normalized text for editable `pkg/...` `.ril` files.
    let mut original_texts: BTreeMap<PathBuf, String> = BTreeMap::new();
    let mut original_raw: BTreeMap<PathBuf, Vec<u8>> = BTreeMap::new();
    for (vpath, vfile) in &pkg.files {
        if is_editable_vpath(vpath) {
            original_raw.insert(vpath.clone(), vfile.bytes.clone());
            if let Ok(sf) =
                SourceFile::from_bytes(FileId::from_path(vpath), vpath.clone(), &vfile.bytes)
            {
                original_texts.insert(vpath.clone(), sf.text().to_owned());
            }
        }
    }

    // Hard refusal on syntax errors before any mutation.
    let initial = compiler.analyze_partial_with_mode(pkg, AnalysisMode::Fix);
    if initial.stage == "parse" {
        report.syntax_errors = initial
            .diagnostics
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .map(|d| render_diag_string(d, &initial.sources))
            .collect();
        return report;
    }

    let mut seen_hashes = BTreeSet::new();
    let mut final_skipped: Vec<SkippedFix> = Vec::new();
    let max_passes = options.max_passes.max(1);

    for pass in 1..=max_passes {
        let state_hash = hash_editable_files(pkg);
        if !seen_hashes.insert(state_hash) {
            report.oscillated = true;
            break;
        }
        report.passes = pass;

        let partial = compiler.analyze_partial_with_mode(pkg, AnalysisMode::Fix);
        if partial.stage == "parse" {
            report.syntax_errors = partial
                .diagnostics
                .iter()
                .filter(|d| d.severity == Severity::Error)
                .map(|d| render_diag_string(d, &partial.sources))
                .collect();
            break;
        }

        let mut candidates: Vec<CandidateFix> = Vec::new();
        let mut skipped_this_pass: Vec<SkippedFix> = Vec::new();

        // Phase A: Compiler diagnostics (HIR / Type / Access).
        if matches!(options.filter, FixFilter::All | FixFilter::Errors) {
            collect_compiler_fixes(&partial, &mut candidates);
        }

        // Phase B1: Signature synchronization.
        if partial.analysis.is_some()
            && !options.no_sigs
            && matches!(options.filter, FixFilter::All | FixFilter::Sigs)
        {
            let (sig_candidates, sig_skipped) = synthesize_signature_fixes(&partial, options);
            candidates.extend(sig_candidates);
            skipped_this_pass.extend(sig_skipped);
        }

        // Phase B2: Lint fixes.
        if matches!(options.filter, FixFilter::All | FixFilter::Lints) {
            let target_files = editable_file_ids(&partial, pkg);
            let lint_report = ril_lint::run_partial(
                &partial.sources,
                &target_files,
                partial.typed.as_deref(),
                partial.analysis.as_deref(),
                lint_config,
            );
            for diag in &lint_report.diagnostics {
                let code = diag.rule.clone();
                for fix in &diag.fixes {
                    candidates.push(CandidateFix {
                        code: code.clone(),
                        priority: 2,
                        fix: fix.clone(),
                    });
                }
            }
        }

        // Filter by `--code` and safety tier.
        let mut eligible = Vec::new();
        for cand in candidates {
            if !options.codes.is_empty() && !options.codes.contains(&cand.code) {
                continue;
            }
            if cand.fix.edits.is_empty() {
                continue;
            }
            if !all_edits_editable(&cand.fix.edits, &partial, pkg) {
                continue;
            }
            match cand.fix.safety {
                FixSafety::Safe => eligible.push(cand),
                FixSafety::Contract => {
                    if options.allow_api_change {
                        eligible.push(cand);
                    } else {
                        skipped_this_pass.push(SkippedFix {
                            file: first_edit_path(&cand.fix, &partial),
                            code: cand.code,
                            title: cand.fix.title,
                            safety: cand.fix.safety,
                            reason: "widens pkg/pub API contract (re-run with --allow-api-change)"
                                .into(),
                            capability_delta: cand.fix.delta,
                        });
                    }
                }
                FixSafety::Unsafe => {
                    if options.allow_unsafe {
                        eligible.push(cand);
                    } else {
                        skipped_this_pass.push(SkippedFix {
                            file: first_edit_path(&cand.fix, &partial),
                            code: cand.code,
                            title: cand.fix.title,
                            safety: cand.fix.safety,
                            reason: "may change behavior (re-run with --unsafe)".into(),
                            capability_delta: cand.fix.delta,
                        });
                    }
                }
                FixSafety::Assist => {
                    skipped_this_pass.push(SkippedFix {
                        file: first_edit_path(&cand.fix, &partial),
                        code: cand.code,
                        title: cand.fix.title,
                        safety: cand.fix.safety,
                        reason: "editor-only assist (not applied in batch CLI)".into(),
                        capability_delta: cand.fix.delta,
                    });
                }
            }
        }

        final_skipped = skipped_this_pass;
        if eligible.is_empty() {
            report.converged = true;
            break;
        }

        // Deterministic sort: priority, then first edit position, then code/title.
        eligible.sort_by(|a, b| {
            let a_key = a
                .fix
                .edits
                .first()
                .map_or((0, 0, 0), |e| (e.span.file.0, e.span.start, e.span.end));
            let b_key = b
                .fix
                .edits
                .first()
                .map_or((0, 0, 0), |e| (e.span.file.0, e.span.start, e.span.end));
            (a.priority, a_key, &a.code, &a.fix.title).cmp(&(
                b.priority,
                b_key,
                &b.code,
                &b.fix.title,
            ))
        });

        // Select non-overlapping batch.
        let selected = select_non_overlapping(eligible);
        if selected.is_empty() {
            report.converged = true;
            break;
        }

        // Try batch application with transactional regression check.
        let baseline_errors = error_codes_of(&partial);
        let (accepted, dropped) = apply_with_guardrails(
            compiler,
            pkg,
            &partial,
            selected,
            &baseline_errors,
            &mut final_skipped,
        );
        if accepted.is_empty() {
            let _ = dropped;
            report.converged = true;
            break;
        }
        for cand in accepted {
            let file = first_edit_path(&cand.fix, &partial);
            if let Some(delta) = &cand.fix.delta {
                report.capability_deltas.push(delta.clone());
            }
            report.applied.push(AppliedFix {
                file,
                code: cand.code,
                title: cand.fix.title,
                safety: cand.fix.safety,
                kind: cand.fix.kind,
                capability_delta: cand.fix.delta,
                pass,
            });
        }
    }

    report.skipped = final_skipped;

    // Optional canonical formatting pass on modified files.
    if options.fmt_after {
        let mut to_fmt: Vec<(PathBuf, String)> = Vec::new();
        for (vpath, orig) in &original_texts {
            if let Some(vfile) = pkg.files.get(vpath)
                && let Ok(sf) =
                    SourceFile::from_bytes(FileId::from_path(vpath), vpath.clone(), &vfile.bytes)
                && sf.text() != orig
            {
                let kind = if vpath == &pkg.entry {
                    match pkg.unit {
                        Unit::Bin => FileKind::Executable,
                        Unit::Lib => FileKind::Module,
                        Unit::Snippet => FileKind::Snippet,
                    }
                } else {
                    FileKind::Module
                };
                if let Ok(formatted) = ril_syntax::fmt::format_source(&sf, kind) {
                    to_fmt.push((vpath.clone(), formatted));
                }
            }
        }
        for (vpath, formatted) in to_fmt {
            pkg.insert(vpath, formatted.into_bytes());
        }
    }

    // Final read-only analysis to collect remaining diagnostics & diffs.
    let final_partial = compiler.analyze_partial_with_mode(pkg, AnalysisMode::Check);
    let target_files = editable_file_ids(&final_partial, pkg);
    let final_lint = ril_lint::run_partial(
        &final_partial.sources,
        &target_files,
        final_partial.typed.as_deref(),
        final_partial.analysis.as_deref(),
        lint_config,
    );
    for diag in &final_partial.diagnostics {
        match diag.severity {
            Severity::Error => report
                .remaining_errors
                .push(render_diag_string(diag, &final_partial.sources)),
            Severity::Warning => report
                .remaining_warnings
                .push(render_diag_string(diag, &final_partial.sources)),
        }
    }
    for diag in &final_lint.diagnostics {
        let rendered = render_lint_string(diag, &final_partial.sources);
        match diag.level {
            ril_lint::LintLevel::Deny => report.remaining_errors.push(rendered),
            ril_lint::LintLevel::Warn => report.remaining_warnings.push(rendered),
            ril_lint::LintLevel::Allow => {}
        }
    }

    for (vpath, orig) in &original_texts {
        if let Some(vfile) = pkg.files.get(vpath)
            && let Ok(sf) =
                SourceFile::from_bytes(FileId::from_path(vpath), vpath.clone(), &vfile.bytes)
            && sf.text() != orig
        {
            report.modified_files.push(FileDiff {
                path: vpath.to_string_lossy().replace('\\', "/"),
                original: orig.clone(),
                updated: sf.text().to_owned(),
            });
        }
    }

    if options.dry_run {
        for (vpath, raw) in original_raw {
            pkg.insert(vpath, raw);
        }
    }

    report
}

fn render_diag_string(diag: &Diagnostic, sources: &SourceMap) -> String {
    let mut buf = Vec::new();
    let _ = diag.render(sources, &mut buf);
    String::from_utf8_lossy(&buf).into_owned()
}

fn render_lint_string(diag: &ril_lint::LintDiagnostic, sources: &SourceMap) -> String {
    let mut buf = Vec::new();
    let _ = diag.render_with_color(sources, false, &mut buf);
    String::from_utf8_lossy(&buf).into_owned()
}

fn is_editable_vpath(vpath: &Path) -> bool {
    let first = vpath.iter().next().and_then(std::ffi::OsStr::to_str);
    if first != Some("pkg") {
        return false;
    }
    let name = vpath.to_string_lossy();
    name.ends_with(".ril") && !name.ends_with(".d.ril")
}

fn hash_editable_files(pkg: &VirtualPackage) -> [u8; 32] {
    let mut buf = Vec::new();
    for (vpath, vfile) in &pkg.files {
        if is_editable_vpath(vpath) {
            buf.extend_from_slice(vpath.to_string_lossy().as_bytes());
            buf.push(0);
            buf.extend_from_slice(&vfile.bytes);
            buf.push(0);
        }
    }
    sha256(&buf)
}

fn editable_file_ids(partial: &PartialAnalysis, pkg: &VirtualPackage) -> BTreeSet<FileId> {
    pkg.files
        .keys()
        .filter(|p| is_editable_vpath(p))
        .filter_map(|p| {
            let id = FileId::from_path(p);
            partial.sources.get(id).map(|_| id)
        })
        .collect()
}

fn all_edits_editable(edits: &[TextEdit], partial: &PartialAnalysis, pkg: &VirtualPackage) -> bool {
    edits.iter().all(|e| {
        partial
            .sources
            .get(e.span.file)
            .is_some_and(|sf| is_editable_vpath(sf.path()) && pkg.files.contains_key(sf.path()))
    })
}

fn first_edit_path(fix: &Fix, partial: &PartialAnalysis) -> String {
    fix.edits
        .first()
        .and_then(|e| partial.sources.get(e.span.file))
        .map(|sf| sf.path().to_string_lossy().replace('\\', "/"))
        .unwrap_or_default()
}

fn select_non_overlapping(candidates: Vec<CandidateFix>) -> Vec<CandidateFix> {
    let mut occupied: BTreeMap<FileId, Vec<(usize, usize)>> = BTreeMap::new();
    let mut chosen = Vec::new();
    for cand in candidates {
        let conflicts = cand.fix.edits.iter().any(|edit| {
            occupied.get(&edit.span.file).is_some_and(|ranges| {
                ranges
                    .iter()
                    .any(|&(s, e)| spans_overlap(s, e, edit.span.start, edit.span.end))
            })
        });
        if conflicts {
            continue;
        }
        for edit in &cand.fix.edits {
            occupied
                .entry(edit.span.file)
                .or_default()
                .push((edit.span.start, edit.span.end));
        }
        chosen.push(cand);
    }
    chosen
}

const fn spans_overlap(a_start: usize, a_end: usize, b_start: usize, b_end: usize) -> bool {
    if a_start == a_end && b_start == b_end {
        return a_start == b_start;
    }
    a_start < b_end && b_start < a_end
}

fn error_codes_of(partial: &PartialAnalysis) -> BTreeMap<String, usize> {
    let mut counts = BTreeMap::new();
    for d in &partial.diagnostics {
        if d.severity == Severity::Error {
            let code = d.code.map_or("ERR", Code::as_str).to_owned();
            *counts.entry(code).or_insert(0) += 1;
        }
    }
    counts
}

fn containment_regression(
    before: &BTreeMap<String, usize>,
    after: &BTreeMap<String, usize>,
) -> Option<&'static str> {
    for code in [
        "E0608", "E0616", "E0625", "E0526", "E0523", "E0524", "E0409", "E0910",
    ] {
        let prev = before.get(code).copied().unwrap_or(0);
        let next = after.get(code).copied().unwrap_or(0);
        if next > prev {
            return Some(code);
        }
    }
    None
}

fn apply_edits_to_package(
    pkg: &VirtualPackage,
    partial: &PartialAnalysis,
    fixes: &[&CandidateFix],
) -> Option<VirtualPackage> {
    let mut by_file: BTreeMap<FileId, Vec<&TextEdit>> = BTreeMap::new();
    for cand in fixes {
        for edit in &cand.fix.edits {
            by_file.entry(edit.span.file).or_default().push(edit);
        }
    }
    let mut next_pkg = pkg.clone();
    for (file_id, mut edits) in by_file {
        let sf = partial.sources.get(file_id)?;
        let mut text = sf.text().to_owned();
        edits.sort_by_key(|b| std::cmp::Reverse((b.span.start, b.span.end)));
        for edit in edits {
            if edit.span.start > edit.span.end
                || edit.span.end > text.len()
                || !text.is_char_boundary(edit.span.start)
                || !text.is_char_boundary(edit.span.end)
            {
                return None;
            }
            text.replace_range(edit.span.start..edit.span.end, &edit.replacement);
        }
        next_pkg.insert(sf.path().to_path_buf(), text.into_bytes());
    }
    Some(next_pkg)
}

fn batch_is_safe(
    compiler: &Compiler,
    candidate_pkg: &VirtualPackage,
    baseline_errors: &BTreeMap<String, usize>,
    has_unsafe: bool,
) -> Result<(), String> {
    let check = compiler.analyze_partial_with_mode(candidate_pkg, AnalysisMode::Check);
    if check.stage == "parse" {
        return Err("edit introduced syntax error".into());
    }
    let after_errors = error_codes_of(&check);
    if let Some(code) = containment_regression(baseline_errors, &after_errors) {
        return Err(format!("edit introduced containment error {code}"));
    }
    if has_unsafe {
        let prev_total: usize = baseline_errors.values().sum();
        let next_total: usize = after_errors.values().sum();
        if next_total > prev_total {
            return Err("unsafe edit increased compiler error count".into());
        }
    }
    Ok(())
}

fn apply_with_guardrails(
    compiler: &Compiler,
    pkg: &mut VirtualPackage,
    partial: &PartialAnalysis,
    selected: Vec<CandidateFix>,
    baseline_errors: &BTreeMap<String, usize>,
    skipped: &mut Vec<SkippedFix>,
) -> (Vec<CandidateFix>, usize) {
    let refs: Vec<&CandidateFix> = selected.iter().collect();
    let has_unsafe = selected.iter().any(|c| c.fix.safety == FixSafety::Unsafe);
    if let Some(candidate_pkg) = apply_edits_to_package(pkg, partial, &refs)
        && batch_is_safe(compiler, &candidate_pkg, baseline_errors, has_unsafe).is_ok()
    {
        *pkg = candidate_pkg;
        return (selected, 0);
    }

    // Batch regressed — isolate individually and keep only non-regressing fixes.
    let mut accepted = Vec::new();
    let mut dropped = 0;
    for cand in selected {
        let single_unsafe = cand.fix.safety == FixSafety::Unsafe;
        let Some(candidate_pkg) = apply_edits_to_package(pkg, partial, &[&cand]) else {
            dropped += 1;
            continue;
        };
        match batch_is_safe(compiler, &candidate_pkg, baseline_errors, single_unsafe) {
            Ok(()) => {
                // Only commit single fix if it does not conflict with already-accepted edits;
                // because `selected` is already non-overlapping, re-applying accepted + cand together works.
                accepted.push(cand);
                let acc_refs: Vec<&CandidateFix> = accepted.iter().collect();
                if let Some(combined) = apply_edits_to_package(pkg, partial, &acc_refs)
                    && batch_is_safe(
                        compiler,
                        &combined,
                        baseline_errors,
                        accepted.iter().any(|c| c.fix.safety == FixSafety::Unsafe),
                    )
                    .is_ok()
                {
                    continue;
                }
                if let Some(bad) = accepted.pop() {
                    dropped += 1;
                    skipped.push(SkippedFix {
                        file: first_edit_path(&bad.fix, partial),
                        code: bad.code,
                        title: bad.fix.title,
                        safety: bad.fix.safety,
                        reason: "rolled back: conflicted with another fix in pass".into(),
                        capability_delta: bad.fix.delta,
                    });
                }
            }
            Err(reason) => {
                dropped += 1;
                skipped.push(SkippedFix {
                    file: first_edit_path(&cand.fix, partial),
                    code: cand.code,
                    title: cand.fix.title,
                    safety: cand.fix.safety,
                    reason: format!("rolled back: {reason}"),
                    capability_delta: cand.fix.delta,
                });
            }
        }
    }
    if !accepted.is_empty() {
        let acc_refs: Vec<&CandidateFix> = accepted.iter().collect();
        if let Some(combined) = apply_edits_to_package(pkg, partial, &acc_refs) {
            *pkg = combined;
        }
    }
    (accepted, dropped)
}

/// Phase A: collects compiler diagnostic fixes (`E0405`, `E0406`, `E0338`, `E0810`, missing stdlib `use ril/...`).
fn collect_compiler_fixes(partial: &PartialAnalysis, out: &mut Vec<CandidateFix>) {
    let mut added_imports: BTreeSet<(FileId, &'static str)> = BTreeSet::new();
    for diag in &partial.diagnostics {
        let code = diag.code.map_or("ERR", Code::as_str).to_owned();
        for fix in diag.fixes() {
            out.push(CandidateFix {
                code: code.clone(),
                priority: 0,
                fix: fix.clone(),
            });
        }
        // Synthesize missing stdlib `use ril/...` import on E0204 for well-known stdlib modules.
        if diag.code == Some(Code::E0204)
            && let Some(primary) = diag.primary
            && let Some(sf) = partial.sources.get(primary.file)
            && let Some(token) = sf.text().get(primary.start..primary.end)
            && let Some(std_mod) = stdlib_module_for_symbol(token)
            && added_imports.insert((primary.file, std_mod))
            && !file_has_import(partial, primary.file, std_mod)
        {
            let insert_at = import_insert_offset(sf, partial.typed.as_deref().map(|t| &t.hir));
            let line = format!("use {std_mod}\n");
            out.push(CandidateFix {
                code: code.clone(),
                priority: 0,
                fix: Fix {
                    id: format!("import_{std_mod}"),
                    title: format!("Import `{std_mod}`"),
                    safety: FixSafety::Safe,
                    kind: FixKind::MissingImport,
                    is_preferred: true,
                    is_organize_imports: false,
                    edits: vec![TextEdit {
                        span: Span::new(primary.file, insert_at, insert_at),
                        replacement: line,
                    }],
                    delta: None,
                },
            });
        }
    }
}

fn stdlib_module_for_symbol(ident: &str) -> Option<&'static str> {
    match ident {
        "Io" => Some("ril/io"),
        "File" => Some("ril/file"),
        "Math" => Some("ril/math"),
        "Panic" => Some("ril/panic"),
        "Async" | "Task" | "Clock" | "Net" => Some("ril/async"),
        "Reflect" => Some("ril/reflect"),
        "Array" => Some("ril/array"),
        "Map" => Some("ril/map"),
        "Set" => Some("ril/set"),
        "String" => Some("ril/string"),
        "Bytes" => Some("ril/bytes"),
        "Numeric" => Some("ril/numeric"),
        _ => None,
    }
}

fn file_has_import(partial: &PartialAnalysis, file_id: FileId, module: &str) -> bool {
    let Some(sf) = partial.sources.get(file_id) else {
        return false;
    };
    let needle = format!("use {module}");
    sf.text()
        .lines()
        .any(|line| line.trim_start().starts_with(&needle))
}

/// Computes a CST-safe byte offset for inserting a new `use ...` import line,
/// never splitting a doc comment from its following declaration.
pub fn import_insert_offset(sf: &SourceFile, hir: Option<&Program>) -> usize {
    let text = sf.text();
    if let Some(hir) = hir
        && let Some(file) = hir.files().find(|f| f.id == sf.id())
    {
        let mut last_import_end: Option<usize> = None;
        for &stmt_id in &file.ast.items {
            let node = file.ast.stmt(stmt_id);
            if matches!(node.value.kind, StmtKind::Import(_)) {
                last_import_end = Some(node.span.end);
            }
        }
        if let Some(end) = last_import_end {
            if let Some(nl) = text.get(end..).and_then(|s| s.find('\n')) {
                return end + nl + 1;
            }
            return text.len();
        }
        if let Some(&first_item) = file.ast.items.first() {
            let item_start = file.ast.stmt(first_item).span.start;
            let prefix = text.get(..item_start).unwrap_or("");
            // Walk backward over consecutive `--` doc comment lines immediately preceding `first_item`.
            let mut cut = item_start;
            let mut offset = 0usize;
            let mut lines: Vec<(usize, &str)> = Vec::new();
            for line in prefix.split_inclusive('\n') {
                lines.push((offset, line));
                offset += line.len();
            }
            while let Some(&(line_start, line_text)) = lines.last() {
                let trimmed = line_text.trim();
                if trimmed.starts_with("--")
                    && !ril_syntax::directive::is_lint_directive_comment(trimmed)
                    && !trimmed.starts_with("-- @")
                {
                    cut = line_start;
                    lines.pop();
                } else {
                    break;
                }
            }
            return cut;
        }
    }
    // Fallback: skip leading `-- @` / `-- ril:` directives.
    let mut offset = 0usize;
    for line in text.split_inclusive('\n') {
        let trimmed = line.trim();
        if trimmed.starts_with("-- @") || ril_syntax::directive::is_lint_directive_comment(trimmed)
        {
            offset += line.len();
        } else {
            break;
        }
    }
    offset
}

/// Phase B1: Synthesizes signature synchronization fixes from `Analysis.fix_meta`.
fn synthesize_signature_fixes(
    partial: &PartialAnalysis,
    _options: &FixOptions,
) -> (Vec<CandidateFix>, Vec<SkippedFix>) {
    let mut candidates = Vec::new();
    let mut skipped = Vec::new();
    let (Some(typed), Some(analysis)) = (&partial.typed, &partial.analysis) else {
        return (candidates, skipped);
    };

    // Detect functions whose callers hit E0518/E0520/E0522 requiring `-> new`.
    let need_new_defs = functions_needing_new_return(partial, typed);

    for (&def_id, inferred) in &analysis.fix_meta.inferred_sigs {
        let def = typed.hir.definition(def_id);
        let file_id = def.name.span.file;
        if typed.hir.is_stdlib_file(file_id) || typed.hir.file(file_id).is_interface() {
            continue;
        }
        let Some(stmt_id) = def.stmt else {
            continue;
        };
        let file = typed.hir.file(file_id);
        let StmtKind::Function(fun) = &file.ast.stmt(stmt_id).value.kind else {
            continue;
        };
        let Some(body_id) = fun.body else {
            continue;
        };
        let Some(callable) = typed.callables.get(&def_id) else {
            continue;
        };
        if inferred.is_meta {
            continue;
        }

        let symbol_name = def.name.value.clone();
        let vis_str = visibility_str(inferred.visibility);
        let can_strip = !inferred.has_holes && !inferred.has_pruned_meta && !inferred.has_via;
        let mut added: Vec<String> = Vec::new();
        let mut removed: Vec<String> = Vec::new();
        let mut causal_chain: Vec<String> = Vec::new();

        // 1. Effects reconciliation.
        let mut target_effects: Vec<String> = Vec::new();
        let mut extra_imports: Vec<TextEdit> = Vec::new();
        let mut existing_effect_kept: Vec<String> = Vec::new();

        // Keep existing declared effects that are still exercised (or if stripping is forbidden).
        for (idx, decl_eff) in callable.effects.iter().enumerate() {
            let exercised = inferred
                .effects
                .iter()
                .any(|actual| typed.effect_covers(decl_eff, actual));
            let surface = fun
                .signature
                .obligations
                .effect_spans
                .get(idx)
                .and_then(|sp| file.source_text().get(sp.start..sp.end))
                .map(|s| s.trim_start_matches('@').to_owned())
                .unwrap_or_else(|| format_effect_fallback(decl_eff));
            if exercised || !can_strip {
                existing_effect_kept.push(decl_eff.clone());
                target_effects.push(surface);
            } else {
                removed.push(format!("@{surface}"));
            }
        }

        // Add missing inferred effects.
        let mut unspellable_or_blocked = false;
        for eff_label in &inferred.effects {
            if existing_effect_kept
                .iter()
                .any(|d| typed.effect_covers(d, eff_label))
            {
                continue;
            }
            if inferred.is_main && eff_label != "io" {
                skipped.push(SkippedFix {
                    file: file.path.to_string_lossy().replace('\\', "/"),
                    code: "E0612".into(),
                    title: format!("Cannot add user effect `@{eff_label}` to `fn main`"),
                    safety: FixSafety::Assist,
                    reason: "`fn main` may only declare `@io`; handle user effects with `with`"
                        .into(),
                    capability_delta: None,
                });
                unspellable_or_blocked = true;
                continue;
            }
            match format_effect_for_scope(typed, def_id, inferred.visibility, eff_label) {
                EffectSpelling::Spelled { surface, import } => {
                    added.push(format!("@{surface}"));
                    target_effects.push(surface);
                    if let Some(chain) = inferred.effect_causes.get(eff_label)
                        && causal_chain.is_empty()
                    {
                        causal_chain = chain.clone();
                    }
                    if let Some(mod_path) = import
                        && !file_has_import(partial, file_id, &mod_path)
                    {
                        let insert_at = import_insert_offset(file.source(), Some(&typed.hir));
                        extra_imports.push(TextEdit {
                            span: Span::new(file_id, insert_at, insert_at),
                            replacement: format!("use {mod_path}\n"),
                        });
                    }
                }
                EffectSpelling::Blocked(reason) => {
                    skipped.push(SkippedFix {
                        file: file.path.to_string_lossy().replace('\\', "/"),
                        code: "E0612".into(),
                        title: format!("Sync effect `@{eff_label}` on `fn {symbol_name}`"),
                        safety: FixSafety::Contract,
                        reason,
                        capability_delta: None,
                    });
                    unspellable_or_blocked = true;
                }
            }
        }
        let _ = unspellable_or_blocked;

        // Canonical sort of effects: `io` first, then alphabetical, deduplicated.
        target_effects.sort_by(|a, b| (a != "io", a.as_str()).cmp(&(b != "io", b.as_str())));
        target_effects.dedup();

        // 2. State clauses reconciliation.
        let decl_shared = callable.state.iter().any(|s| s == "^mut");
        let decl_capture = callable.state.iter().any(|s| s == "capture");

        let want_shared = inferred.needs_shared_mut || (!can_strip && decl_shared);
        let want_capture = inferred.needs_capture || (!can_strip && decl_capture);

        if want_shared && !decl_shared {
            added.push("&^mut".into());
        } else if !want_shared && decl_shared {
            removed.push("&^mut".into());
        }
        if want_capture && !decl_capture {
            added.push("&capture".into());
        } else if !want_capture && decl_capture {
            removed.push("&capture".into());
        }

        // `&up(...)` for local where functions.
        let declared_up: Vec<String> = fun
            .signature
            .obligations
            .state
            .iter()
            .filter(|c| c.kind == StateKind::Environment)
            .flat_map(|c| &c.bindings)
            .map(|(st, p)| format_binding_spec(st.variable, st.mode, &p.segments_text()))
            .collect();
        let target_up: Vec<String> = if inferred.is_local_where {
            let mut items: Vec<String> = inferred
                .up_captures
                .iter()
                .map(|u| format_binding_spec(u.variable, u.mode, &u.name))
                .collect();
            if !can_strip {
                for existing in &declared_up {
                    if !items.contains(existing) {
                        items.push(existing.clone());
                    }
                }
            }
            items.sort();
            items.dedup();
            items
        } else {
            declared_up.clone()
        };
        if target_up != declared_up {
            for item in &target_up {
                if !declared_up.contains(item) {
                    added.push(format!("&up({item})"));
                }
            }
            for item in &declared_up {
                if !target_up.contains(item) {
                    removed.push(format!("&up({item})"));
                }
            }
        }

        // `&return(...)` preservation / sync.
        let declared_return: Vec<String> = fun
            .signature
            .obligations
            .state
            .iter()
            .filter(|c| c.kind == StateKind::Return)
            .flat_map(|c| &c.bindings)
            .map(|(st, p)| format_binding_spec(false, st.mode, &p.segments_text()))
            .collect();
        let target_return: Vec<String> =
            if !matches!(fun.signature.result_mode, Mode::Plain | Mode::Infer) {
                let mut items: Vec<String> = inferred
                    .return_contained
                    .iter()
                    .map(|(acc, name)| format_binding_spec(false, access_to_mode(*acc), name))
                    .collect();
                if !can_strip {
                    for existing in &declared_return {
                        if !items.contains(existing) {
                            items.push(existing.clone());
                        }
                    }
                }
                items.sort();
                items.dedup();
                items
            } else {
                declared_return.clone()
            };
        if target_return != declared_return {
            for item in &target_return {
                if !declared_return.contains(item) {
                    added.push(format!("&return({item})"));
                }
            }
            for item in &declared_return {
                if !target_return.contains(item) {
                    removed.push(format!("&return({item})"));
                }
            }
        }

        // 3. `-> new` return mode addition (only when needed by a diagnostic / caller).
        let has_arrow = fun.signature.arrow_span.end > fun.signature.arrow_span.start;
        let want_add_new = inferred.return_mode == Some(InferredReturnMode::New)
            && fun.signature.result_mode == Mode::Plain
            && has_arrow
            && need_new_defs.contains(&def_id);
        if want_add_new {
            added.push("-> new".into());
        }

        if added.is_empty() && removed.is_empty() {
            continue;
        }

        // Build exact edits.
        let mut edits = Vec::new();
        edits.extend(extra_imports);

        let obligations_changed = added.iter().any(|s| s != "-> new") || !removed.is_empty();
        if obligations_changed {
            if let Some(ob_edit) = build_obligation_edit(
                file.source(),
                &file.ast,
                fun,
                body_id,
                &target_effects,
                want_shared,
                want_capture,
                &target_up,
                &target_return,
            ) {
                edits.push(ob_edit);
            } else {
                skipped.push(SkippedFix {
                    file: file.path.to_string_lossy().replace('\\', "/"),
                    code: "E0612".into(),
                    title: format!("Sync signature obligations on `fn {symbol_name}`"),
                    safety: FixSafety::Assist,
                    reason: "signature obligation span contains inline comments; edit skipped to preserve comments".into(),
                    capability_delta: None,
                });
                continue;
            }
        }

        if want_add_new && has_arrow {
            let arrow_span = fun.signature.arrow_span;
            let text = file.source_text();
            let after_arrow = text.get(arrow_span.end..).unwrap_or("");
            let ws = after_arrow.len() - after_arrow.trim_start_matches([' ', '\t']).len();
            let insert_pos = arrow_span.end + ws;
            edits.push(TextEdit {
                span: Span::new(file_id, insert_pos, insert_pos),
                replacement: "new ".into(),
            });
        }

        if edits.is_empty() {
            continue;
        }

        let is_public_or_pkg = !inferred.is_local_where
            && !inferred.is_main
            && matches!(
                inferred.visibility,
                Visibility::Package | Visibility::Public
            );
        let safety = if is_public_or_pkg {
            FixSafety::Contract
        } else {
            FixSafety::Safe
        };

        let delta = CapabilityDelta {
            symbol: symbol_name.clone(),
            visibility: vis_str.to_owned(),
            added: added.clone(),
            removed: removed.clone(),
            causal_chain,
        };
        let summary_parts: Vec<String> = added
            .iter()
            .map(|a| format!("+{a}"))
            .chain(removed.iter().map(|r| format!("-{r}")))
            .collect();
        let code = if added.iter().any(|s| s.starts_with('@')) {
            "E0612"
        } else if !added.is_empty() {
            "E0510"
        } else if removed.iter().any(|s| s.starts_with('@')) {
            "E0626"
        } else {
            "E0529"
        };

        candidates.push(CandidateFix {
            code: code.into(),
            priority: 1,
            fix: Fix {
                id: format!("sync_sig_{symbol_name}"),
                title: format!(
                    "Sync signature of `fn {symbol_name}` ({})",
                    summary_parts.join(", ")
                ),
                safety,
                kind: FixKind::SignatureSync,
                is_preferred: safety == FixSafety::Safe,
                is_organize_imports: false,
                edits,
                delta: Some(delta),
            },
        });
    }

    (candidates, skipped)
}

#[allow(clippy::too_many_arguments)]
fn build_obligation_edit(
    sf: &SourceFile,
    ast: &Ast,
    fun: &Function,
    body_id: ril_syntax::syntax::ExprId,
    effects: &[String],
    want_shared: bool,
    want_capture: bool,
    up_items: &[String],
    return_items: &[String],
) -> Option<TextEdit> {
    let start = fun.signature.params_close_span.end;
    let has_arrow = fun.signature.arrow_span.end > fun.signature.arrow_span.start;
    let end = if has_arrow {
        fun.signature.arrow_span.start
    } else {
        ast.expr(body_id).span.start
    };
    if start > end || end > sf.text().len() {
        return None;
    }
    let slice = sf.text().get(start..end)?;
    // Comment safety: never destroy comments embedded between `)` and `->` / `{`.
    if slice.contains("--") {
        return None;
    }
    let mut parts: Vec<String> = Vec::new();
    for eff in effects {
        parts.push(format!("@{eff}"));
    }
    if want_shared {
        parts.push("&^mut".into());
    }
    if want_capture {
        parts.push("&capture".into());
    }
    if !up_items.is_empty() {
        parts.push(format!("&up({})", up_items.join(", ")));
    }
    if !return_items.is_empty() {
        parts.push(format!("&return({})", return_items.join(", ")));
    }
    let replacement = if parts.is_empty() {
        " ".to_owned()
    } else {
        format!(" {} ", parts.join(" "))
    };
    if slice == replacement {
        return None;
    }
    Some(TextEdit {
        span: Span::new(sf.id(), start, end),
        replacement,
    })
}

fn functions_needing_new_return(
    partial: &PartialAnalysis,
    typed: &TypedProgram,
) -> BTreeSet<DefinitionId> {
    let mut out = BTreeSet::new();
    for diag in &partial.diagnostics {
        if !matches!(
            diag.code,
            Some(Code::E0520 | Code::E0522 | Code::E0544 | Code::E0546 | Code::E0548)
        ) {
            continue;
        }
        let Some(span) = diag.primary else {
            continue;
        };
        // Check if `span` is inside a function body or covers a call to a function.
        for (_, def_id) in typed.hir.references_within(span) {
            if typed.hir.definition(def_id).kind == DefinitionKind::Function {
                out.insert(def_id);
            }
        }
        // Also check enclosing function for E0544/E0546/E0548.
        if matches!(diag.code, Some(Code::E0544 | Code::E0546 | Code::E0548)) {
            for &def_id in typed.callables.keys() {
                let def = typed.hir.definition(def_id);
                if def.name.span.file == span.file
                    && let Some(stmt) = def.stmt
                {
                    let stmt_span = typed.hir.file(span.file).ast.stmt(stmt).span;
                    if span.start >= stmt_span.start && span.end <= stmt_span.end {
                        out.insert(def_id);
                    }
                }
            }
        }
    }
    out
}

enum EffectSpelling {
    Spelled {
        surface: String,
        import: Option<String>,
    },
    Blocked(String),
}

/// Formats a canonical internal effect label into the shortest valid surface path in `fn_def`'s scope.
fn format_effect_for_scope(
    typed: &TypedProgram,
    fn_def_id: DefinitionId,
    fn_vis: Visibility,
    eff_label: &str,
) -> EffectSpelling {
    if eff_label == "io" {
        return EffectSpelling::Spelled {
            surface: "io".into(),
            import: None,
        };
    }
    if eff_label.contains('#') {
        return EffectSpelling::Blocked(
            "local block effect cannot escape into function signature (E0618)".into(),
        );
    }
    let Some(eff_def_id) = typed.hir.effect_by_label(eff_label) else {
        return EffectSpelling::Blocked(format!("effect `{eff_label}` cannot be resolved"));
    };
    let eff_def = typed.hir.definition(eff_def_id);
    let fn_def = typed.hir.definition(fn_def_id);

    // Visibility check (E0910): public/pkg signature cannot expose a less-visible effect.
    if fn_vis > eff_def.visibility && !matches!(fn_vis, Visibility::Private) {
        return EffectSpelling::Blocked(format!(
            "effect `{}` has `{}` visibility and cannot appear in `{}` signature (E0910)",
            eff_def.name.value,
            visibility_str(eff_def.visibility),
            visibility_str(fn_vis),
        ));
    }

    // 1. Direct or `Super::` chain lookup in scope hierarchy.
    let mut cur_scope = fn_def.scope;
    let mut super_depth = 0usize;
    loop {
        for (name, res, _) in typed.hir.scope_entries(cur_scope) {
            if res == Resolution::Definition(eff_def_id) {
                let prefix = "Super::".repeat(super_depth);
                return EffectSpelling::Spelled {
                    surface: format!("{prefix}{name}"),
                    import: None,
                };
            }
            if let Resolution::Module(mod_scope) = res {
                for (sub_name, sub_res, _) in typed.hir.scope_entries(mod_scope) {
                    if sub_res == Resolution::Definition(eff_def_id) {
                        let prefix = "Super::".repeat(super_depth);
                        return EffectSpelling::Spelled {
                            surface: format!("{prefix}{name}::{sub_name}"),
                            import: None,
                        };
                    }
                }
            }
        }
        if let Some(parent) = typed.hir.scope_parent(cur_scope) {
            cur_scope = parent;
            super_depth += 1;
        } else {
            break;
        }
    }

    // 2. Check module root scope of the defining file (in case `fn_def` is inside a `where` helper).
    let file_scope = typed.hir.module_scope(fn_def.name.span.file);
    for (name, res, _) in typed.hir.scope_entries(file_scope) {
        if res == Resolution::Definition(eff_def_id) {
            return EffectSpelling::Spelled {
                surface: name,
                import: None,
            };
        }
        if let Resolution::Module(mod_scope) = res {
            for (sub_name, sub_res, _) in typed.hir.scope_entries(mod_scope) {
                if sub_res == Resolution::Definition(eff_def_id) {
                    return EffectSpelling::Spelled {
                        surface: format!("{name}::{sub_name}"),
                        import: None,
                    };
                }
            }
        }
    }

    // 3. Same-package module import synthesis (`use pkg/...`).
    let eff_file = typed.hir.file(eff_def.name.span.file);
    if typed
        .hir
        .is_visible(eff_def.scope, file_scope, eff_def.visibility)
        && let Some(mod_path) = module_import_path(&eff_file.path)
        && let Some(mod_ident) = eff_file
            .path
            .file_stem()
            .and_then(std::ffi::OsStr::to_str)
            .map(pascal_case)
    {
        return EffectSpelling::Spelled {
            surface: format!("{mod_ident}::{}", eff_def.name.value),
            import: Some(mod_path),
        };
    }

    EffectSpelling::Blocked(format!(
        "effect `{}` is not reachable or visible from `fn {}`",
        eff_def.name.value, fn_def.name.value
    ))
}

fn module_import_path(path: &Path) -> Option<String> {
    let norm = path.to_string_lossy().replace('\\', "/");
    let stripped = norm.strip_suffix(".ril")?;
    if stripped.starts_with("pkg/") || stripped.starts_with("ril/") {
        Some(stripped.to_owned())
    } else {
        None
    }
}

fn pascal_case(raw: &str) -> String {
    let mut out = String::new();
    let mut cap = true;
    for ch in raw.chars() {
        if ch == '_' || ch == '-' {
            cap = true;
        } else if cap {
            out.extend(ch.to_uppercase());
            cap = false;
        } else {
            out.push(ch);
        }
    }
    out
}

fn format_effect_fallback(label: &str) -> String {
    label.rsplit("::").next().unwrap_or(label).to_owned()
}

fn format_binding_spec(variable: bool, mode: Mode, name: &str) -> String {
    let mut parts = Vec::new();
    if variable {
        parts.push("var");
    }
    if let Some(m) = mode.as_str() {
        parts.push(m);
    }
    parts.push(name);
    parts.join(" ")
}

const fn access_to_mode(access: Access) -> Mode {
    match access {
        Access::Immutable => Mode::Plain,
        Access::Ref => Mode::Ref,
        Access::Mut => Mode::Mut,
        Access::Shared => Mode::Shared,
    }
}

const fn visibility_str(vis: Visibility) -> &'static str {
    match vis {
        Visibility::Private => "private",
        Visibility::Package => "pkg",
        Visibility::Public => "pub",
    }
}

trait PathExt {
    fn segments_text(&self) -> String;
}

impl PathExt for ril_syntax::syntax::Path {
    fn segments_text(&self) -> String {
        self.segments
            .iter()
            .map(|s| s.name.value.as_str())
            .collect::<Vec<_>>()
            .join("::")
    }
}

/// Ensures `lexer` is available if needed for future token-level checks.
#[allow(dead_code)]
fn _lex_keepalive(sf: &SourceFile) -> usize {
    lexer::lex_with_recovery(sf).tokens.len()
}
