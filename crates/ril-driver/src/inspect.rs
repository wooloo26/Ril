//! Unified static inspection & provenance projection shared by `ril inspect` (AI-first JSON CLI)
//! and `ril-lsp` (Hover and Inlay Hints).

use std::collections::{BTreeMap, BTreeSet};

use ril_hir::{DefinitionId, DefinitionKind, Program};
use ril_sema::{
    access::{Analysis, Input, Summary},
    behavior::{WitnessStep, is_pure, is_total},
    ty::{Callable, Ty, TypedProgram},
};
use ril_source::{
    diag::{Diagnostic, Severity},
    span::{FileId, SourceFile, SourceMap, Span},
};
use ril_syntax::syntax::{Mode, StmtKind};
use serde::Serialize;

use crate::PartialAnalysis;

pub const SCHEMA_VERSION: u32 = 1;

/// Reserved `--include` section names for future AI-first deep queries.
const RESERVED_INCLUDES: &[&str] = &[
    "types",
    "locals",
    "stdlib",
    "via_domains",
    "call_graph",
    "provenance",
    "effect_flow",
    "ownership",
    "horn",
    "mir_summary",
];

const SUPPORTED_INCLUDES: &[&str] = &["fix_hints"];

#[derive(Clone, Debug, Default)]
pub struct AtQuery {
    pub file: Option<String>,
    pub start_line: usize,
    pub end_line: usize,
    pub col: Option<usize>,
}

impl AtQuery {
    /// Parses `<file>:<line>`, `<file>:<line>:<col>`, `<file>:<start>-<end>`, or without `<file>:`.
    pub fn parse(raw: &str) -> Result<Self, String> {
        let trimmed = raw.trim();
        if trimmed.is_empty() {
            return Err("empty --at location".into());
        }
        // Split optional `<file>:` prefix (note: Windows paths could contain `C:\`, so scan right).
        let parts: Vec<&str> = trimmed.split(':').collect();
        let (file, loc_part, col_part) = match parts.as_slice() {
            [line_or_range] => (None, *line_or_range, None),
            [first, second] => {
                if first.chars().all(|c| c.is_ascii_digit()) {
                    (None, *first, Some(*second))
                } else {
                    (Some((*first).to_owned()), *second, None)
                }
            }
            [first @ .., line_or_range, col]
                if line_or_range
                    .chars()
                    .all(|c| c.is_ascii_digit() || c == '-')
                    && col.chars().all(|c| c.is_ascii_digit()) =>
            {
                let f = first.join(":");
                ((!f.is_empty()).then_some(f), *line_or_range, Some(*col))
            }
            [first @ .., line_or_range] => {
                let f = first.join(":");
                ((!f.is_empty()).then_some(f), *line_or_range, None)
            }
            [] => return Err(format!("invalid --at location `{raw}`")),
        };

        let (start_line, end_line) = if let Some((s, e)) = loc_part.split_once('-') {
            let start = s
                .parse::<usize>()
                .map_err(|_| format!("invalid line in --at `{raw}`"))?;
            let end = e
                .parse::<usize>()
                .map_err(|_| format!("invalid end line in --at `{raw}`"))?;
            if start == 0 || end < start {
                return Err(format!("invalid line range in --at `{raw}`"));
            }
            (start, end)
        } else {
            let line = loc_part
                .parse::<usize>()
                .map_err(|_| format!("invalid line in --at `{raw}`"))?;
            if line == 0 {
                return Err(format!("lines in --at are 1-based (`{raw}`)"));
            }
            (line, line)
        };
        let col = match col_part {
            Some(c) => {
                let parsed = c
                    .parse::<usize>()
                    .map_err(|_| format!("invalid column in --at `{raw}`"))?;
                if parsed == 0 {
                    return Err(format!("columns in --at are 1-based (`{raw}`)"));
                }
                Some(parsed)
            }
            None => None,
        };
        Ok(Self {
            file,
            start_line,
            end_line,
            col,
        })
    }
}

#[derive(Clone, Debug, Default)]
pub struct InspectQuery {
    pub files: Vec<String>,
    pub symbols: Vec<String>,
    pub at: Vec<AtQuery>,
    pub symbols_only: bool,
    pub includes: Vec<String>,
}

impl InspectQuery {
    pub fn wants_fix_hints(&self) -> bool {
        self.includes
            .iter()
            .flat_map(|raw| raw.split(','))
            .map(str::trim)
            .any(|item| item == "fix_hints")
    }

    pub fn validate(&self) -> Result<(), String> {
        for raw in &self.includes {
            for item in raw.split(',').map(str::trim).filter(|s| !s.is_empty()) {
                if SUPPORTED_INCLUDES.contains(&item) {
                    continue;
                }
                if RESERVED_INCLUDES.contains(&item) {
                    return Err(format!(
                        "--include section `{item}` is reserved and not yet implemented"
                    ));
                }
                return Err(format!("unknown --include section `{item}`"));
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct InspectFixEdit {
    pub loc: String,
    pub start: usize,
    pub end: usize,
    pub replacement: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct InspectFixHint {
    pub code: String,
    pub title: String,
    pub safety: ril_source::fix::FixSafety,
    pub kind: ril_source::fix::FixKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub capability_delta: Option<ril_source::fix::CapabilityDelta>,
    pub edits: Vec<InspectFixEdit>,
}

#[derive(Clone, Debug, Serialize)]
pub struct InspectReport {
    pub schema_version: u32,
    pub ok: bool,
    pub stage: &'static str,
    pub files: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<InspectDiagnostic>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub symbols: Vec<SymbolFact>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub sites: Vec<SiteFact>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub fix_hints: Vec<InspectFixHint>,
}

impl InspectReport {
    pub fn to_json(&self, pretty: bool) -> String {
        if pretty {
            serde_json::to_string_pretty(self)
        } else {
            serde_json::to_string(self)
        }
        .unwrap_or_else(|err| ril_source::ice!("inspect JSON serialization failed: {err}"))
    }

    pub fn fatal_json(message: &str, pretty: bool) -> String {
        #[derive(Serialize)]
        struct Fatal<'a> {
            schema_version: u32,
            ok: bool,
            fatal: &'a str,
        }
        let payload = Fatal {
            schema_version: SCHEMA_VERSION,
            ok: false,
            fatal: message,
        };
        if pretty {
            serde_json::to_string_pretty(&payload)
        } else {
            serde_json::to_string(&payload)
        }
        .unwrap_or_else(|err| ril_source::ice!("fatal JSON serialization failed: {err}"))
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct InspectDiagnostic {
    pub sev: &'static str,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub code: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub loc: Option<String>,
    pub msg: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub labels: Vec<InspectLabel>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub notes: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub help: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct InspectLabel {
    pub loc: String,
    pub msg: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct WitnessStepJson {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub at: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub call: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cause: Option<&'static str>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct SymbolFact {
    pub sym: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kind: Option<&'static str>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub loc: Option<String>,
    pub sig: String,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub partial: bool,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub pure: bool,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub total: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub r#mut: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub shared_mut: Vec<String>,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub captures: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub effect_ops: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub no_ctl_params: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub may_panic: Vec<WitnessStepJson>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub may_abort: Vec<WitnessStepJson>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub may_diverge: Vec<WitnessStepJson>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum SiteFact {
    Closure {
        loc: String,
        #[serde(rename = "in", default, skip_serializing_if = "Option::is_none")]
        enclosing: Option<String>,
        sig: String,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        captures: Vec<String>,
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        pure: bool,
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        total: bool,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        effect_ops: Vec<String>,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        may_panic: Vec<WitnessStepJson>,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        may_abort: Vec<WitnessStepJson>,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        may_diverge: Vec<WitnessStepJson>,
    },
    ViaCall {
        loc: String,
        #[serde(rename = "in", default, skip_serializing_if = "Option::is_none")]
        enclosing: Option<String>,
        callee: String,
        via: BTreeMap<String, &'static str>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        ret: Option<String>,
    },
    With {
        loc: String,
        #[serde(rename = "in", default, skip_serializing_if = "Option::is_none")]
        enclosing: Option<String>,
        op: String,
        scope: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        handler: Option<String>,
    },
    EffectCall {
        loc: String,
        #[serde(rename = "in", default, skip_serializing_if = "Option::is_none")]
        enclosing: Option<String>,
        op: String,
        bound_by: String,
    },
    NarrowDrop {
        loc: String,
        #[serde(rename = "in", default, skip_serializing_if = "Option::is_none")]
        enclosing: Option<String>,
        path: String,
        cause: &'static str,
    },
}

struct FileIndex<'a> {
    files: Vec<String>,
    id_to_idx: BTreeMap<FileId, usize>,
    sources: &'a SourceMap,
    hir: Option<&'a Program>,
}

impl<'a> FileIndex<'a> {
    fn new(sources: &'a SourceMap, hir: Option<&'a Program>, entry: Option<FileId>) -> Self {
        let mut ordered: Vec<(FileId, String)> = Vec::new();
        let mut seen = BTreeSet::new();
        if let Some(entry_id) = entry
            && let Some(sf) = sources.get(entry_id)
        {
            ordered.push((entry_id, normalize_path(sf.path())));
            seen.insert(entry_id);
        }
        let mut rest: Vec<(FileId, String)> = Vec::new();
        if let Some(hir) = hir {
            for f in hir.files() {
                if !hir.is_stdlib_file(f.id) && seen.insert(f.id) {
                    rest.push((f.id, normalize_path(&f.path)));
                }
            }
        }
        for (id, path) in sources.file_paths() {
            if seen.insert(id) {
                rest.push((id, normalize_path(&path)));
            }
        }
        rest.sort_by(|a, b| a.1.cmp(&b.1));
        ordered.extend(rest);

        let mut id_to_idx = BTreeMap::new();
        let mut files = Vec::with_capacity(ordered.len());
        for (idx, (id, path)) in ordered.into_iter().enumerate() {
            id_to_idx.insert(id, idx);
            files.push(path);
        }
        Self {
            files,
            id_to_idx,
            sources,
            hir,
        }
    }

    fn source_file(&self, id: FileId) -> Option<&SourceFile> {
        self.sources.get(id).or_else(|| {
            self.hir
                .and_then(|h| h.files().find(|f| f.id == id).map(ril_hir::File::source))
        })
    }

    fn ensure_file(&mut self, id: FileId) -> Option<usize> {
        if id == FileId::BUILTIN {
            return None;
        }
        if let Some(&idx) = self.id_to_idx.get(&id) {
            return Some(idx);
        }
        let sf = self.source_file(id)?;
        let idx = self.files.len();
        self.files.push(normalize_path(sf.path()));
        self.id_to_idx.insert(id, idx);
        Some(idx)
    }

    fn format_point(&mut self, span: Span) -> Option<String> {
        let idx = self.ensure_file(span.file)?;
        let sf = self.source_file(span.file)?;
        let loc = sf.location(span.start)?;
        Some(format!("{idx}:{}:{}", loc.line, loc.column))
    }

    fn format_span(&mut self, span: Span) -> Option<String> {
        let idx = self.ensure_file(span.file)?;
        let sf = self.source_file(span.file)?;
        let start = sf.location(span.start)?;
        let end = sf.location(span.end.max(span.start))?;
        if start.line == end.line {
            if end.column > start.column {
                Some(format!(
                    "{idx}:{}:{}-{}",
                    start.line, start.column, end.column
                ))
            } else {
                Some(format!("{idx}:{}:{}", start.line, start.column))
            }
        } else {
            Some(format!(
                "{idx}:{}:{}-{}:{}",
                start.line, start.column, end.line, end.column
            ))
        }
    }

    fn span_coords(&self, span: Span) -> Option<(usize, usize, usize, usize, usize)> {
        let &idx = self.id_to_idx.get(&span.file)?;
        let sf = self.source_file(span.file)?;
        let start = sf.location(span.start)?;
        let end = sf.location(span.end.max(span.start))?;
        Some((idx, start.line, start.column, end.line, end.column))
    }

    fn file_matches_filter(&self, file_id: FileId, filters: &[String]) -> bool {
        if filters.is_empty() {
            return true;
        }
        let Some(&idx) = self.id_to_idx.get(&file_id) else {
            return false;
        };
        let Some(path) = self.files.get(idx) else {
            return false;
        };
        filters.iter().any(|f| {
            let norm = f.replace('\\', "/");
            path == &norm || path.ends_with(&format!("/{norm}")) || path.ends_with(&norm)
        })
    }

    fn span_matches_at(&self, span: Span, queries: &[AtQuery]) -> bool {
        if queries.is_empty() {
            return true;
        }
        let Some((idx, sl, sc, el, ec)) = self.span_coords(span) else {
            return false;
        };
        let Some(path) = self.files.get(idx) else {
            return false;
        };
        queries.iter().any(|q| {
            if let Some(ref qf) = q.file {
                let norm = qf.replace('\\', "/");
                if path != &norm && !path.ends_with(&format!("/{norm}")) && !path.ends_with(&norm) {
                    return false;
                }
            }
            if el < q.start_line || sl > q.end_line {
                return false;
            }
            if let Some(col) = q.col
                && sl == el
                && sl == q.start_line
            {
                return col >= sc && col <= ec.max(sc);
            }
            true
        })
    }
}

fn normalize_path(path: &std::path::Path) -> String {
    path.to_string_lossy().replace('\\', "/")
}

/// Builds a complete `InspectReport` from a `PartialAnalysis` and query filters.
pub fn build_report(
    partial: &PartialAnalysis,
    entry: Option<FileId>,
    query: &InspectQuery,
) -> InspectReport {
    let hir = partial.typed.as_deref().map(|t| &t.hir);
    let mut index = FileIndex::new(&partial.sources, hir, entry);

    let mut diagnostics = Vec::new();
    for diag in &partial.diagnostics {
        if !diag_matches_file(&index, diag, &query.files) {
            continue;
        }
        diagnostics.push(convert_diagnostic(&mut index, diag));
    }

    let ok = !diagnostics.iter().any(|d| d.sev == "error");

    let mut symbols: Vec<((usize, usize, usize), SymbolFact)> = Vec::new();
    let mut sites: Vec<((usize, usize, usize), SiteFact)> = Vec::new();

    if let Some(typed) = &partial.typed {
        let analysis = partial.analysis.as_deref();

        // Collect user-file functions (including local/where functions and effect ops).
        for (&def_id, callable) in &typed.callables {
            let def = typed.hir.definition(def_id);
            if typed.hir.is_stdlib_file(def.name.span.file) {
                continue;
            }
            if !index.file_matches_filter(def.name.span.file, &query.files) {
                continue;
            }
            let sym_name = display_symbol_name(typed, def_id);
            if !symbol_matches_filter(&sym_name, &def.name.value, &query.symbols) {
                continue;
            }
            let full_span = def.stmt.map_or(def.name.span, |s| {
                typed.hir.file(def.name.span.file).ast.stmt(s).span
            });
            if !index.span_matches_at(full_span, &query.at) {
                continue;
            }
            let fact = build_symbol_fact(&mut index, typed, analysis, def_id, callable);
            let sort_key = index
                .span_coords(def.name.span)
                .map_or((usize::MAX, 0, 0), |(f, l, c, _, _)| (f, l, c));
            symbols.push((sort_key, fact));
        }

        if !query.symbols_only {
            // Closures, `with` handlers, and effect calls from `BehaviorAnalysis`.
            if let Some(analysis) = analysis {
                for closure in &analysis.behavior.closures {
                    if !index.file_matches_filter(closure.span.file, &query.files)
                        || !index.span_matches_at(closure.span, &query.at)
                    {
                        continue;
                    }
                    let enc_name = closure.enclosing.map(|id| display_symbol_name(typed, id));
                    if !query.symbols.is_empty()
                        && !enc_name.as_deref().is_some_and(|n| {
                            let bare = n.rsplit("::").next().unwrap_or(n);
                            symbol_matches_filter(n, bare, &query.symbols)
                        })
                    {
                        continue;
                    }
                    let Some(loc) = index.format_span(closure.span) else {
                        continue;
                    };
                    let sig = typed
                        .types
                        .get(&closure.span)
                        .map(|t| t.display(&typed.hir).to_string())
                        .unwrap_or_else(|| "fn(...) -> _".into());
                    let (pure, total) = match typed.types.get(&closure.span) {
                        Some(Ty::Callable(c)) => {
                            let empty = Summary::default();
                            let p = is_pure(c, &empty)
                                && closure.captures.iter().all(|cap| {
                                    !cap.starts_with("mut ") && !cap.starts_with("^mut ")
                                });
                            let t = p
                                && !closure.behavior.may_panic
                                && !closure.behavior.may_abort
                                && !closure.behavior.may_diverge;
                            (p, t)
                        }
                        _ => (false, false),
                    };
                    let sort_key = index
                        .span_coords(closure.span)
                        .map_or((usize::MAX, 0, 0), |(f, l, c, _, _)| (f, l, c));
                    let may_panic = convert_witnesses(&mut index, &closure.witnesses.may_panic);
                    let may_abort = convert_witnesses(&mut index, &closure.witnesses.may_abort);
                    let may_diverge = convert_witnesses(&mut index, &closure.witnesses.may_diverge);
                    sites.push((
                        sort_key,
                        SiteFact::Closure {
                            loc,
                            enclosing: enc_name,
                            sig,
                            captures: closure.captures.clone(),
                            pure,
                            total,
                            effect_ops: closure.effect_ops.clone(),
                            may_panic,
                            may_abort,
                            may_diverge,
                        },
                    ));
                }

                for via_call in &analysis.via_calls {
                    if !index.file_matches_filter(via_call.span.file, &query.files)
                        || !index.span_matches_at(via_call.span, &query.at)
                    {
                        continue;
                    }
                    let enclosing = find_enclosing_fn(typed, via_call.span);
                    let enc_name = enclosing.map(|id| display_symbol_name(typed, id));
                    if !query.symbols.is_empty()
                        && !enc_name.as_deref().is_some_and(|n| {
                            let bare = n.rsplit("::").next().unwrap_or(n);
                            symbol_matches_filter(n, bare, &query.symbols)
                        })
                    {
                        continue;
                    }
                    let Some(loc) = index.format_span(via_call.span) else {
                        continue;
                    };
                    let callee = display_symbol_name(typed, via_call.callee);
                    let param_names = function_param_names(typed, via_call.callee);
                    let mut via_map = BTreeMap::new();
                    for &(param_idx, mode) in &via_call.choices {
                        let key = param_names
                            .get(param_idx)
                            .and_then(|n| n.clone())
                            .unwrap_or_else(|| format!("arg{param_idx}"));
                        via_map.insert(key, input_mode_str(mode));
                    }
                    let ret = typed
                        .types
                        .get(&via_call.span)
                        .map(|t| t.display(&typed.hir).to_string());
                    let sort_key = index
                        .span_coords(via_call.span)
                        .map_or((usize::MAX, 0, 0), |(f, l, c, _, _)| (f, l, c));
                    sites.push((
                        sort_key,
                        SiteFact::ViaCall {
                            loc,
                            enclosing: enc_name,
                            callee,
                            via: via_map,
                            ret,
                        },
                    ));
                }

                for w in &analysis.behavior.with_sites {
                    if !index.file_matches_filter(w.span.file, &query.files)
                        || !index.span_matches_at(w.span, &query.at)
                    {
                        continue;
                    }
                    let enc_name = w.enclosing.map(|id| display_symbol_name(typed, id));
                    if !query.symbols.is_empty()
                        && !enc_name.as_deref().is_some_and(|n| {
                            let bare = n.rsplit("::").next().unwrap_or(n);
                            symbol_matches_filter(n, bare, &query.symbols)
                        })
                    {
                        continue;
                    }
                    let Some(loc) = index.format_span(w.span) else {
                        continue;
                    };
                    let scope = index.format_span(w.scope).unwrap_or_else(|| loc.clone());
                    let handler = typed
                        .types
                        .get(&w.handler_span)
                        .map(|t| t.display(&typed.hir).to_string());
                    let sort_key = index
                        .span_coords(w.span)
                        .map_or((usize::MAX, 0, 0), |(f, l, c, _, _)| (f, l, c));
                    sites.push((
                        sort_key,
                        SiteFact::With {
                            loc,
                            enclosing: enc_name,
                            op: w.op.clone(),
                            scope,
                            handler,
                        },
                    ));
                }

                for ec in &analysis.behavior.effect_calls {
                    if !index.file_matches_filter(ec.span.file, &query.files)
                        || !index.span_matches_at(ec.span, &query.at)
                    {
                        continue;
                    }
                    let enc_name = ec.enclosing.map(|id| display_symbol_name(typed, id));
                    if !query.symbols.is_empty()
                        && !enc_name.as_deref().is_some_and(|n| {
                            let bare = n.rsplit("::").next().unwrap_or(n);
                            symbol_matches_filter(n, bare, &query.symbols)
                        })
                    {
                        continue;
                    }
                    let Some(loc) = index.format_span(ec.span) else {
                        continue;
                    };
                    let bound_by = ec
                        .bound_by
                        .and_then(|s| index.format_point(s))
                        .unwrap_or_else(|| "caller".into());
                    let sort_key = index
                        .span_coords(ec.span)
                        .map_or((usize::MAX, 0, 0), |(f, l, c, _, _)| (f, l, c));
                    sites.push((
                        sort_key,
                        SiteFact::EffectCall {
                            loc,
                            enclosing: enc_name,
                            op: ec.op.clone(),
                            bound_by,
                        },
                    ));
                }
            }

            // Narrowing invalidation sites from `TypedProgram`.
            for nd in &typed.narrow_drops {
                if typed.hir.is_stdlib_file(nd.span.file)
                    || !index.file_matches_filter(nd.span.file, &query.files)
                    || !index.span_matches_at(nd.span, &query.at)
                {
                    continue;
                }
                let enclosing = find_enclosing_fn(typed, nd.span);
                let enc_name = enclosing.map(|id| display_symbol_name(typed, id));
                if !query.symbols.is_empty()
                    && !enc_name.as_deref().is_some_and(|n| {
                        let bare = n.rsplit("::").next().unwrap_or(n);
                        symbol_matches_filter(n, bare, &query.symbols)
                    })
                {
                    continue;
                }
                let Some(loc) = index.format_span(nd.span) else {
                    continue;
                };
                let sort_key = index
                    .span_coords(nd.span)
                    .map_or((usize::MAX, 0, 0), |(f, l, c, _, _)| (f, l, c));
                sites.push((
                    sort_key,
                    SiteFact::NarrowDrop {
                        loc,
                        enclosing: enc_name,
                        path: nd.path.clone(),
                        cause: nd.cause.as_str(),
                    },
                ));
            }
        }
    }

    symbols.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.sym.cmp(&b.1.sym)));
    sites.sort_by_key(|a| a.0);

    let mut fix_hints = Vec::new();
    if query.wants_fix_hints() {
        let candidates = crate::fix::collect_fix_hints(partial, &ril_lint::LintConfig::default());
        for cand in candidates {
            let matches = cand.fix.edits.iter().any(|edit| {
                index.file_matches_filter(edit.span.file, &query.files)
                    && index.span_matches_at(edit.span, &query.at)
            });
            if !matches {
                continue;
            }
            let edits: Vec<InspectFixEdit> = cand
                .fix
                .edits
                .iter()
                .filter_map(|edit| {
                    let loc = index.format_span(edit.span)?;
                    Some(InspectFixEdit {
                        loc,
                        start: edit.span.start,
                        end: edit.span.end,
                        replacement: edit.replacement.clone(),
                    })
                })
                .collect();
            if edits.is_empty() {
                continue;
            }
            fix_hints.push(InspectFixHint {
                code: cand.code,
                title: cand.fix.title,
                safety: cand.fix.safety,
                kind: cand.fix.kind,
                capability_delta: cand.fix.delta,
                edits,
            });
        }
    }

    InspectReport {
        schema_version: SCHEMA_VERSION,
        ok,
        stage: partial.stage,
        files: index.files,
        diagnostics,
        symbols: symbols.into_iter().map(|(_, s)| s).collect(),
        sites: sites.into_iter().map(|(_, s)| s).collect(),
        fix_hints,
    }
}

/// Shared helper for `ril-lsp`: renders a named function's signature with parameter names
/// and expanded `&mut(p1, p2)` / `&^mut(p)` annotations when `Analysis` is available.
pub fn format_expanded_signature(
    typed: &TypedProgram,
    analysis: Option<&Analysis>,
    def_id: DefinitionId,
) -> Option<String> {
    let callable = typed.callables.get(&def_id)?;
    let def = typed.hir.definition(def_id);
    let param_names = function_param_names(typed, def_id);

    let ast_fun = def.stmt.and_then(|s| {
        if def.name.span.file == FileId::BUILTIN {
            return None;
        }
        let file = typed.hir.file(def.name.span.file);
        match &file.ast.stmt(s).value.kind {
            StmtKind::Function(f) => Some((file, f)),
            _ => None,
        }
    });

    let mut out = String::new();
    let is_meta = ast_fun.is_some_and(|(_, f)| f.is_meta);
    if is_meta {
        out.push_str("meta ");
    }
    out.push_str("fn ");
    out.push_str(&def.name.value);
    out.push('(');
    for (i, param) in callable.parameters.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        if param.is_meta {
            out.push_str("meta ");
        }
        match param.mode {
            Mode::Plain => {}
            Mode::Ref => out.push_str("ref "),
            Mode::Mut => out.push_str("mut "),
            Mode::Shared => out.push_str("^mut "),
            Mode::New => out.push_str("new "),
            Mode::Via => out.push_str("via "),
            Mode::Infer => out.push_str("infer "),
        }
        if let Some(Some(name)) = param_names.get(i) {
            out.push_str(name);
            out.push_str(": ");
        }
        out.push_str(&param.ty.display(&typed.hir).to_string());
        if let Some((file, fun)) = ast_fun
            && let Some(ast_param) = fun.signature.params.get(i)
        {
            for &guard in &ast_param.guards {
                if let Some(text) = compact_expr_source(file, guard) {
                    out.push_str(" |> ");
                    out.push_str(&text);
                }
            }
        }
    }
    out.push(')');

    // Effects
    if callable.open_effects {
        out.push_str(" @");
    }
    for eff in &callable.effects {
        out.push_str(" @");
        out.push_str(eff);
    }

    // State (expand `&mut` and `&^mut` using `Summary` when available!)
    if callable.open_state {
        out.push_str(" &");
    }
    let summary = analysis.and_then(|a| a.summaries.get(&def_id));
    let mut_names = summary
        .map(|s| formal_names(&param_names, &s.writes))
        .unwrap_or_default();
    let shared_names = summary
        .map(|s| formal_names(&param_names, &s.retained))
        .unwrap_or_default();

    for clause in &callable.state {
        out.push_str(" &");
        if clause == "mut" && !mut_names.is_empty() {
            out.push_str("mut(");
            out.push_str(&mut_names.join(", "));
            out.push(')');
        } else if clause == "^mut" && !shared_names.is_empty() {
            out.push_str("^mut(");
            out.push_str(&shared_names.join(", "));
            out.push(')');
        } else {
            out.push_str(clause);
        }
    }

    out.push_str(" -> ");
    match callable.result_mode {
        Mode::Plain => {}
        Mode::Ref => out.push_str("ref "),
        Mode::Mut => out.push_str("mut "),
        Mode::Shared => out.push_str("^mut "),
        Mode::New => out.push_str("new "),
        Mode::Via => out.push_str("via "),
        Mode::Infer => out.push_str("infer "),
    }
    out.push_str(&callable.result.display(&typed.hir).to_string());
    if let Some((file, fun)) = ast_fun {
        for &guard in &fun.signature.guards {
            if let Some(text) = compact_expr_source(file, guard) {
                out.push_str(" |> ");
                out.push_str(&text);
            }
        }
    }
    Some(out)
}

fn compact_expr_source(file: &ril_hir::File, expr: ril_syntax::syntax::ExprId) -> Option<String> {
    let span = file.ast.expr(expr).span;
    let raw = file.source_text().get(span.start..span.end)?;
    let compact: String = raw.split_whitespace().collect::<Vec<_>>().join(" ");
    (!compact.is_empty()).then_some(compact)
}

/// Shared helper for `ril-lsp`: extracts parameter names written by `&mut` (and `&^mut`).
pub fn expanded_mut_params(
    typed: &TypedProgram,
    analysis: &Analysis,
    def_id: DefinitionId,
) -> (Vec<String>, Vec<String>) {
    let Some(summary) = analysis.summaries.get(&def_id) else {
        return (Vec::new(), Vec::new());
    };
    let param_names = function_param_names(typed, def_id);
    (
        formal_names(&param_names, &summary.writes),
        formal_names(&param_names, &summary.retained),
    )
}

fn build_symbol_fact(
    index: &mut FileIndex<'_>,
    typed: &TypedProgram,
    analysis: Option<&Analysis>,
    def_id: DefinitionId,
    callable: &Callable,
) -> SymbolFact {
    let def = typed.hir.definition(def_id);
    let sym = display_symbol_name(typed, def_id);
    let loc = index.format_span(def.name.span);
    let sig = format_expanded_signature(typed, analysis, def_id).unwrap_or_else(|| {
        Ty::Callable(std::sync::Arc::new(callable.clone()))
            .display(&typed.hir)
            .to_string()
    });
    let kind = if typed.hir.operation_effect(def_id).is_some() {
        if typed.hir.is_ctl_operation(def_id) {
            Some("ctl_op")
        } else {
            Some("eff_op")
        }
    } else if def.stmt.is_some_and(|s| {
        matches!(
            &typed.hir.file(def.name.span.file).ast.stmt(s).value.kind,
            StmtKind::Function(f) if f.is_meta
        )
    }) {
        Some("meta_fn")
    } else {
        None
    };

    let Some(analysis) = analysis else {
        return SymbolFact {
            sym,
            kind,
            loc,
            sig,
            partial: true,
            pure: false,
            total: false,
            r#mut: Vec::new(),
            shared_mut: Vec::new(),
            captures: false,
            effect_ops: Vec::new(),
            no_ctl_params: Vec::new(),
            may_panic: Vec::new(),
            may_abort: Vec::new(),
            may_diverge: Vec::new(),
        };
    };

    let summary = analysis.summaries.get(&def_id).cloned().unwrap_or_default();
    let behavior = analysis
        .behavior
        .summaries
        .get(&def_id)
        .cloned()
        .unwrap_or_default();
    let param_names = function_param_names(typed, def_id);
    let mut_params = formal_names(&param_names, &summary.writes);
    let shared_params = formal_names(&param_names, &summary.retained);
    let no_ctl_params = formal_names(&param_names, &summary.no_ctl_params);

    let mut effect_ops = BTreeSet::new();
    for eu in &summary.effect_uses {
        if eu.effect == "io" {
            effect_ops.insert("@io".into());
        } else if let Some(op) = &eu.operation {
            let short_op = op.rsplit("::").next().unwrap_or(op);
            let short_eff = eu.effect.rsplit("::").next().unwrap_or(&eu.effect);
            let is_ctl = typed.hir.definitions().any(|(id, d)| {
                d.name.value == short_op
                    && typed.hir.operation_effect(id).is_some_and(|eff_id| {
                        let eff_name = &typed.hir.definition(eff_id).name.value;
                        eff_name == short_eff || typed.hir.export_name(eff_id) == eu.effect
                    })
                    && typed.hir.is_ctl_operation(id)
            });
            if is_ctl {
                effect_ops.insert(format!("ctl {short_eff}::{short_op}"));
            } else {
                effect_ops.insert(format!("{short_eff}::{short_op}"));
            }
        } else {
            let short_eff = eu.effect.rsplit("::").next().unwrap_or(&eu.effect);
            effect_ops.insert(format!("@{short_eff}"));
        }
    }
    for eff in &summary.effects {
        if eff == "io" {
            effect_ops.insert("@io".into());
        } else {
            let short_eff = eff.rsplit("::").next().unwrap_or(eff);
            if !effect_ops
                .iter()
                .any(|e| e.contains(&format!("{short_eff}::")) || e == &format!("@{short_eff}"))
            {
                effect_ops.insert(format!("@{short_eff}"));
            }
        }
    }
    if callable.open_effects {
        effect_ops.insert("@".into());
    }

    let pure = is_pure(callable, &summary);
    let total = is_total(callable, &summary, &behavior);
    let (may_panic, may_abort, may_diverge) =
        if let Some(w) = analysis.behavior.witnesses.get(&def_id) {
            (
                convert_witnesses(index, &w.may_panic),
                convert_witnesses(index, &w.may_abort),
                convert_witnesses(index, &w.may_diverge),
            )
        } else {
            (
                default_witness_if(behavior.may_panic),
                default_witness_if(behavior.may_abort),
                default_witness_if(behavior.may_diverge),
            )
        };

    SymbolFact {
        sym,
        kind,
        loc,
        sig,
        partial: false,
        pure,
        total,
        r#mut: mut_params,
        shared_mut: shared_params,
        captures: summary.captures,
        effect_ops: effect_ops.into_iter().collect(),
        no_ctl_params,
        may_panic,
        may_abort,
        may_diverge,
    }
}

fn default_witness_if(flag: bool) -> Vec<WitnessStepJson> {
    if flag {
        vec![WitnessStepJson {
            at: None,
            call: None,
            cause: Some("external"),
            detail: None,
        }]
    } else {
        Vec::new()
    }
}

fn convert_witnesses(index: &mut FileIndex<'_>, steps: &[WitnessStep]) -> Vec<WitnessStepJson> {
    steps
        .iter()
        .map(|s| WitnessStepJson {
            at: s.at.and_then(|sp| index.format_point(sp)),
            call: s.call.clone(),
            cause: s.cause.map(ril_sema::behavior::WitnessCause::as_str),
            detail: s.detail.clone(),
        })
        .collect()
}

fn convert_diagnostic(index: &mut FileIndex<'_>, diag: &Diagnostic) -> InspectDiagnostic {
    let sev = match diag.severity {
        Severity::Error => "error",
        Severity::Warning => "warning",
    };
    let loc = diag.primary.and_then(|sp| index.format_span(sp));
    let labels = diag
        .labels()
        .iter()
        .filter_map(|l| {
            let loc = index.format_span(l.span)?;
            Some(InspectLabel {
                loc,
                msg: l.message.clone(),
            })
        })
        .collect();
    InspectDiagnostic {
        sev,
        code: diag.code.map(|c| c.as_str().to_owned()),
        loc,
        msg: diag.message.clone(),
        labels,
        notes: diag.notes().to_vec(),
        help: diag.help().to_vec(),
    }
}

fn diag_matches_file(index: &FileIndex<'_>, diag: &Diagnostic, filters: &[String]) -> bool {
    if filters.is_empty() {
        return true;
    }
    if diag
        .primary
        .is_some_and(|sp| index.file_matches_filter(sp.file, filters))
    {
        return true;
    }
    diag.labels()
        .iter()
        .any(|l| index.file_matches_filter(l.span.file, filters))
}

fn display_symbol_name(typed: &TypedProgram, id: DefinitionId) -> String {
    let def = typed.hir.definition(id);
    if let Some(eff_id) = typed.hir.operation_effect(id) {
        let eff = &typed.hir.definition(eff_id).name.value;
        return format!("{eff}::{}", def.name.value);
    }
    def.name.value.clone()
}

fn symbol_matches_filter(sym: &str, bare: &str, filters: &[String]) -> bool {
    if filters.is_empty() {
        return true;
    }
    filters
        .iter()
        .any(|f| sym == f || bare == f || sym.ends_with(&format!("::{f}")))
}

pub fn function_param_names(typed: &TypedProgram, def_id: DefinitionId) -> Vec<Option<String>> {
    let def = typed.hir.definition(def_id);
    let Some(stmt) = def.stmt else {
        return Vec::new();
    };
    if def.name.span.file == FileId::BUILTIN {
        return Vec::new();
    }
    let ast = &typed.hir.file(def.name.span.file).ast;
    match &ast.stmt(stmt).value.kind {
        StmtKind::Function(f) => f
            .signature
            .params
            .iter()
            .map(|p| p.name.as_ref().map(|n| n.value.clone()))
            .collect(),
        _ => Vec::new(),
    }
}

fn formal_names(param_names: &[Option<String>], indices: &[usize]) -> Vec<String> {
    indices
        .iter()
        .map(|&idx| {
            param_names
                .get(idx)
                .and_then(|n| n.clone())
                .unwrap_or_else(|| format!("arg{idx}"))
        })
        .collect()
}

fn input_mode_str(mode: Input) -> &'static str {
    match mode {
        Input::Plain => "imm",
        Input::Ref => "ref",
        Input::Mut => "mut",
        Input::Shared => "^mut",
        Input::New => "new",
    }
}

fn find_enclosing_fn(typed: &TypedProgram, span: Span) -> Option<DefinitionId> {
    typed
        .hir
        .definitions()
        .filter(|(_, d)| {
            d.kind == DefinitionKind::Function && d.name.span.file == span.file && d.stmt.is_some()
        })
        .filter_map(|(id, d)| {
            let stmt_span = typed.hir.file(span.file).ast.stmt(d.stmt?).span;
            (span.start >= stmt_span.start && span.end <= stmt_span.end)
                .then_some((stmt_span.end.saturating_sub(stmt_span.start), id))
        })
        .min_by_key(|(len, _)| *len)
        .map(|(_, id)| id)
}
