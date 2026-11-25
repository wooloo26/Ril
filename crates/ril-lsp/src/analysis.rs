use std::{
    collections::{BTreeMap, HashMap},
    path::PathBuf,
    sync::Arc,
};

use ril_driver::{CompileOptions, Compiler, PartialAnalysis};
use ril_sema::ty::{Ty, TypedProgram};
use ril_source::span::{FileId, Span};

use crate::workspace::{LspConfig, WorkspacePackage, build_package_with_override};

#[derive(Default)]
pub(crate) struct CachedDoc {
    pub(crate) latest_typed: Option<Arc<TypedProgram>>,
    pub(crate) last_good_typed: Option<Arc<TypedProgram>>,
}

pub(crate) struct LspState {
    pub(crate) compiler: Compiler,
    pub(crate) workspace_root: Option<PathBuf>,
    pub(crate) documents: BTreeMap<String, String>,
    pub(crate) cache: HashMap<String, CachedDoc>,
    pub(crate) config: LspConfig,
    pub(crate) shutdown: bool,
}

impl LspState {
    pub(crate) fn new() -> Self {
        Self {
            compiler: Compiler::incremental(CompileOptions::default()),
            workspace_root: None,
            documents: BTreeMap::new(),
            cache: HashMap::new(),
            config: LspConfig::default(),
            shutdown: false,
        }
    }

    pub(crate) fn build_package(&self, uri: &str) -> Option<WorkspacePackage> {
        build_package_with_override(&self.documents, uri, None)
    }

    /// Runs best-effort partial analysis for `uri` and refreshes `latest_typed` / `last_good_typed`.
    pub(crate) fn refresh_document(&mut self, uri: &str) -> Option<(WorkspacePackage, PartialAnalysis)> {
        let ws = self.build_package(uri)?;
        let partial = self.compiler.analyze_partial(&ws.pkg);
        let entry = self.cache.entry(uri.to_owned()).or_default();
        if let Some(ref typed) = partial.typed {
            entry.latest_typed = Some(Arc::clone(typed));
            if partial.diagnostics.is_empty() {
                entry.last_good_typed = Some(Arc::clone(typed));
            }
        }
        Some((ws, partial))
    }

    /// Returns the best available `TypedProgram` for `uri`, preferring `latest_typed`
    /// and falling back to fresh partial analysis or `last_good_typed`.
    pub(crate) fn best_typed(&mut self, uri: &str) -> Option<(WorkspacePackage, Arc<TypedProgram>)> {
        let ws = self.build_package(uri)?;
        if let Some(cached) = self.cache.get(uri)
            && let Some(ref typed) = cached.latest_typed
        {
            return Some((ws, Arc::clone(typed)));
        }
        let partial = self.compiler.analyze_partial(&ws.pkg);
        let entry = self.cache.entry(uri.to_owned()).or_default();
        if let Some(typed) = partial.typed {
            entry.latest_typed = Some(Arc::clone(&typed));
            if partial.diagnostics.is_empty() {
                entry.last_good_typed = Some(Arc::clone(&typed));
            }
            return Some((ws, typed));
        }
        entry.last_good_typed.clone().map(|typed| (ws, typed))
    }

    /// Compiles a sanitized probe version of `uri` (e.g. stripping an incomplete
    /// `|> <prefix>` or `.<prefix>` tail) and extracts the static `Ty` of the expression
    /// ending near `expr_end`.
    pub(crate) fn probe_expr_type(
        &self,
        uri: &str,
        probe_text: &str,
        expr_start: usize,
        expr_end: usize,
    ) -> Option<(Arc<TypedProgram>, FileId, Ty)> {
        let ws = build_package_with_override(&self.documents, uri, Some(probe_text))?;
        let partial = self.compiler.analyze_partial(&ws.pkg);
        let typed = partial.typed?;
        let file = typed.hir.files().find(|f| f.path == ws.entry_logical)?;
        let file_id = file.id;

        if let Some(ty) = lookup_expr_type_near(&typed, file_id, expr_start, expr_end) {
            return Some((typed, file_id, ty));
        }
        None
    }
}

pub(crate) fn lookup_expr_type_near(
    typed: &TypedProgram,
    file_id: FileId,
    expr_start: usize,
    expr_end: usize,
) -> Option<Ty> {
    // 1. Exact span match.
    let exact = Span::new(file_id, expr_start, expr_end);
    if let Some(ty) = typed.types.get(&exact)
        && !matches!(ty, Ty::Unknown | Ty::Infer(_))
    {
        return Some(ty.clone());
    }

    // 2. Best expression span bounded inside `[expr_start, expr_end]` and ending at `expr_end`.
    let by_end = typed
        .types
        .iter()
        .filter(|(span, ty)| {
            span.file == file_id
                && !matches!(ty, Ty::Unknown | Ty::Infer(_))
                && span.start >= expr_start
                && span.end <= expr_end
                && span.end + 1 >= expr_end
        })
        .max_by_key(|(span, _)| span.end.saturating_sub(span.start));
    if let Some((_, ty)) = by_end {
        return Some(ty.clone());
    }

    // 3. Fallback: resolved identifier at the end of the expression (only if simple identifier).
    let file = typed.hir.file(file_id);
    let expr_text = file.source_text().get(expr_start..expr_end).map(str::trim);
    let is_simple_ident = expr_text.is_some_and(|s| {
        !s.is_empty() && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
    });
    if is_simple_ident {
        let probe_pos = expr_end.saturating_sub(1).max(expr_start);
        if let Some(def_id) = typed
            .hir
            .resolutions()
            .filter(|(span, _)| {
                span.file == file_id
                    && span.start >= expr_start
                    && span.end <= expr_end
                    && probe_pos >= span.start
                    && probe_pos <= span.end
            })
            .min_by_key(|(span, _)| span.end.saturating_sub(span.start))
            .and_then(|(_, res)| res.definition())
            && let Some(ty) = typed.bindings.get(&def_id)
            && !matches!(ty, Ty::Unknown | Ty::Infer(_))
        {
            return Some(ty.clone());
        }
        // Fault-tolerant lexical binding lookup: if parse recovery skipped this statement due to
        // a syntax error on an adjacent line, look up the closest preceding binding with this name.
        if let Some(ident) = expr_text
            && let Some((_, ty)) = typed
                .hir
                .definitions()
                .filter(|(_, def)| {
                    def.name.span.file == file_id
                        && def.name.value == ident
                        && def.name.span.end <= expr_start
                })
                .filter_map(|(id, def)| {
                    let ty = typed.bindings.get(&id)?;
                    (!matches!(ty, Ty::Unknown | Ty::Infer(_)))
                        .then_some((def.name.span.start, ty.clone()))
                })
                .max_by_key(|(start, _)| *start)
        {
            return Some(ty);
        }
    }

    // 4. Tightest expression span strictly contained within `[expr_start, expr_end]` (never an enclosing Block).
    let probe_pos = expr_end.saturating_sub(1).max(expr_start);
    typed
        .types
        .iter()
        .filter(|(span, ty)| {
            span.file == file_id
                && !matches!(ty, Ty::Unknown | Ty::Infer(_))
                && span.start >= expr_start
                && span.end <= expr_end
                && probe_pos >= span.start
                && probe_pos <= span.end
        })
        .min_by_key(|(span, _)| span.end.saturating_sub(span.start))
        .map(|(_, ty)| ty.clone())
}
