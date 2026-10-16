//! Read-only analysis survives errors without exposing a verification constructor.
use super::*;
use crate::{
    hir::{HirProgram, VerifiedProgram},
    sema::{SemanticFacts, UnsupportedFeature},
};
use ril_syntax::ast::Program;
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnalysisStatus {
    Verified,
    Rejected,
    Incomplete,
    UnsupportedEnvironment,
}

#[derive(Debug)]
pub struct AnalysisSnapshot {
    outcome: CompilationOutcome,
    diagnostics: Vec<Diagnostic>,
    source: Option<Arc<Program>>,
    hir: Option<Arc<HirProgram>>,
    checked_hir: Option<Arc<HirProgram>>,
    facts: Option<Arc<SemanticFacts>>,
    unresolved: Vec<UnsupportedFeature>,
    verified: Option<VerifiedProgram>,
}

impl AnalysisSnapshot {
    pub fn status(&self) -> AnalysisStatus {
        match self.outcome {
            CompilationOutcome::Accepted { .. } | CompilationOutcome::Built { .. } => {
                AnalysisStatus::Verified
            }
            CompilationOutcome::Rejected { .. } => AnalysisStatus::Rejected,
            CompilationOutcome::NotImplemented { .. } => AnalysisStatus::Incomplete,
            CompilationOutcome::UnsupportedEnvironment { .. } => {
                AnalysisStatus::UnsupportedEnvironment
            }
        }
    }
    pub fn outcome(&self) -> &CompilationOutcome {
        &self.outcome
    }
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }
    fn outcome_diagnostics(outcome: &CompilationOutcome) -> Vec<Diagnostic> {
        match outcome {
            CompilationOutcome::Accepted { diagnostics, .. }
            | CompilationOutcome::Built { diagnostics, .. }
            | CompilationOutcome::Rejected { diagnostics } => diagnostics.clone(),
            _ => Vec::new(),
        }
    }
    pub fn source(&self) -> Option<&Program> {
        self.source.as_deref()
    }
    pub fn hir(&self) -> Option<&HirProgram> {
        self.hir.as_deref()
    }
    /// The post-static input used by semantic checking. It has a separate ID
    /// space; unmapped transformations do not claim original source identity.
    pub fn checked_hir(&self) -> Option<&HirProgram> {
        self.checked_hir.as_deref()
    }
    /// These are observations, including unresolved facts, not an authorization.
    pub fn facts(&self) -> Option<&SemanticFacts> {
        self.facts.as_deref()
    }
    pub fn unresolved(&self) -> &[UnsupportedFeature] {
        &self.unresolved
    }
    pub fn into_verified(self) -> Result<VerifiedProgram, CompilationOutcome> {
        self.verified.ok_or(self.outcome)
    }

    pub(super) fn failed(outcome: CompilationOutcome, source: Option<Program>) -> Self {
        let source = source.map(Arc::new);
        let (hir, mut unresolved) = Self::source_hir(source.as_deref());
        if let CompilationOutcome::NotImplemented { reason } = &outcome {
            unresolved.push(UnsupportedFeature {
                span: source
                    .as_ref()
                    .and_then(|program| program.statements.first())
                    .map(|statement| statement.span)
                    .unwrap_or(Span {
                        file: FileId(0),
                        start: 0,
                        end: 0,
                    }),
                description: reason.to_string(),
            });
        }
        Self {
            diagnostics: Self::outcome_diagnostics(&outcome),
            outcome,
            source,
            hir,
            checked_hir: None,
            facts: None,
            unresolved,
            verified: None,
        }
    }
    pub(super) fn semantic(
        outcome: CompilationOutcome,
        source: Program,
        checked_hir: Option<Arc<HirProgram>>,
        facts: Option<Arc<SemanticFacts>>,
        mut unresolved: Vec<UnsupportedFeature>,
    ) -> Self {
        let (hir, source_unresolved) = Self::source_hir(Some(&source));
        unresolved.extend(source_unresolved);
        Self {
            diagnostics: Self::outcome_diagnostics(&outcome),
            outcome,
            source: Some(Arc::new(source)),
            hir,
            checked_hir,
            facts,
            unresolved,
            verified: None,
        }
    }
    pub(super) fn verified(program: VerifiedProgram) -> Self {
        let (hir, unresolved) = Self::source_hir(Some(program.resolved_source()));
        Self {
            diagnostics: program.diagnostics().to_vec(),
            outcome: CompilationOutcome::Accepted {
                diagnostics: program.diagnostics().to_vec(),
                causes: vec![],
            },
            source: Some(program.shared_source()),
            hir,
            checked_hir: Some(program.shared_hir()),
            facts: Some(program.shared_facts()),
            unresolved,
            verified: Some(program),
        }
    }
    pub(super) fn verified_mut(&mut self) -> Option<&mut VerifiedProgram> {
        self.verified.as_mut()
    }
    pub(super) fn with_diagnostics(mut self, diagnostics: Vec<Diagnostic>) -> Self {
        self.diagnostics = diagnostics;
        self
    }
    pub(super) fn with_unresolved(mut self, unresolved: Vec<UnsupportedFeature>) -> Self {
        self.unresolved.extend(unresolved);
        self
    }
    fn source_hir(source: Option<&Program>) -> (Option<Arc<HirProgram>>, Vec<UnsupportedFeature>) {
        let Some(source) = source else {
            return (None, vec![]);
        };
        match HirProgram::lower(source) {
            Ok(hir) => (Some(Arc::new(hir)), vec![]),
            Err(error) => (
                None,
                vec![UnsupportedFeature {
                    span: source
                        .statements
                        .first()
                        .map(|statement| statement.span)
                        .unwrap_or(Span {
                            file: FileId(0),
                            start: 0,
                            end: 0,
                        }),
                    description: format!("source HIR is unavailable: {error}"),
                }],
            ),
        }
    }
}
