mod check;
mod flow;
pub mod horn;

pub use flow::{Access, Coordinate};

use std::collections::BTreeMap;

use ril_base::{diag::Diagnostic, span::Span};
use ril_frontend::hir::DefinitionId;
use serde::{Deserialize, Serialize};

use crate::ty::TypedProgram;

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct Summary {
    pub writes: Vec<usize>,
    pub retained: Vec<usize>,
    pub return_sources: Vec<ReturnSource>,
    pub effects: Vec<String>,
    pub captures: bool,
    pub constructs: bool,
}

impl Summary {
    pub fn subsumes(&self, revised: &Self) -> bool {
        revised
            .writes
            .iter()
            .all(|formal| self.writes.contains(formal) || self.retained.contains(formal))
            && revised
                .retained
                .iter()
                .all(|formal| self.retained.contains(formal))
            && revised
                .effects
                .iter()
                .all(|effect| self.effects.contains(effect))
            && (!revised.captures || self.captures)
            && (!self.constructs || revised.constructs)
            && revised
                .return_sources
                .iter()
                .all(|source| self.return_sources.contains(source))
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct ReturnSource {
    pub formal: usize,
    pub source_path: Vec<Coordinate>,
    pub result_path: Vec<Coordinate>,
    pub access: Access,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum Input {
    Plain,
    Ref,
    Mut,
    Shared,
    New,
}

impl Input {
    const fn access(self) -> Access {
        match self {
            Self::Plain => Access::Immutable,
            Self::Ref => Access::Ref,
            Self::Mut | Self::New => Access::Mut,
            Self::Shared => Access::Shared,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Instance {
    pub modes: Vec<Input>,
    pub summary: Summary,
}

impl Instance {
    pub fn domain_subsumes(baseline: &[Self], revision: &[Self]) -> bool {
        baseline.iter().all(|old| {
            revision
                .iter()
                .find(|new| old.modes == new.modes)
                .is_some_and(|new| old.summary.subsumes(&new.summary))
        })
    }
}

#[derive(Clone, Copy, Debug)]
pub enum CleanupAction {
    Function(DefinitionId),
    CloseSender,
}

#[derive(Default)]
pub struct Analysis {
    pub summaries: BTreeMap<DefinitionId, Summary>,
    pub via: BTreeMap<DefinitionId, Vec<Instance>>,
    pub horn_rules: Vec<horn::Rule<usize>>,
    pub cleanups: BTreeMap<Span, CleanupAction>,
}

pub fn check(program: &TypedProgram) -> Result<Analysis, Vec<Diagnostic>> {
    let (analysis, diagnostics) = check::analyze(program);
    if diagnostics.is_empty() {
        Ok(analysis)
    } else {
        Err(diagnostics)
    }
}

pub fn horn_rules(program: &TypedProgram) -> Vec<horn::Rule<usize>> {
    check::analyze(program).0.horn_rules
}
