mod check;
mod flow;
pub mod horn;

pub use flow::Access;

use std::collections::BTreeMap;

use ril_base::{diag::Diagnostic, span::Span};
use ril_frontend::hir::DefinitionId;
use serde::{Deserialize, Serialize};

use crate::ty::TypedProgram;

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct Summary {
    pub writes: Vec<usize>,
    pub retained: Vec<usize>,
    pub roots: Vec<usize>,
    pub contained: Vec<(Access, usize)>,
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
            && revised.roots.iter().all(|root| self.roots.contains(root))
            && revised
                .contained
                .iter()
                .all(|source| self.contained.contains(source))
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum Input {
    Plain,
    Ref,
    Mut,
    Shared,
    New,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Instance {
    pub modes: Vec<Input>,
    pub summary: Summary,
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
    check::check(program)
}
