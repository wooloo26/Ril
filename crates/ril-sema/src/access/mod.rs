mod check;
mod flow;
pub mod horn;

pub use flow::{Access, Coordinate};

use std::collections::BTreeMap;

use ril_base::{diag::Diagnostic, span::Span};
use ril_frontend::{hir::DefinitionId, syntax::Mode};
use serde::{Deserialize, Serialize};

use crate::ty::TypedProgram;

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct Summary {
    pub writes: Vec<usize>,
    pub retained: Vec<usize>,
    pub return_sources: Vec<ReturnSource>,
    pub effects: Vec<String>,
    pub invocations: Vec<Invocation>,
    pub callback_returns: Vec<CallbackReturn>,
    pub storage_updates: Vec<StorageUpdate>,
    pub captures: bool,
    pub constructs: bool,
}

impl Summary {
    fn normalize_invocations(&mut self) {
        let mut inputs = BTreeMap::new();
        for invocation in &self.invocations {
            let key = (invocation.receiver, invocation.parameter, invocation.mode);
            *inputs.entry(key).or_insert(false) |= invocation.preserves_input
                && !matches!(invocation.mode, InvocationMode::Input(input) if input != Input::New);
        }
        self.invocations = inputs
            .into_iter()
            .map(
                |((receiver, parameter, mode), preserves_input)| Invocation {
                    receiver,
                    parameter,
                    mode,
                    preserves_input,
                },
            )
            .collect();
    }

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
                .invocations
                .iter()
                .all(|invoke| self.invocations.iter().any(|old| old.permits(invoke)))
            && revised
                .callback_returns
                .iter()
                .all(|result| self.callback_returns.contains(result))
            && revised
                .return_sources
                .iter()
                .all(|source| self.return_sources.contains(source))
            && revised
                .storage_updates
                .iter()
                .all(|update| self.storage_updates.iter().any(|old| old.permits(update)))
            && self
                .storage_updates
                .iter()
                .filter(|old| old.definite)
                .all(|old| {
                    revised
                        .storage_updates
                        .iter()
                        .any(|update| old.same_target(update) && update.definite)
                })
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub enum InvocationMode {
    Input(Input),
    Formal(usize),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct Invocation {
    pub receiver: usize,
    pub parameter: usize,
    pub mode: InvocationMode,
    pub preserves_input: bool,
}

impl Invocation {
    fn permits(&self, revised: &Self) -> bool {
        self.receiver == revised.receiver
            && self.parameter == revised.parameter
            && self.mode == revised.mode
            && (!revised.preserves_input || self.preserves_input)
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct CallbackReturn {
    pub receiver: usize,
    pub receiver_path: Vec<Coordinate>,
    pub source_path: Vec<Coordinate>,
    pub result_path: Vec<Coordinate>,
    pub cap: Option<Access>,
    pub arguments: Vec<CallbackArgument>,
}

impl CallbackReturn {
    fn specialize(&mut self, input: &impl Fn(usize) -> Option<Input>) {
        for argument in &mut self.arguments {
            for mode in &mut argument.modes {
                if let InvocationMode::Formal(formal) = *mode
                    && let Some(input) = input(formal)
                {
                    for source in &mut argument.sources {
                        if source.formal == formal
                            && source.source_path.is_empty()
                            && source.result_path.is_empty()
                        {
                            source.access = input.access();
                        }
                    }
                    *mode = InvocationMode::Input(input);
                }
            }
            argument.modes.sort_unstable();
            argument.modes.dedup();
            argument.sources.sort_unstable();
            argument.sources.dedup();
            argument.constructs |= argument.modes == [InvocationMode::Input(Input::New)];
            for result in &mut argument.callback_returns {
                result.specialize(input);
            }
            argument.callback_returns.sort_unstable();
            argument.callback_returns.dedup();
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct CallbackArgument {
    pub position: usize,
    pub modes: Vec<InvocationMode>,
    pub sources: Vec<ReturnSource>,
    pub callback_returns: Vec<CallbackReturn>,
    pub constructs: bool,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct ReturnSource {
    pub formal: usize,
    pub source_path: Vec<Coordinate>,
    pub result_path: Vec<Coordinate>,
    pub access: Access,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct StorageUpdate {
    pub formal: usize,
    pub path: Vec<Coordinate>,
    pub sources: Vec<ReturnSource>,
    pub callback_returns: Vec<CallbackReturn>,
    pub definite: bool,
    pub constructs: bool,
}

impl StorageUpdate {
    fn same_target(&self, revised: &Self) -> bool {
        self.formal == revised.formal && self.path == revised.path
    }

    fn permits(&self, revised: &Self) -> bool {
        self.same_target(revised)
            && (!self.constructs || revised.constructs)
            && revised
                .sources
                .iter()
                .all(|source| self.sources.contains(source))
            && revised
                .callback_returns
                .iter()
                .all(|result| self.callback_returns.contains(result))
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

impl Input {
    const fn from_mode(mode: Mode) -> Option<Self> {
        Some(match mode {
            Mode::Plain => Self::Plain,
            Mode::Ref => Self::Ref,
            Mode::Mut => Self::Mut,
            Mode::Shared => Self::Shared,
            Mode::New => Self::New,
            Mode::Via | Mode::Infer => return None,
        })
    }

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
