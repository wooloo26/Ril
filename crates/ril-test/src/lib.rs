#![forbid(unsafe_code)]

mod protocol;
mod runner;
mod shield;
mod spec;

pub use protocol::{Activation, Case, CaseMode, Suite, SuiteError, parse_suite};
pub use runner::{discover, run_case, run_harness, run_worker, trials};
pub use spec::spec_suite;

use std::{
    collections::BTreeMap,
    fmt,
    path::{Path, PathBuf},
    process::ExitStatus,
    str::FromStr,
};

use ril_base::{diag::Diagnostic, span::FileId};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Milestone {
    M0,
    M1,
    M2,
    M3,
    M4,
    M5,
}

impl FromStr for Milestone {
    type Err = String;

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        match text {
            "m0" => Ok(Self::M0),
            "m1" => Ok(Self::M1),
            "m2" => Ok(Self::M2),
            "m3" => Ok(Self::M3),
            "m4" => Ok(Self::M4),
            "m5" => Ok(Self::M5),
            _ => Err(format!("unknown milestone {text:?}")),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Stage {
    Source,
    Lex,
    Parse,
    Hir,
    Type,
    Access,
    Mir,
    Run,
}

impl Stage {
    pub const fn milestone(self) -> Milestone {
        match self {
            Self::Source => Milestone::M0,
            Self::Lex | Self::Parse | Self::Hir => Milestone::M1,
            Self::Type => Milestone::M2,
            Self::Access => Milestone::M3,
            Self::Mir | Self::Run => Milestone::M4,
        }
    }
}

impl FromStr for Stage {
    type Err = String;

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        match text {
            "source" => Ok(Self::Source),
            "lex" => Ok(Self::Lex),
            "parse" => Ok(Self::Parse),
            "hir" => Ok(Self::Hir),
            "type" | "ty" => Ok(Self::Type),
            "access" => Ok(Self::Access),
            "mir" => Ok(Self::Mir),
            "run" => Ok(Self::Run),
            _ => Err(format!("unknown compiler stage {text:?}")),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Unit {
    Bin,
    Lib,
    Decl,
    Snippet,
}

impl Unit {
    const fn entry(self) -> &'static str {
        match self {
            Self::Decl => "pkg/main.d.ril",
            Self::Bin | Self::Lib | Self::Snippet => "pkg/main.ril",
        }
    }
}

impl FromStr for Unit {
    type Err = String;

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        match text {
            "bin" => Ok(Self::Bin),
            "lib" => Ok(Self::Lib),
            "decl" => Ok(Self::Decl),
            "snippet" => Ok(Self::Snippet),
            _ => Err(format!("unknown unit kind {text:?}")),
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct VirtualFile {
    pub bytes: Vec<u8>,
    suite_lines: Vec<usize>,
}

impl VirtualFile {
    pub fn suite_line(&self, virtual_line: usize) -> Option<usize> {
        self.suite_lines.get(virtual_line.checked_sub(1)?).copied()
    }

    fn push(&mut self, text: &str, line: usize) {
        self.bytes.extend_from_slice(text.as_bytes());
        self.suite_lines.push(line);
    }

    fn append(&mut self, other: Self) {
        self.bytes.extend(other.bytes);
        self.suite_lines.extend(other.suite_lines);
    }
}

#[derive(Clone, Debug)]
pub struct VirtualPackage {
    pub unit: Unit,
    pub files: BTreeMap<PathBuf, VirtualFile>,
    pub entry: PathBuf,
    pub budget: Option<u64>,
}

impl VirtualPackage {
    pub fn new(unit: Unit) -> Self {
        Self {
            unit,
            files: BTreeMap::new(),
            entry: unit.entry().into(),
            budget: None,
        }
    }

    pub fn insert(&mut self, path: PathBuf, bytes: Vec<u8>) {
        self.files.insert(
            path,
            VirtualFile {
                bytes,
                suite_lines: Vec::new(),
            },
        );
    }
}

#[derive(Clone, Debug, Default)]
pub struct CheckResult {
    pub diagnostics: Vec<Diagnostic>,
    pub signatures: BTreeMap<String, String>,
    pub file_paths: BTreeMap<FileId, PathBuf>,
}

impl CheckResult {
    pub fn unsupported(message: impl Into<String>) -> Self {
        Self {
            diagnostics: vec![Diagnostic::unsupported(message)],
            signatures: BTreeMap::new(),
            file_paths: BTreeMap::new(),
        }
    }
}

#[derive(Debug)]
pub struct ExecOutput {
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub status: ExitStatus,
}

pub trait TestDriver: Send + Sync {
    fn check_stage(&self, pkg: &VirtualPackage, upto: Stage) -> CheckResult;

    fn check_compat(&self, _base: &VirtualPackage, _rev: &VirtualPackage) -> CheckResult {
        CheckResult::unsupported("compat check not enabled")
    }

    fn run_jit(&self, _pkg: &VirtualPackage) -> Result<ExecOutput, Vec<Diagnostic>> {
        Err(vec![Diagnostic::unsupported("jit not enabled")])
    }

    fn build_aot(&self, _pkg: &VirtualPackage, _out: &Path) -> Result<(), Vec<Diagnostic>> {
        Err(vec![Diagnostic::unsupported("aot not enabled")])
    }
}

#[derive(Debug)]
pub struct WorkerError(String);

impl fmt::Display for WorkerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for WorkerError {}
