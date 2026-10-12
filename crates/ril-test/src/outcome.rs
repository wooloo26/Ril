use crate::{Case, Mode, Result};
use serde::{Deserialize, Serialize};
use std::path::Path;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExpectedOutcome {
    pub mode: Mode,
    pub errors: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub exit: Option<i64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stdout: Option<Vec<u8>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stderr: Option<Vec<u8>>,
}
pub fn expected_outcome(item: &Case) -> Result<ExpectedOutcome> {
    let mut item = item.clone();
    crate::validate_case(&mut item)?;
    let stream = |name: &Option<String>| {
        name.as_ref().map(|name| {
            if name == "empty" {
                Vec::new()
            } else {
                item.files
                    .iter()
                    .find(|file| &file.name == name)
                    .unwrap()
                    .bytes
                    .clone()
            }
        })
    };
    Ok(ExpectedOutcome {
        mode: item.meta.mode,
        errors: item.errors.clone(),
        exit: item.meta.exit,
        stdout: stream(&item.meta.stdout),
        stderr: stream(&item.meta.stderr),
    })
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum StaticStatus {
    Accepted,
    Rejected,
    CompilerCrash,
    NotImplemented,
    UnsupportedEnvironment,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum BuildStatus {
    Succeeded,
    Failed,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum RuntimeStatus {
    Exited,
    ReturnedUnit,
    ReturnedOk,
    ReturnedErr,
    LanguagePanic,
    DoubleFault,
    Cancelled,
    NativeCrash,
    Timeout,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum PanicOrigin {
    DesignatedOperation,
    FixtureSetup,
}

/// Adapter facts are an internal Rust interface, not a compiler wire protocol.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(default)]
pub struct ObservedOutcome {
    pub environment: Option<String>,
    #[serde(rename = "static")]
    pub static_status: Option<StaticStatus>,
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
    pub build: Option<BuildStatus>,
    pub runtime: Option<RuntimeStatus>,
    pub origin: Option<PanicOrigin>,
    pub exit: Option<i64>,
    pub stdout: Option<Vec<u8>>,
    pub stderr: Option<Vec<u8>>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Verdict {
    Pass,
    Fail,
    HarnessError,
    Incomplete,
}

pub fn judge_outcome(expected: &ExpectedOutcome, observed: Option<&ObservedOutcome>) -> Verdict {
    use RuntimeStatus::*;
    let Some(observed) = observed else {
        return Verdict::HarnessError;
    };
    if observed.environment.is_some() {
        return Verdict::HarnessError;
    }
    if matches!(
        observed.static_status,
        Some(StaticStatus::NotImplemented | StaticStatus::UnsupportedEnvironment)
    ) {
        return Verdict::Incomplete;
    }
    let passes = if expected.mode == Mode::CheckFail {
        observed.static_status == Some(StaticStatus::Rejected)
            && !expected.errors.is_empty()
            && expected
                .errors
                .iter()
                .all(|code| observed.errors.contains(code))
    } else if observed.static_status != Some(StaticStatus::Accepted) {
        false
    } else if expected.mode == Mode::CheckPass {
        true
    } else if observed.build != Some(BuildStatus::Succeeded) {
        false
    } else {
        match expected.mode {
            Mode::RunPass => matches!(observed.runtime, Some(ReturnedUnit | ReturnedOk)),
            Mode::RunPanic => {
                observed.runtime == Some(LanguagePanic)
                    && observed.origin == Some(PanicOrigin::DesignatedOperation)
            }
            Mode::RunProgram => {
                let valid_exit = match observed.runtime {
                    Some(ReturnedUnit | ReturnedOk) => observed.exit == Some(0),
                    Some(ReturnedErr | LanguagePanic | DoubleFault | Cancelled) => {
                        observed.exit == Some(1)
                    }
                    Some(NativeCrash | Timeout) => false,
                    Some(Exited) | None => true,
                };
                valid_exit
                    && observed.exit.is_some()
                    && observed.exit == expected.exit
                    && expected
                        .stdout
                        .as_ref()
                        .is_none_or(|bytes| observed.stdout.as_ref() == Some(bytes))
                    && expected
                        .stderr
                        .as_ref()
                        .is_none_or(|bytes| observed.stderr.as_ref() == Some(bytes))
            }
            _ => false,
        }
    };
    if passes { Verdict::Pass } else { Verdict::Fail }
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(default)]
pub struct ExecutionReport {
    pub selected: usize,
    pub attempted: usize,
    pub passed: usize,
    pub failed: usize,
    pub harness_error: usize,
    pub unimplemented: usize,
    pub unsupported_environment: usize,
}
pub fn summarize_execution(report: &ExecutionReport) -> Verdict {
    if report.harness_error > 0 {
        return Verdict::HarnessError;
    }
    if report.failed > 0 {
        return Verdict::Fail;
    }
    if report.selected == 0
        || report.attempted != report.selected
        || report.passed != report.selected
        || report.unimplemented > 0
        || report.unsupported_environment > 0
    {
        return Verdict::Incomplete;
    }
    Verdict::Pass
}
/// A future runner must supply fresh program state and an isolated workspace per case.
pub trait CompilerAdapter {
    fn observe(&mut self, case: &Case, workspace: &Path) -> Result<ObservedOutcome>;
}
pub fn evaluate_case(
    adapter: &mut dyn CompilerAdapter,
    case: &Case,
    workspace: &Path,
) -> Result<Verdict> {
    let expected = expected_outcome(case)?;
    let observed = adapter.observe(case, workspace)?;
    Ok(judge_outcome(&expected, Some(&observed)))
}
