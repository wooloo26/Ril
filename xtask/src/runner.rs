//! Execute corpus cases through the CLI, without depending on the compiler.
use process_wrap::std::*;
use ril_test::{
    BuildStatus, Capability, Case, CompilerAdapter, ExecutionReport, Mode, ObservedOutcome,
    PointerTarget, RuntimeStatus, StaticStatus, Unit, Verdict,
};
use serde::{Deserialize, Serialize};
use std::{
    fs,
    io::{self, Read, Write},
    path::{Path, PathBuf},
    process::{Command, ExitStatus, Stdio},
    sync::mpsc,
    thread,
    time::{Duration, Instant},
};

#[derive(Debug, Clone)]
pub struct RunOptions {
    pub compiler: PathBuf,
    pub cases: Vec<String>,
    pub filter: Option<String>,
    pub modes: Vec<Mode>,
    pub applicable_only: bool,
    pub timeout: Duration,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CaseExecution {
    pub id: String,
    pub verdict: Verdict,
    pub observed: Option<ObservedOutcome>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    pub elapsed_ms: u128,
}

#[derive(Debug, Serialize)]
pub struct CorpusExecution {
    pub compiler: PathBuf,
    pub report: ExecutionReport,
    pub verdict: Verdict,
    pub cases: Vec<CaseExecution>,
    pub excluded: Vec<CaseExclusion>,
}
#[derive(Debug, Serialize)]
pub struct CaseExclusion {
    pub id: String,
    pub reason: String,
}

pub fn run_corpus(cases: &[Case], options: &RunOptions) -> ril_test::Result<CorpusExecution> {
    if options.timeout.is_zero() {
        return Err(invalid("timeout must be positive"));
    }
    for id in &options.cases {
        if !cases.iter().any(|case| &case.id == id) {
            return Err(invalid(format!("unknown case: {id}")));
        }
    }
    // Resolve relative executable paths before switching into an isolated case directory.
    let compiler = std::path::absolute(&options.compiler)?;
    let mut adapter = CliAdapter::new(compiler.clone(), options.timeout);
    let selected = cases.iter().filter(|case| {
        (options.cases.is_empty() || options.cases.contains(&case.id))
            && options
                .filter
                .as_ref()
                .is_none_or(|filter| case.id.contains(filter))
            && (options.modes.is_empty() || options.modes.contains(&case.meta.mode))
    });
    let mut report = ExecutionReport::default();
    let mut executions = Vec::new();
    let mut excluded = Vec::new();
    for case in selected {
        if options.applicable_only
            && let Some(reason) = applicability_host().and_then(|host| exclusion_reason(case, host))
        {
            excluded.push(CaseExclusion {
                id: case.id.clone(),
                reason,
            });
            continue;
        }
        report.selected += 1;
        if !unavailable_requirement(case) {
            report.attempted += 1;
        }
        let started = Instant::now();
        let observation = tempfile::tempdir()
            .map_err(ril_test::Error::from)
            .and_then(|temp| adapter.observe(case, temp.path()));
        let (observed, verdict, detail) = match observation {
            Ok(observed) => {
                let verdict =
                    ril_test::judge_outcome(&ril_test::expected_outcome(case)?, Some(&observed));
                (Some(observed), verdict, adapter.last_detail.take())
            }
            Err(error) => (None, Verdict::HarnessError, Some(error.to_string())),
        };
        match observed
            .as_ref()
            .and_then(|observed| observed.static_status)
        {
            Some(StaticStatus::NotImplemented) => report.unimplemented += 1,
            Some(StaticStatus::UnsupportedEnvironment) => report.unsupported_environment += 1,
            _ => {}
        }
        match verdict {
            Verdict::Pass => report.passed += 1,
            Verdict::Fail => report.failed += 1,
            Verdict::HarnessError => report.harness_error += 1,
            Verdict::Incomplete => {}
        }
        executions.push(CaseExecution {
            id: case.id.clone(),
            verdict,
            observed,
            detail,
            elapsed_ms: started.elapsed().as_millis(),
        });
    }
    Ok(CorpusExecution {
        compiler,
        verdict: ril_test::summarize_execution(&report),
        report,
        cases: executions,
        excluded,
    })
}

/// Selection depends only on an explicit OS requirement, never on compiler,
/// linker, feature, or tool availability. Unsupported execution stays visible.
pub fn exclusion_reason(case: &Case, host: &str) -> Option<String> {
    if !case.meta.mode.is_run() {
        return None;
    }
    let requirements = case.meta.requires.as_deref().unwrap_or_default();
    let windows = requirements.contains(&Capability::Windows);
    let posix = requirements.contains(&Capability::Posix);
    let required = match (windows, posix) {
        (true, false) => "x86_64-pc-windows-msvc",
        (false, true) => "x86_64-unknown-linux-gnu",
        _ => return None,
    };
    if !matches!(host, "x86_64-pc-windows-msvc" | "x86_64-unknown-linux-gnu") || host == required {
        return None;
    }
    Some(format!(
        "native case explicitly requires {required}; runner host is {host}"
    ))
}
fn applicability_host() -> Option<&'static str> {
    if cfg!(all(target_arch = "x86_64", target_os = "windows")) {
        Some("x86_64-pc-windows-msvc")
    } else if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
        Some("x86_64-unknown-linux-gnu")
    } else {
        None
    }
}

pub struct CliAdapter {
    pub compiler: PathBuf,
    pub timeout: Duration,
    last_detail: Option<String>,
}

fn invalid(message: impl Into<String>) -> ril_test::Error {
    ril_test::Error::Invalid(message.into())
}

fn host_target() -> &'static str {
    if cfg!(windows) {
        "x86_64-pc-windows-msvc"
    } else {
        "x86_64-unknown-linux-gnu"
    }
}

fn target(case: &Case) -> &'static str {
    match case.meta.target {
        Some(PointerTarget::Pointer32) => "pointer32",
        Some(PointerTarget::Pointer64) => "pointer64",
        None => host_target(),
    }
}

fn unavailable_requirement(case: &Case) -> bool {
    case.meta
        .requires
        .iter()
        .flatten()
        .any(|requirement| match requirement {
            Capability::Windows => !cfg!(windows),
            Capability::Posix => !cfg!(unix),
            Capability::Filesystem
            | Capability::Process
            | Capability::Clock
            | Capability::Entropy => false,
        })
}

fn unit_name(unit: Unit) -> &'static str {
    match unit {
        Unit::Library => "library",
        Unit::Executable => "executable",
    }
}

impl CliAdapter {
    pub fn new(compiler: PathBuf, timeout: Duration) -> Self {
        Self {
            compiler,
            timeout,
            last_detail: None,
        }
    }
    fn compiler_command(
        &self,
        phase: &str,
        source: &Path,
        case: &Case,
        unit: Unit,
        workspace: &Path,
    ) -> Command {
        let mut command = Command::new(&self.compiler);
        command.current_dir(workspace).arg(phase).arg(source).args([
            "--json",
            "--target",
            target(case),
            "--unit",
            unit_name(unit),
        ]);
        command
    }

    fn compile(
        &mut self,
        command: Command,
        deadline: Instant,
    ) -> ril_test::Result<(ObservedOutcome, CompilerResponse)> {
        let output = capture(command, Vec::new(), deadline)?;
        if output.timed_out || native_crash(output.status) {
            self.last_detail = Some(if output.timed_out {
                "compiler timed out".into()
            } else {
                "compiler crashed".into()
            });
            return Ok((
                ObservedOutcome {
                    static_status: Some(StaticStatus::CompilerCrash),
                    stderr: Some(output.stderr),
                    runtime: output.timed_out.then_some(RuntimeStatus::Timeout),
                    ..Default::default()
                },
                CompilerResponse::default(),
            ));
        }
        let response: CompilerResponse = match serde_json::from_slice(&output.stdout) {
            Ok(response) => response,
            Err(_error) if !output.status.is_some_and(|status| status.success()) => {
                self.last_detail = Some(format!(
                    "compiler exited {:?} without a structured report",
                    output.status.and_then(|status| status.code())
                ));
                return Ok((
                    ObservedOutcome {
                        static_status: Some(StaticStatus::CompilerCrash),
                        stderr: Some(output.stderr),
                        ..Default::default()
                    },
                    CompilerResponse::default(),
                ));
            }
            Err(error) => return Err(invalid(format!("invalid compiler JSON: {error}"))),
        };
        let static_status = match response.status.as_str() {
            "accepted" | "built" | "executed" => StaticStatus::Accepted,
            "rejected" => StaticStatus::Rejected,
            "not-implemented" => StaticStatus::NotImplemented,
            "unsupported-environment" => StaticStatus::UnsupportedEnvironment,
            status => return Err(invalid(format!("unknown compiler status: {status}"))),
        };
        if let Some(reason) = &response.reason {
            self.last_detail = Some(reason.to_string());
        }
        let required_exit = match static_status {
            StaticStatus::Accepted => 0,
            StaticStatus::Rejected => 1,
            _ => 2,
        };
        if output.status.and_then(|status| status.code()) != Some(required_exit) {
            return Err(invalid("compiler status contradicts its process exit code"));
        }
        let (warnings, errors): (Vec<_>, Vec<_>) = response
            .diagnostics
            .iter()
            .partition(|diagnostic| diagnostic.severity.as_deref() == Some("warning"));
        if static_status == StaticStatus::Accepted && !errors.is_empty() {
            return Err(invalid(
                "accepted compiler report contains error diagnostics",
            ));
        }
        Ok((
            ObservedOutcome {
                static_status: Some(static_status),
                errors: errors
                    .iter()
                    .map(|diagnostic| diagnostic.code.clone())
                    .collect(),
                warnings: warnings
                    .iter()
                    .map(|diagnostic| diagnostic.code.clone())
                    .collect(),
                ..Default::default()
            },
            response,
        ))
    }

    fn build(
        &mut self,
        source: &Path,
        output: &Path,
        case: &Case,
        workspace: &Path,
        deadline: Instant,
    ) -> ril_test::Result<ObservedOutcome> {
        if let Some(parent) = output.parent() {
            fs::create_dir_all(parent)?;
        }
        let mut command = self.compiler_command("build", source, case, Unit::Executable, workspace);
        command.arg("--output").arg(output);
        let (mut observed, response) = self.compile(command, deadline)?;
        if observed.static_status == Some(StaticStatus::Accepted) {
            if response.status != "built" && response.status != "accepted" {
                return Err(invalid("build did not return an artifact report"));
            }
            let reported = response
                .artifact
                .map(|artifact| artifact.path)
                .or(response.path)
                .ok_or_else(|| invalid("successful build omitted artifact path"))?;
            let reported = if reported.is_absolute() {
                reported
            } else {
                workspace.join(reported)
            };
            if fs::canonicalize(reported)? != fs::canonicalize(output)? || !output.is_file() {
                return Err(invalid("compiler artifact differs from requested output"));
            }
            observed.build = Some(BuildStatus::Succeeded);
        } else {
            observed.build = Some(BuildStatus::Failed);
        }
        Ok(observed)
    }
}

impl CompilerAdapter for CliAdapter {
    fn observe(&mut self, case: &Case, workspace: &Path) -> ril_test::Result<ObservedOutcome> {
        self.last_detail = None;
        if unavailable_requirement(case) {
            self.last_detail = Some("case requires a different operating system".into());
            return Ok(ObservedOutcome {
                static_status: Some(StaticStatus::UnsupportedEnvironment),
                ..Default::default()
            });
        }
        let deadline = Instant::now()
            .checked_add(self.timeout)
            .ok_or_else(|| invalid("timeout is too large"))?;
        let extracted = ril_test::extract_case(case, workspace)?;
        let workspace = &extracted.directory;
        let unit = case
            .meta
            .unit
            .unwrap_or(if case.meta.mode == Mode::RunProgram {
                Unit::Executable
            } else {
                Unit::Library
            });
        let (checked, response) = self.compile(
            self.compiler_command("check", &extracted.root, case, unit, workspace),
            deadline,
        )?;
        if checked.static_status == Some(StaticStatus::Accepted) && response.status != "accepted" {
            return Err(invalid("check returned a non-check report"));
        }
        if checked.static_status != Some(StaticStatus::Accepted) || !case.meta.mode.is_run() {
            return Ok(checked);
        }
        for helper in case.meta.build.iter().flatten() {
            let observed = self.build(
                &workspace.join(&helper.source),
                &workspace.join(&helper.output),
                case,
                workspace,
                deadline,
            )?;
            if observed.static_status != Some(StaticStatus::Accepted) {
                return Ok(observed);
            }
        }
        let stdin = case
            .meta
            .stdin
            .as_ref()
            .map(|name| fs::read(workspace.join(name)))
            .transpose()?
            .unwrap_or_default();
        if case.meta.mode == Mode::RunProgram {
            let artifacts = tempfile::tempdir_in(workspace)?;
            let program = artifacts
                .path()
                .join(if cfg!(windows) { "case.exe" } else { "case" });
            let mut observed = self.build(&extracted.root, &program, case, workspace, deadline)?;
            if observed.static_status != Some(StaticStatus::Accepted) {
                return Ok(observed);
            }
            let mut command = Command::new(program);
            command.current_dir(workspace);
            configure_invocation(&mut command, case);
            let output = capture(command, stdin, deadline)?;
            observed.runtime = Some(if output.timed_out {
                RuntimeStatus::Timeout
            } else if native_crash(output.status) {
                RuntimeStatus::NativeCrash
            } else {
                RuntimeStatus::Exited
            });
            observed.exit = output
                .status
                .and_then(|status| status.code())
                .map(i64::from);
            observed.stdout = Some(output.stdout);
            observed.stderr = Some(output.stderr);
            return Ok(observed);
        }
        let mut command =
            self.compiler_command("test", &extracted.root, case, Unit::Library, workspace);
        command.arg("--entry").arg(
            case.meta
                .entry
                .as_ref()
                .ok_or_else(|| invalid("test entry is missing"))?,
        );
        // Compiler flags and arguments to Env::args occupy separate argv regions.
        configure_invocation(&mut command, case);
        let output = capture(command, stdin, deadline)?;
        if output.timed_out || native_crash(output.status) {
            return Ok(ObservedOutcome {
                build: Some(BuildStatus::Succeeded),
                runtime: Some(if output.timed_out {
                    RuntimeStatus::Timeout
                } else {
                    RuntimeStatus::NativeCrash
                }),
                ..checked
            });
        }
        self.runtime_report(output)
    }
}

fn configure_invocation(command: &mut Command, case: &Case) {
    if let Some(args) = &case.meta.args {
        if command.get_args().next().is_some_and(|arg| arg == "test") {
            command.arg("--");
        }
        command.args(args);
    }
    for assignment in case.meta.env.iter().flatten() {
        if let Some((name, value)) = assignment.split_once('=') {
            command.env(name, value);
        }
    }
    for name in case.meta.unset_env.iter().flatten() {
        command.env_remove(name);
    }
}

impl CliAdapter {
    fn runtime_report(&mut self, output: Captured) -> ril_test::Result<ObservedOutcome> {
        let response: CompilerResponse = serde_json::from_slice(&output.stdout)
            .map_err(|error| invalid(format!("invalid test JSON: {error}")))?;
        if let Some(reason) = &response.reason {
            self.last_detail = Some(reason.to_string());
        }
        if response.status != "executed" {
            // An unavailable backend must remain incomplete, even after a successful check.
            return match response.status.as_str() {
                "not-implemented" | "unsupported-environment"
                    if output.status.and_then(|status| status.code()) == Some(2) =>
                {
                    Ok(ObservedOutcome {
                        static_status: Some(if response.status == "not-implemented" {
                            StaticStatus::NotImplemented
                        } else {
                            StaticStatus::UnsupportedEnvironment
                        }),
                        ..Default::default()
                    })
                }
                "rejected" if output.status.and_then(|status| status.code()) == Some(1) => {
                    Ok(ObservedOutcome {
                        static_status: Some(StaticStatus::Rejected),
                        errors: response
                            .diagnostics
                            .into_iter()
                            .filter(|diagnostic| diagnostic.severity.as_deref() != Some("warning"))
                            .map(|diagnostic| diagnostic.code)
                            .collect(),
                        build: Some(BuildStatus::Failed),
                        ..Default::default()
                    })
                }
                _ => Err(invalid("test command did not return an execution report")),
            };
        }
        if !output.status.is_some_and(|status| status.success()) {
            return Err(invalid(
                "test execution report contradicts process exit code",
            ));
        }
        if response
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity.as_deref() != Some("warning"))
        {
            return Err(invalid("execution report contains error diagnostics"));
        }
        let runtime = response
            .runtime
            .ok_or_else(|| invalid("execution report omitted runtime status"))?;
        if runtime == RuntimeStatus::Exited {
            return Err(invalid(
                "test functions require a classified return or panic",
            ));
        }
        Ok(ObservedOutcome {
            static_status: Some(StaticStatus::Accepted),
            build: Some(BuildStatus::Succeeded),
            runtime: Some(runtime),
            origin: response.origin,
            exit: response.exit,
            stdout: response.stdout,
            stderr: response.stderr,
            ..Default::default()
        })
    }
}

#[derive(Debug, Default, Deserialize)]
struct CompilerResponse {
    status: String,
    reason: Option<serde_json::Value>,
    #[serde(default)]
    diagnostics: Vec<CompilerDiagnostic>,
    artifact: Option<Artifact>,
    path: Option<PathBuf>,
    runtime: Option<RuntimeStatus>,
    origin: Option<ril_test::PanicOrigin>,
    exit: Option<i64>,
    stdout: Option<Vec<u8>>,
    stderr: Option<Vec<u8>>,
}
#[derive(Debug, Deserialize)]
struct CompilerDiagnostic {
    code: String,
    severity: Option<String>,
}
#[derive(Debug, Deserialize)]
struct Artifact {
    path: PathBuf,
}

struct Captured {
    status: Option<ExitStatus>,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    timed_out: bool,
}

fn native_crash(status: Option<ExitStatus>) -> bool {
    status.is_some_and(|status| status.code().is_none_or(|code| cfg!(windows) && code < 0))
}

struct ProcessCleanup(Box<dyn ChildWrapper>);
impl std::ops::Deref for ProcessCleanup {
    type Target = dyn ChildWrapper;
    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}
impl std::ops::DerefMut for ProcessCleanup {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0.as_mut()
    }
}
impl Drop for ProcessCleanup {
    fn drop(&mut self) {
        let _ = self.0.start_kill();
    }
}

// Drain all pipes concurrently so large input/output cannot deadlock the timeout loop.
fn capture(mut command: Command, input: Vec<u8>, deadline: Instant) -> io::Result<Captured> {
    command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut wrapped = CommandWrap::from(command);
    #[cfg(unix)]
    wrapped.wrap(ProcessGroup::leader());
    #[cfg(windows)]
    wrapped.wrap(JobObject);
    let mut child = ProcessCleanup(wrapped.spawn()?);
    let stdin = child
        .stdin()
        .take()
        .ok_or_else(|| io::Error::other("missing child stdin"))?;
    let stdout = child
        .stdout()
        .take()
        .ok_or_else(|| io::Error::other("missing child stdout"))?;
    let stderr = child
        .stderr()
        .take()
        .ok_or_else(|| io::Error::other("missing child stderr"))?;
    let (sender, receiver) = mpsc::channel();
    let sender_in = sender.clone();
    thread::spawn(move || {
        let result = {
            let mut stdin = stdin;
            stdin.write_all(&input)
        };
        let result = match result {
            Err(error) if error.kind() == io::ErrorKind::BrokenPipe => Ok(Vec::new()),
            result => result.map(|()| Vec::new()),
        };
        let _ = sender_in.send((0, result));
    });
    for (index, stream) in [
        (1, Box::new(stdout) as Box<dyn Read + Send>),
        (2, Box::new(stderr) as Box<dyn Read + Send>),
    ] {
        let sender = sender.clone();
        thread::spawn(move || {
            let mut bytes = Vec::new();
            let result = stream
                .take(16 * 1024 * 1024 + 1)
                .read_to_end(&mut bytes)
                .and_then(|_| {
                    if bytes.len() > 16 * 1024 * 1024 {
                        Err(io::Error::other("child output exceeded 16 MiB"))
                    } else {
                        Ok(bytes)
                    }
                });
            let _ = sender.send((index, result));
        });
    }
    drop(sender);
    let mut streams = [None, None, None];
    let mut status = None;
    let mut timed_out = false;
    loop {
        while let Ok((index, result)) = receiver.try_recv() {
            streams[index] = Some(result);
        }
        if streams
            .iter()
            .any(|stream| stream.as_ref().is_some_and(|result| result.is_err()))
        {
            child.kill()?;
            return Err(streams
                .into_iter()
                .flatten()
                .find_map(Result::err)
                .expect("checked stream error"));
        }
        if status.is_none() {
            status = child.try_wait()?;
        }
        if status.is_some() && streams.iter().all(Option::is_some) {
            break;
        }
        if Instant::now() >= deadline {
            timed_out = true;
            child.kill()?;
            status = child.try_wait()?;
            let cleanup_deadline = Instant::now() + Duration::from_secs(2);
            while streams.iter().any(Option::is_none) && Instant::now() < cleanup_deadline {
                if let Ok((index, result)) = receiver.recv_timeout(Duration::from_millis(10)) {
                    streams[index] = Some(result);
                }
            }
            break;
        }
        thread::sleep(Duration::from_millis(5));
    }
    let mut take_stream = |index: usize| {
        streams[index]
            .take()
            .unwrap_or_else(|| Err(io::Error::other("child pipe did not close after cleanup")))
    };
    take_stream(0)?;
    Ok(Captured {
        status,
        stdout: take_stream(1)?,
        stderr: take_stream(2)?,
        timed_out,
    })
}
