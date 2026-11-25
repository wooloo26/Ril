use std::{
    collections::BTreeSet,
    fs,
    io::{self, Read},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
    thread,
    time::{Duration, Instant},
};

use libtest_mimic::{Arguments, Failed, Trial};
use ril_base::{
    diag::Diagnostic,
    span::{FileId, SourceFile},
};

use crate::{
    Case, CaseMode, CheckResult, ExecOutput, Stage, Suite, TestDriver, VirtualPackage, WorkerError,
    parse_suite, protocol::Backend,
};

pub fn run_harness(path: &Path, driver: Arc<dyn TestDriver>) -> ! {
    let args = Arguments::from_args();
    let cases = (|| {
        let max_stage = match std::env::var("RIL_TEST_STAGE") {
            Ok(text) => text.parse::<Stage>()?,
            Err(std::env::VarError::NotPresent) => Stage::Run,
            Err(err) => return Err(err.to_string()),
        };
        Ok(trials(discover(path)?, driver, max_stage))
    })()
    .unwrap_or_else(|error: String| {
        vec![Trial::test("suite_discovery", move || {
            Err(Failed::from(error))
        })]
    });
    libtest_mimic::run(&args, cases).exit()
}

pub fn discover(path: &Path) -> Result<Vec<Suite>, String> {
    let mut paths = Vec::new();
    collect_paths(path, &mut paths).map_err(|err| format!("{}: {err}", path.display()))?;
    paths.sort_unstable();
    let mut suites = Vec::new();
    let mut names = BTreeSet::new();
    for path in paths {
        let source =
            fs::read_to_string(&path).map_err(|err| format!("{}: {err}", path.display()))?;
        let suite = parse_suite(&path, &source).map_err(|err| err.to_string())?;
        if !names.insert(suite.name.clone()) {
            return Err(format!(
                "{}: duplicate suite name {}",
                path.display(),
                suite.name
            ));
        }
        suites.push(suite);
    }
    if suites.is_empty() {
        return Err(format!("{}: no .ril test suites found", path.display()));
    }
    Ok(suites)
}

fn collect_paths(path: &Path, paths: &mut Vec<PathBuf>) -> io::Result<()> {
    if path.is_dir() {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            if !entry.file_type()?.is_symlink() {
                collect_paths(&entry.path(), paths)?;
            }
        }
    } else if path.extension().is_some_and(|ext| ext == "ril") {
        paths.push(path.into());
    }
    Ok(())
}

pub fn trials(suites: Vec<Suite>, driver: Arc<dyn TestDriver>, max_stage: Stage) -> Vec<Trial> {
    suites
        .into_iter()
        .flat_map(|suite| {
            let driver = Arc::clone(&driver);
            suite.cases.into_iter().map(move |case| {
                let driver = Arc::clone(&driver);
                let location = format!("{}:{}", suite.path.display(), case.line);
                let name = format!("{}::{}", suite.name, case.id);
                let pending = case.stage > max_stage;
                Trial::test(name, move || {
                    run_case(&case, driver.as_ref())
                        .map_err(|err| Failed::from(format!("{location}: {err}")))
                })
                .with_ignored_flag(pending)
            })
        })
        .collect()
}

pub fn run_case(case: &Case, driver: &dyn TestDriver) -> Result<(), String> {
    match case.mode {
        CaseMode::CompilePass | CaseMode::CompileFail(_) => {
            check(case, &driver.check_stage(&case.pkg, case.stage))
        }
        CaseMode::CompatPass | CaseMode::CompatFail(_) => {
            let base = case.baseline.as_ref().ok_or("missing baseline")?;
            check(case, &driver.check_compat(base, &case.pkg))
        }
        CaseMode::RunPass | CaseMode::RunPanic(_) | CaseMode::RunAbort => execute(case, driver),
    }
}

fn check(case: &Case, result: &CheckResult) -> Result<(), String> {
    let diagnostics = &result.diagnostics;
    let codes: BTreeSet<_> = diagnostics.iter().filter_map(|d| d.code).collect();
    let expected = match case.mode {
        CaseMode::CompileFail(code) | CaseMode::CompatFail(code) => Some(code),
        _ => None,
    };

    let fail = |message: String| {
        let output = diagnostics
            .iter()
            .map(|diag| {
                if let Some(line) = diagnostic_line(&case.pkg, result, diag) {
                    format!("suite line {line}: {diag}")
                } else {
                    diag.to_string()
                }
            })
            .collect::<Vec<_>>()
            .join("\n");
        if output.is_empty() {
            message
        } else {
            format!("{message}\n{output}")
        }
    };
    if diagnostics.iter().any(|d| d.code.is_none()) {
        return Err(fail("compiler failed to check this case".into()));
    }
    if let Some(code) = expected {
        if !codes.contains(&code) {
            return Err(fail(format!("expected {code}")));
        }
    } else if !diagnostics.is_empty() {
        return Err(fail("expected a successful compilation".into()));
    }
    if let Some(&code) = case.forbidden.iter().find(|code| codes.contains(code)) {
        return Err(fail(format!("unexpected {code}")));
    }
    if let Some(primary) = case.primary
        && diagnostics.first().and_then(|d| d.code) != Some(primary)
    {
        return Err(fail(format!("expected primary diagnostic {primary}")));
    }
    for &(line, code) in &case.markers {
        if !diagnostics
            .iter()
            .any(|d| d.code == Some(code) && diagnostic_line(&case.pkg, result, d) == Some(line))
        {
            return Err(fail(format!("expected {code} at suite line {line}")));
        }
    }
    for (name, expected) in &case.signatures {
        let actual = result.signatures.get(name).map(String::as_str);
        if actual != Some(expected) {
            return Err(fail(format!(
                "expected signature {expected:?} for {name}, got {actual:?}"
            )));
        }
    }
    Ok(())
}

fn diagnostic_line(
    pkg: &VirtualPackage,
    result: &CheckResult,
    diagnostic: &Diagnostic,
) -> Option<usize> {
    let span = diagnostic.primary?;
    let file = result
        .file_paths
        .get(&span.file)
        .and_then(|path| pkg.files.get(path))
        .or_else(|| {
            let FileId(index) = span.file;
            pkg.files.iter().nth(index).map(|(_, file)| file)
        })?;
    let line = if let Ok(source) = SourceFile::from_bytes(span.file, pkg.entry.clone(), &file.bytes)
    {
        source.location(span.start)?.line
    } else {
        file.bytes
            .get(..span.start)?
            .iter()
            .filter(|&&b| b == b'\n')
            .count()
            + 1
    };
    file.suite_line(line)
}

fn display_diagnostics(diagnostics: &[Diagnostic]) -> String {
    diagnostics
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n")
}

fn execute(case: &Case, driver: &dyn TestDriver) -> Result<(), String> {
    let checked = driver.check_stage(&case.pkg, case.stage);
    check(case, &checked)?;
    let mut outputs = Vec::new();
    if case.backend != Backend::Aot {
        outputs.push((
            "jit",
            driver
                .run_jit(&case.pkg)
                .map_err(|ds| display_diagnostics(&ds))?,
        ));
    }
    if case.backend != Backend::Jit {
        let directory = tempfile::tempdir().map_err(|err| err.to_string())?;
        let binary = directory
            .path()
            .join(format!("case{}", std::env::consts::EXE_SUFFIX));
        driver
            .build_aot(&case.pkg, &binary)
            .map_err(|ds| display_diagnostics(&ds))?;
        let output = run_worker(&mut Command::new(binary)).map_err(|err| err.to_string())?;
        outputs.push(("aot", output));
    }
    for (backend, output) in &outputs {
        check_output(case, output).map_err(|message| format!("{backend}: {message}"))?;
    }
    if let [(_, jit), (_, aot)] = outputs.as_slice()
        && (jit.stdout != aot.stdout || jit.stderr != aot.stderr || jit.status != aot.status)
    {
        return Err("JIT and AOT output or exit status differs".into());
    }
    Ok(())
}

fn check_output(case: &Case, output: &ExecOutput) -> Result<(), String> {
    let stderr = String::from_utf8_lossy(&output.stderr);
    let exit = output.status.code();
    match &case.mode {
        CaseMode::RunPass if exit != Some(case.exit.unwrap_or(0)) => {
            return Err(format!("unexpected status {}\n{stderr}", output.status));
        }
        CaseMode::RunPanic(message) => {
            let reported = stderr
                .lines()
                .find_map(|line| line.strip_prefix("[RIL_RT_PANIC]"));
            if exit != Some(case.exit.unwrap_or(1)) || reported.is_none() {
                return Err(format!(
                    "expected a Ril panic, got {}\n{stderr}",
                    output.status
                ));
            }
            if let Some(message) = message
                && reported.map(str::trim) != Some(message.as_str())
            {
                return Err(format!(
                    "expected panic message {message:?}, got {stderr:?}"
                ));
            }
        }
        CaseMode::RunAbort
            if !is_abort(output.status)
                || !stderr
                    .lines()
                    .any(|line| line == "[RIL_RT_ABORT:DOUBLE_PANIC]") =>
        {
            return Err(format!(
                "expected a double panic abort, got {}\n{stderr}",
                output.status
            ));
        }
        _ => {}
    }
    if let Some(expected) = &case.stdout
        && *expected != output.stdout
    {
        return Err(format!(
            "expected stdout {:?}, got {:?}",
            String::from_utf8_lossy(expected),
            String::from_utf8_lossy(&output.stdout)
        ));
    }
    Ok(())
}

#[cfg(unix)]
fn is_abort(status: std::process::ExitStatus) -> bool {
    use std::os::unix::process::ExitStatusExt as _;
    status.signal() == Some(6)
}

#[cfg(windows)]
fn is_abort(status: std::process::ExitStatus) -> bool {
    status.code() == Some(3)
}

#[cfg(not(any(unix, windows)))]
fn is_abort(_status: std::process::ExitStatus) -> bool {
    false
}

const OUTPUT_LIMIT: usize = 1024 * 1024;
const WORKER_TIMEOUT: Duration = Duration::from_secs(5);

pub fn run_worker(command: &mut Command) -> Result<ExecOutput, WorkerError> {
    let wrap = |err: io::Error| WorkerError(err.to_string());
    let mut child = command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(wrap)?;
    let total = Arc::new(AtomicUsize::new(0));
    let stdout = read_pipe(
        child
            .stdout
            .take()
            .ok_or_else(|| WorkerError("worker stdout unavailable".into()))?,
        Arc::clone(&total),
    );
    let stderr = read_pipe(
        child
            .stderr
            .take()
            .ok_or_else(|| WorkerError("worker stderr unavailable".into()))?,
        Arc::clone(&total),
    );
    let start = Instant::now();
    let mut status = None;
    loop {
        if total.load(Ordering::Relaxed) > OUTPUT_LIMIT || start.elapsed() >= WORKER_TIMEOUT {
            let _ = child.kill();
            let _ = child.wait();
            return Err(WorkerError(
                if total.load(Ordering::Relaxed) > OUTPUT_LIMIT {
                    "worker exceeded 1 MiB output limit".into()
                } else {
                    "worker exceeded 5s timeout".into()
                },
            ));
        }
        if status.is_none() {
            status = child.try_wait().map_err(wrap)?;
        }
        if let Some(status) = status
            && stdout.is_finished()
            && stderr.is_finished()
        {
            let collect = |reader: thread::JoinHandle<io::Result<Vec<u8>>>| {
                reader
                    .join()
                    .map_err(|_| WorkerError("worker output reader panicked".into()))?
                    .map_err(wrap)
            };
            return Ok(ExecOutput {
                stdout: collect(stdout)?,
                stderr: collect(stderr)?,
                status,
            });
        }
        thread::sleep(Duration::from_millis(5));
    }
}

fn read_pipe(
    mut pipe: impl Read + Send + 'static,
    total: Arc<AtomicUsize>,
) -> thread::JoinHandle<io::Result<Vec<u8>>> {
    thread::spawn(move || {
        let mut result = Vec::new();
        let mut buffer = [0; 8192];
        loop {
            let count = pipe.read(&mut buffer)?;
            if count == 0 || total.fetch_add(count, Ordering::Relaxed) + count > OUTPUT_LIMIT {
                return Ok(result);
            }
            if let Some(bytes) = buffer.get(..count) {
                result.extend_from_slice(bytes);
            }
        }
    })
}
