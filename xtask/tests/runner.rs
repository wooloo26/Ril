//! These tests validate the harness against a subprocess fixture, not Ril conformance.
use ril_test::{Case, StaticStatus, Verdict, parse_bundle};
use std::{
    fs,
    path::PathBuf,
    process::Command,
    sync::OnceLock,
    time::{Duration, Instant},
};
use xtask::runner::{RunOptions, exclusion_reason, run_corpus};

fn compiler() -> PathBuf {
    static FIXTURE: OnceLock<tempfile::TempDir> = OnceLock::new();
    let temp = FIXTURE.get_or_init(|| {
        let temp = tempfile::tempdir().unwrap();
        let output = temp.path().join(if cfg!(windows) {
            "fake-compiler.exe"
        } else {
            "fake-compiler"
        });
        let source =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/support/fake_compiler.rs");
        let status = Command::new("rustc")
            .args(["--edition=2024", "--crate-name", "fake_compiler"])
            .arg(source)
            .arg("-o")
            .arg(&output)
            .status()
            .unwrap();
        assert!(status.success());
        temp
    });
    temp.path().join(if cfg!(windows) {
        "fake-compiler.exe"
    } else {
        "fake-compiler"
    })
}

fn case(name: &str, mode: &str, marker: &str, metadata: &str, files: &str) -> Case {
    let entry = if matches!(mode, "run-pass" | "run-panic") {
        "--@ entry: test_fixture\n"
    } else {
        ""
    };
    let expectation = match mode {
        "check-fail" => "-- Error [E0520]\n",
        "run-panic" => "-- Panics\n",
        _ => "",
    };
    let declaration = if mode == "run-program" {
        "pub fn main() {}"
    } else {
        "pub fn test_fixture() {}"
    };
    parse_bundle(&format!("--@ case: {name}\n--@ mode: {mode}\n--@ spec: SPEC#complete-provenance-and-optional-annotations\n{entry}{metadata}{expectation}--@ file: root.ril\n-- {marker}\n{declaration}\n--@ end-file\n{files}--@ end-case\n"), "tests/fixture/runner.ril").unwrap().remove(0)
}

fn options() -> RunOptions {
    RunOptions {
        compiler: compiler(),
        cases: vec![],
        filter: None,
        modes: vec![],
        applicable_only: false,
        timeout: Duration::from_secs(5),
    }
}

#[test]
fn static_selection_and_fresh_workspaces() {
    let cases = [
        case(
            "first",
            "check-pass",
            "isolated-workspace check-unit-library",
            "",
            "",
        ),
        case(
            "second",
            "check-pass",
            "isolated-workspace check-unit-executable",
            "--@ unit: executable\n",
            "",
        ),
        case("rejected", "check-fail", "check-reject", "", ""),
        case(
            "layout",
            "check-pass",
            "pointer-layout",
            "--@ target: pointer32\n",
            "",
        ),
    ];
    let execution = run_corpus(&cases, &options()).unwrap();
    assert_eq!(execution.verdict, Verdict::Pass);
    assert_eq!(execution.report.passed, 4);
    assert_eq!(execution.report.attempted, 4);
    let mut selected_modes = options();
    selected_modes.modes = vec![ril_test::Mode::CheckFail];
    let execution = run_corpus(&cases, &selected_modes).unwrap();
    assert_eq!(execution.report.selected, 1);
    assert_eq!(execution.verdict, Verdict::Pass);
    let mut options = options();
    options.filter = Some("second".into());
    assert_eq!(run_corpus(&cases, &options).unwrap().report.selected, 1);
    options.cases = vec![cases[0].id.clone()];
    assert_eq!(
        run_corpus(&cases, &options).unwrap().verdict,
        Verdict::Incomplete
    );
    options.cases = vec!["missing".into()];
    assert!(run_corpus(&cases, &options).is_err());
}

#[test]
fn cli_exposes_selection_machine_reports_and_incomplete_exit() {
    let id = "tests/conformance/provenance.ril::accept-last-use-does-not-freeze";
    let output = Command::new(env!("CARGO_BIN_EXE_xtask"))
        .args(["corpus", "run", "--json", "--case", id, "--compiler"])
        .arg(compiler())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["verdict"], "pass");
    assert_eq!(report["report"]["selected"], 1);
    assert_eq!(report["cases"][0]["id"], id);
    let output = Command::new(env!("CARGO_BIN_EXE_xtask"))
        .args([
            "corpus",
            "run",
            "--json",
            "--filter",
            "no-such-fixture",
            "--compiler",
        ])
        .arg(compiler())
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["verdict"], "incomplete");
    assert_eq!(report["report"]["selected"], 0);
}

#[test]
fn rejected_accepted_crashed_and_incomplete_cannot_be_confused() {
    for (marker, mode, expected) in [
        ("check-reject", "check-pass", Verdict::Fail),
        ("accepted", "check-fail", Verdict::Fail),
        ("compiler-crash", "check-fail", Verdict::Fail),
        ("invalid-json", "check-pass", Verdict::HarnessError),
        ("status-exit-mismatch", "check-pass", Verdict::HarnessError),
        ("check-unimplemented", "check-fail", Verdict::Incomplete),
        ("check-unsupported", "check-pass", Verdict::Incomplete),
        ("test-unimplemented", "run-pass", Verdict::Incomplete),
        ("missing-runtime", "run-pass", Verdict::HarnessError),
        ("returned-err", "run-pass", Verdict::Fail),
        ("panic-setup", "run-panic", Verdict::Fail),
        ("panic-operation", "run-panic", Verdict::Pass),
    ] {
        let execution = run_corpus(&[case("one", mode, marker, "", "")], &options()).unwrap();
        assert_eq!(execution.verdict, expected, "{marker}");
        assert_eq!(execution.report.attempted, 1);
    }
    let requires = if cfg!(windows) { "posix" } else { "windows" };
    let execution = run_corpus(
        &[case(
            "platform",
            "check-pass",
            "compiler-crash",
            &format!("--@ requires: {requires}\n"),
            "",
        )],
        &options(),
    )
    .unwrap();
    assert_eq!(execution.verdict, Verdict::Incomplete);
    assert_eq!(execution.report.attempted, 0);
    assert_eq!(execution.report.unsupported_environment, 1);
    let mut options = options();
    options.compiler = PathBuf::from("missing-compiler");
    assert_eq!(
        run_corpus(&[case("missing", "check-pass", "", "", "")], &options)
            .unwrap()
            .verdict,
        Verdict::HarnessError
    );
}

#[test]
fn helpers_arguments_environment_and_stdin_are_materialized_exactly() {
    let files = "--@ file: helper.ril\npub fn main() {}\n--@ end-file\n--@ file: input.bin hex\n00 ff 0d 0a\n--@ end-file\n";
    let metadata = "--@ build: helper.ril -> helper.exe\n--@ stdin: input.bin\n--@ args: [\"a b\",\"\"]\n--@ env: RIL_HARNESS_EMPTY=\n--@ unset-env: RIL_HARNESS_ABSENT\n";
    let execution = run_corpus(
        &[case(
            "inputs",
            "run-pass",
            "helper-required test-input",
            metadata,
            files,
        )],
        &options(),
    )
    .unwrap();
    assert_eq!(execution.verdict, Verdict::Pass, "{execution:?}");
}

#[test]
fn native_program_outputs_are_bytes_and_backend_gaps_stay_incomplete() {
    let metadata = "--@ exit: 0\n--@ stdout: expected.bin\n--@ stderr: expected.err\n--@ stdin: input.bin\n--@ args: [\"a b\",\"\",\"quoted\\\"value\",\"trailing\\\\\"]\n--@ env: RIL_HARNESS_EMPTY=\n--@ unset-env: RIL_HARNESS_ABSENT\n";
    let files = "--@ file: expected.bin hex\n00 ff 0d 0a\n--@ end-file\n--@ file: input.bin hex\n00 ff 0d 0a\n--@ end-file\n--@ file: expected.err hex\n65 72 72 0d 0a\n--@ end-file\n";
    let execution = run_corpus(
        &[case(
            "program",
            "run-program",
            "program-input",
            metadata,
            files,
        )],
        &options(),
    )
    .unwrap();
    assert_eq!(execution.verdict, Verdict::Pass, "{execution:?}");
    let execution = run_corpus(
        &[case(
            "gap",
            "run-program",
            "build-unimplemented",
            "--@ exit: 0\n",
            "",
        )],
        &options(),
    )
    .unwrap();
    assert_eq!(execution.verdict, Verdict::Incomplete);
    let execution = run_corpus(
        &[case(
            "error",
            "run-program",
            "program-failure",
            "--@ exit: 0\n",
            "",
        )],
        &options(),
    )
    .unwrap();
    assert_eq!(execution.verdict, Verdict::Fail);
}

#[test]
fn timeouts_kill_the_descendant_tree() {
    let temp = tempfile::tempdir().unwrap();
    let marker = temp.path().join("descendant-marker");
    let mut fixture = case("timeout", "check-pass", "descendant-timeout", "", "");
    // Static case metadata cannot set process environment, so use a local executable wrapper
    // fixture input marker to pass a path through its source instead.
    fixture.files[0]
        .bytes
        .extend_from_slice(format!("\n-- descendant-marker:{}\n", marker.display()).as_bytes());
    let mut options = options();
    options.timeout = Duration::from_secs(2);
    let started = Instant::now();
    let execution = run_corpus(&[fixture], &options).unwrap();
    assert!(started.elapsed() < Duration::from_secs(8));
    assert_eq!(execution.verdict, Verdict::Fail, "{execution:?}");
    assert_eq!(
        execution.cases[0].observed.as_ref().unwrap().static_status,
        Some(StaticStatus::CompilerCrash)
    );
    assert!(
        marker.exists(),
        "descendant must have started before timeout"
    );
    fs::remove_file(&marker).unwrap();
    std::thread::sleep(Duration::from_millis(150));
    assert!(!marker.exists(), "descendant survived timeout cleanup");
}

#[test]
fn applicability_excludes_only_explicit_other_os_native_execution() {
    let opposite = if cfg!(windows) { "posix" } else { "windows" };
    let cases = [
        case("win", "run-pass", "accepted", "--@ requires: windows\n", ""),
        case("posix", "run-pass", "accepted", "--@ requires: posix\n", ""),
        case("plain", "run-pass", "accepted", "", ""),
        case(
            "layout",
            "check-pass",
            "pointer-layout",
            "--@ target: pointer32\n",
            "",
        ),
        case(
            "static-other-os",
            "check-pass",
            "compiler-crash",
            &format!("--@ target: pointer64\n--@ requires: {opposite}\n"),
            "",
        ),
        case(
            "tool-gap",
            "run-pass",
            "check-unsupported",
            "--@ requires: filesystem\n",
            "",
        ),
    ];
    let original = run_corpus(&cases, &options()).unwrap();
    assert_eq!(original.report.selected, 6);
    assert!(original.excluded.is_empty());
    let mut filtered = options();
    filtered.applicable_only = true;
    let execution = run_corpus(&cases, &filtered).unwrap();
    assert_eq!(execution.report.selected, 5);
    assert_eq!(execution.report.attempted, 4);
    assert_eq!(execution.report.passed, 3);
    assert_eq!(execution.report.unsupported_environment, 2);
    assert_eq!(execution.verdict, Verdict::Incomplete);
    assert_eq!(execution.excluded.len(), 1);
    assert!(
        execution.excluded[0]
            .id
            .ends_with(if cfg!(windows) { "::posix" } else { "::win" })
    );
    assert!(
        execution.excluded[0]
            .reason
            .contains("native case explicitly requires")
    );
    assert!(
        execution
            .cases
            .iter()
            .any(|case| case.id.ends_with("::static-other-os"))
    );
    assert!(
        execution
            .cases
            .iter()
            .any(|case| case.id.ends_with("::tool-gap") && case.verdict == Verdict::Incomplete)
    );
    let json = serde_json::to_value(&execution).unwrap();
    assert!(json["excluded"][0]["reason"].is_string());
    let mut both = case(
        "both",
        "run-pass",
        "accepted",
        "--@ requires: windows\n",
        "",
    );
    both.meta.requires = Some(vec![
        ril_test::Capability::Windows,
        ril_test::Capability::Posix,
    ]);
    assert!(exclusion_reason(&both, "x86_64-pc-windows-msvc").is_none());
    assert!(exclusion_reason(&cases[0], "unknown-host").is_none());
}

#[test]
fn supported_platform_selection_union_covers_the_entire_language_corpus() {
    use std::collections::BTreeSet;
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap();
    let cases = ril_test::discover_cases(&root.join("tests")).unwrap();
    let select = |host| {
        cases
            .iter()
            .filter(|case| exclusion_reason(case, host).is_none())
            .map(|case| case.id.clone())
            .collect::<BTreeSet<_>>()
    };
    let windows = select("x86_64-pc-windows-msvc");
    let linux = select("x86_64-unknown-linux-gnu");
    let all: BTreeSet<_> = cases.iter().map(|case| case.id.clone()).collect();
    assert_eq!(windows.union(&linux).cloned().collect::<BTreeSet<_>>(), all);
    for case in cases.iter().filter(|case| !case.meta.mode.is_run()) {
        assert!(windows.contains(&case.id) && linux.contains(&case.id));
    }
}

#[test]
fn applicability_cli_reports_exclusion_without_turning_it_into_a_pass() {
    let id = if cfg!(windows) {
        "tests/stdlib/native.ril::posix-bytes"
    } else {
        "tests/stdlib/native.ril::windows-units"
    };
    let output = Command::new(env!("CARGO_BIN_EXE_xtask"))
        .args([
            "corpus",
            "run",
            "--json",
            "--applicable-only",
            "--case",
            id,
            "--compiler",
        ])
        .arg(compiler())
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["report"]["selected"], 0);
    assert_eq!(report["report"]["passed"], 0);
    assert_eq!(report["verdict"], "incomplete");
    assert_eq!(report["excluded"][0]["id"], id);
    assert!(report["cases"].as_array().unwrap().is_empty());
}
