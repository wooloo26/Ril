//! Independent process limits guard against an interpreter memory regression.
use std::{fs, process::Command};

fn bounded(source: &str, budget: u64) -> serde_json::Value {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("capture.ril");
    fs::write(&path, source).unwrap();
    #[cfg(windows)]
    let mut compiler = {
        let mut command = Command::new("powershell.exe");
        command.args([
            "-NoProfile",
            "-NonInteractive",
            "-ExecutionPolicy",
            "Bypass",
            "-File",
        ]);
        command.arg(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/support/bounded_static.ps1"
        ));
        command
            .arg(env!("CARGO_BIN_EXE_ril"))
            .arg(&path)
            .arg(budget.to_string())
            .arg(directory.path());
        command
    };
    #[cfg(unix)]
    let mut compiler = {
        let mut command = Command::new("bash");
        command.args([
            "-c",
            "ulimit -v 524288 || exit 125; exec timeout -k 1s 20s \"$@\"",
            "--",
        ]);
        command
            .arg(env!("CARGO_BIN_EXE_ril"))
            .arg("check")
            .arg(&path)
            .args(["--json", "--static-budget", &budget.to_string()]);
        command
    };
    let output = compiler.output().unwrap();
    #[cfg(windows)]
    let bytes = {
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let envelope: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(envelope["timeout"], false, "{envelope}");
        assert_eq!(envelope["memory_limit_bytes"], 536_870_912u64);
        assert_eq!(envelope["verified_job_flags"], 0x100u64);
        assert!(
            envelope["peak_process_commit_bytes"].as_u64().unwrap() < 536_870_912,
            "{envelope}"
        );
        assert!(
            matches!(envelope["exit"].as_i64(), Some(1 | 2)),
            "{envelope}"
        );
        envelope["stdout"].as_str().unwrap().as_bytes().to_vec()
    };
    #[cfg(unix)]
    let bytes = {
        assert!(
            matches!(output.status.code(), Some(1 | 2)),
            "exit={:?}\n{}\n{}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        output.stdout
    };
    serde_json::from_slice(&bytes).unwrap_or_else(|_| {
        panic!(
            "Compiler did not return JSON: {}",
            String::from_utf8_lossy(&bytes)
        )
    })
}

#[test]
fn large_captured_environment_stops_before_deep_clone_and_keeps_language_quota() {
    // Same bytes and syntax as the original bounded-memory failure. Every loop
    // iteration creates a fresh declaration environment retaining BIG.
    let source = format!(
        "meta let BIG=\"{}\"\nmeta fn spin(){{loop{{next; where meta fn unused()->str{{BIG}}}}}}\nmeta let _=spin()\n",
        "x".repeat(1_048_576)
    );
    let report = bounded(&source, 100_000);
    assert_eq!(report["status"], "not-implemented", "{report}");
    assert!(
        report["reason"]["detail"]
            .as_str()
            .unwrap()
            .contains("work allowance exhausted"),
        "{report}"
    );
    let report = bounded(&source, 1);
    assert_eq!(report["status"], "rejected", "{report}");
    assert!(
        report["diagnostics"]
            .as_array()
            .unwrap()
            .iter()
            .any(|diagnostic| diagnostic["code"] == "E0811"),
        "{report}"
    );
}
