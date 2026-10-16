use std::{fs, process::Command};
#[test]
fn source_commands_verify_emit_link_and_execute_real_native_code() {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("main.ril");
    fs::write(&input, "pub fn main() { assert(20 + 22 == 42) }").unwrap();
    let executable = temp.path().join(if cfg!(windows) {
        "program.exe"
    } else {
        "program"
    });
    for mode in ["check", "build"] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_ril"));
        command.arg(mode).arg(&input).arg("--json");
        if mode == "build" {
            command
                .arg("--output")
                .arg(&executable)
                .args(["--unit", "executable"]);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.code(),
            Some(0),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let json: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(
            json["status"],
            if mode == "check" { "accepted" } else { "built" }
        );
    }
    assert!(Command::new(&executable).status().unwrap().success());
    fs::write(&input, [0xff]).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("check")
        .arg(&input)
        .arg("--json")
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    let json: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(json["diagnostics"][0]["code"], "E0104");
}

#[test]
fn test_reports_language_panic_separately_from_process_failure() {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("panic.ril");
    fs::write(
        &input,
        "pub fn test_failure() { panic(\"designated defect\") }",
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&input)
        .args(["--entry", "test_failure", "--json"])
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let json: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(json["status"], "executed");
    assert_eq!(json["runtime"], "language-panic");
    assert_eq!(json["exit"], 1);
    let stderr: Vec<u8> = serde_json::from_value(json["stderr"].clone()).unwrap();
    assert_eq!(stderr, b"designated defect\n");
}
#[test]
fn lists_only_the_two_initial_targets() {
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .args(["targets", "--json"])
        .output()
        .unwrap();
    assert!(output.status.success());
    let targets: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(targets.as_array().unwrap().len(), 2);
}

#[test]
fn a_valid_deep_expression_reports_the_syntax_budget_without_crashing_the_cli() {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("deep.ril");
    fs::write(
        &source,
        format!(
            "fn example()->int{{{}1{}}}",
            "(".repeat(1000),
            ")".repeat(1000)
        ),
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("check")
        .arg(&source)
        .arg("--json")
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(2),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["status"], "not-implemented");
    assert_eq!(report["reason"]["stage"], "syntax");
}

#[test]
fn abstract_layout_checks_do_not_become_native_targets() {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("layout.ril");
    fs::write(&source, "pub fn main() {}").unwrap();
    let check = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("check")
        .arg(&source)
        .args(["--target", "pointer32", "--json"])
        .output()
        .unwrap();
    assert!(
        check.status.success(),
        "{}",
        String::from_utf8_lossy(&check.stdout)
    );
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("build")
        .arg(&source)
        .args(["--target", "pointer32", "--json"])
        .output()
        .unwrap();
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["status"], "unsupported-environment", "{report}");
    assert!(
        !source
            .with_extension(if cfg!(windows) { "exe" } else { "" })
            .exists()
    );
}
