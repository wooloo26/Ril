use std::{fs, process::Command};
#[test]
fn source_commands_are_explicitly_incomplete_and_do_not_emit_files() {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("main.ril");
    fs::write(&input, "pub fn main() {}").unwrap();
    for mode in ["check", "build"] {
        let output = Command::new(env!("CARGO_BIN_EXE_ril"))
            .arg(mode)
            .arg(&input)
            .arg("--json")
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2));
        let json: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(json["status"], "not-implemented");
    }
    assert_eq!(fs::read_dir(temp.path()).unwrap().count(), 1);
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
fn lists_only_the_two_initial_targets() {
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .args(["targets", "--json"])
        .output()
        .unwrap();
    assert!(output.status.success());
    let targets: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(targets.as_array().unwrap().len(), 2);
}
