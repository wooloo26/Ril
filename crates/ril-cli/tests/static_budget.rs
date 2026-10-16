use std::{fs, process::Command};

#[test]
fn cli_configures_each_static_root_and_rejects_zero_allowance() {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("quota.ril");
    fs::write(&source, "meta fn one()->int{1}\nmeta fn two()->int{one()}\nmeta let FIRST=two()\nmeta let SECOND=two()").unwrap();
    for (quota, expected) in [(1, "rejected"), (2, "accepted")] {
        let output = Command::new(env!("CARGO_BIN_EXE_ril"))
            .arg("check")
            .arg(&source)
            .args(["--json", "--static-budget", &quota.to_string()])
            .output()
            .unwrap();
        let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(report["status"], expected, "{report}");
        if quota == 1 {
            assert!(
                report["diagnostics"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|d| d["code"] == "E0811"),
                "{report}"
            );
        }
    }
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("check")
        .arg(source)
        .args(["--static-budget", "0"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("--static-budget"));
}

#[test]
fn escaping_static_declaration_groups_emit_their_own_native_constants() {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("lexical.ril");
    fs::write(
        &source,
        r#"
meta fn make(value:int)->fn()->int{
    first
    where
    meta fn first()->int{second()}
    meta fn second()->int{value}
}
meta fn observe()->(int,int){
    let first=make(7)
    let second=make(9)
    (first(),second())
}
meta let VALUES=observe()
pub fn test_native() &{VALUES}{assert(VALUES.0==7 && VALUES.1==9)}
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(source)
        .args(["--json", "--entry", "test_native", "--static-budget", "7"])
        .output()
        .unwrap();
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], "returned-unit", "{report}");
}
