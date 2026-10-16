use std::{fs, process::Command};

#[test]
fn verified_generic_bodies_keep_symbolic_metadata_and_execute_with_the_managed_abi() {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("generic.ril");
    fs::write(
        &source,
        r#"
fn identity<T>(value:T)->T { value }
pub fn test_generic() {
    assert(identity(42) == 42)
    let original = .{ value: 7 }
    let same = identity(original)
    assert(same.value == 7 && original.value == 7)
}
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&source)
        .args(["--entry", "test_generic", "--json"])
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(result["status"], "executed", "{result}");
    assert_eq!(result["runtime"], "returned-unit", "{result}");
}
