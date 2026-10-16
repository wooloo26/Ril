//! Copy qualification follows actual payloads while graph copying preserves cycles.
use std::{fs, process::Command};

#[test]
fn binary_recursive_resource_sibling_is_rejected_without_execution() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory
        .path()
        .join("binary-recursive-resource-negative.ril");
    fs::write(
        &path,
        ril_test::case_source(
            "tests/regressions/copy.ril::binary-recursive-copy-resource-negative",
        ),
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("check")
        .arg(&path)
        .arg("--json")
        .output()
        .unwrap();
    assert!(!output.status.success(), "negative source was accepted");
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["status"], "rejected", "{report}");
    assert!(
        report["diagnostics"]
            .as_array()
            .unwrap()
            .iter()
            .any(|diagnostic| diagnostic["code"] == "E0530"),
        "{report}"
    );
}

#[test]
fn binary_recursive_copies_preserve_both_cycles_and_shared_child_identity() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("binary-recursive-copy.ril");
    fs::write(
        &path,
        ril_test::case_source("tests/regressions/copy.ril::binary-recursive-copy"),
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&path)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["runtime"], "returned-unit", "{report}");
    assert_eq!(report["exit"], 0, "{report}");
}

#[test]
fn witnessed_payloads_and_closed_recursive_copies_execute() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("copy-boundaries.ril");
    fs::write(
        &path,
        r#"
use ril/file
type Node={mut value:int,mut following:?Node}
fn copy(depth:int,source:Node)->Node{if depth==0{clone(source)}else{copy(depth-1,source)}}
pub fn test_native(){
    let absent:?File::Handle=None
    assert(clone(absent) is None)
    assert(clone_immut(absent) is None)
    let view wrapper=.{item:absent}
    assert(clone(wrapper).item is None)
    assert(clone_immut(wrapper).item is None)
    let original:Result<fn()->int,str>=Ok(\->7)
    assert(original is Ok(_)|Err(_))
    let copied=clone(original)
    let callback=copied ?? \_error->panic("unexpected")
    assert(callback()==7)
    let mut node=Node.{value:1,following:None}
    node.following=Some(^mut node)
    let mut independent=^mut copy(2,node)
    independent.value=9
    assert(independent.following?.value==Some(9))
    assert(node.following?.value==Some(1))
}
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&path)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["runtime"], "returned-unit", "{report}");
    assert_eq!(report["exit"], 0, "{report}");
}
