//! Nested generic row transport uses the caller's actual graph and duties.
use std::{fs, process::Command};

#[test]
fn nested_rows_keep_member_identity_and_result_payloads_at_runtime() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("row-transport.ril");
    fs::write(
        &path,
        r#"
type Cell={mut value:int}
fn carry<R>(item:{..R})->[]{..R}{[item]}
fn pair<R>(item:{..R})->({..R},{..R}){(item,item)}
fn nested<R>(item:{payload:[]{..R}})->{payload:[]{..R}}{item}
fn optional<R>(item:?{..R})->?{..R}{item}
fn mapped<R>(items:[str:{..R}])->[str:{..R}]{items}
fn wrapped<R>(item:{..R})->Result<{..R},str>{Ok(item)}
pub fn test_native(){
    let mut original=Cell.{value:1}
    let view aliases=pair(.{child:^mut original})
    let view nested_alias=nested(.{payload:carry(.{child:^mut original})})
    original.value=9
    assert(aliases.0.child.value==9 && aliases.1.child.value==9)
    assert(nested_alias.payload[0].child.value==9)
    let view maybe=optional(Some(.{child:^mut original}))
    assert((maybe ?? panic("missing")).child.value==9)
    let view map=mapped(["selected":.{child:^mut original}])
    assert((map["selected"] ?? panic("missing")).child.value==9)
    let view result=wrapped(.{answer:Ok(7)})
    match result{Ok(item)->assert(item.answer is Ok(7)),Err(_)->panic("unexpected")}
    let view isolated=carry(.{child:clone_immut(original)})
    original.value=12
    assert(isolated[0].child.value==9)
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
