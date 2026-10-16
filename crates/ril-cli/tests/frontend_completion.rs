use std::{fs, process::Command};

fn execute(source_text: &str) -> serde_json::Value {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("frontend.ril");
    fs::write(&source, source_text).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&source)
        .args(["--entry", "test_frontend", "--json"])
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

#[test]
fn closed_record_rests_extract_remaining_fields_after_one_source_evaluation() {
    let result = execute(
        r#"
var calls=0
fn source()->{id:int,name:str,stamp:int} &{mut calls} {
    calls+=1
    .{id:1,name:"Ada",stamp:7}
}
pub fn test_frontend() &{mut calls} {
    let .{id,..rest}=source()
    assert(calls==1 && id==1 && rest.name=="Ada" && rest.stamp==7)
    let .{..empty}=.{ }
    assert(empty==.{ })
}
"#,
    );
    assert_eq!(result["runtime"], "returned-unit", "{result}");
}

#[test]
fn checked_arithmetic_and_independent_shift_counts_execute() {
    let result = execute(
        r#"
pub fn test_frontend() {
    assert(10/?0==None && 10%?0==None)
    assert(-128i8/?-1i8==None)
    assert(10/?2==Some(5))
    let small:?u8=10/?2
    assert(small==Some(5u8))
    assert(1u8<<2i16==4u8)
    let shifted:u8=1<<2i16
    assert(shifted==4u8)
    var changing=1u8
    changing<<=2i16
    changing>>=1i32
    assert(changing==2u8)
    meta let EXPECTED=4
    assert(4 is EXPECTED && Some(4) is Some(EXPECTED))
}
"#,
    );
    assert_eq!(result["runtime"], "returned-unit", "{result}");
    let result = execute("pub fn test_frontend(){let _=1u8 << -1}");
    assert_eq!(result["runtime"], "language-panic", "{result}");
    let result = execute(
        "type Guard={mut on_close:fn()->()}\npub fn test_frontend(){var value=1u8;let scoped mut guard=Guard.{on_close:\\->assert(value==1u8)};value<<=-1}",
    );
    assert_eq!(result["runtime"], "language-panic", "{result}");
}
