use std::{fs, process::Command};

fn report(source: &str, execute: bool) -> serde_json::Value {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("static-result-loops.ril");
    fs::write(&input, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_ril"));
    command
        .arg(if execute { "test" } else { "check" })
        .arg(input)
        .arg("--json");
    if execute {
        command.args(["--entry", "test_native"]);
    }
    let output = command.output().unwrap();
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap_or_else(|_| {
        panic!(
            "{:?}\n{}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    if execute {
        assert!(output.status.success(), "{report}");
        assert_eq!(report["status"], "executed", "{report}");
        assert_eq!(report["runtime"], "returned-unit", "{report}");
        assert_eq!(report["exit"], 0, "{report}");
    } else {
        assert!(
            !output.status.success(),
            "negative check was accepted: {report}"
        );
    }
    report
}

#[test]
fn loop_last_publication_preserves_producers_aliases_and_clone_duties() {
    report(
        r#"
meta let ROOT={
    let value:Result<int,str>=loop {last Ok(7)}
    assert(value is Ok(7))
    (value,value)
}
pub fn test_native() &{ROOT}{
    assert(ROOT.0 is Ok(7))
    assert(ROOT.1 is Ok(7))
    let copied=clone(ROOT)
    assert(copied.0 is Ok(7))
    assert(copied.1 is Ok(7))
}
"#,
        true,
    );
}

#[test]
fn exact_array_and_map_iterations_publish_reached_receipts() {
    report(
        r#"
meta let ROOT={
    let values:[2]Result<int,str>=[Ok(1),Err("two")]
    for values as value {assert(value is Ok(_)|Err(_))}
    for ["first":values[0],"second":values[1]] as (key,value) {
        assert(value is Ok(_)|Err(_))
    }
    values
}
pub fn test_native() &{ROOT}{
    assert(ROOT[0] is Ok(1))
    assert(ROOT[1] is Err("two"))
    let copied=clone(ROOT)
    assert(copied[0] is Ok(1))
    assert(copied[1] is Err("two"))
}
"#,
        true,
    );
}

#[test]
fn return_from_a_loop_and_later_member_inspection_keep_the_same_duties() {
    report(
        r#"
meta fn make()->Result<int,str>{for [1] as item {return Ok(7)};Err("empty")}
meta let ROOT={
    let values:[2]Result<int,str>=[make(),Ok(9)]
    for values as value {assert(value is Ok(_));last}
    assert(values[1] is Ok(9))
    values
}
pub fn test_native() &{ROOT}{assert(ROOT[0] is Ok(7));assert(ROOT[1] is Ok(9))}
"#,
        true,
    );
}

#[test]
fn skipped_iterations_and_unvisited_definition_paths_are_rejected() {
    for source in [
        "meta fn checked(flag:bool){let value=Ok(7);while flag {assert(value is Ok(7));last};()}",
        "meta let _=for [Ok(1),Ok(2)] as value {assert(value is Ok(_));last}",
        "meta let _=for [true,false] as flag {let value=Ok(7);if flag {next};assert(value is Ok(7))}",
    ] {
        let value = report(source, false);
        assert_eq!(value["status"], "rejected", "{value}");
        assert!(
            value["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|diagnostic| diagnostic["code"] == "E0720"),
            "{value}"
        );
    }
}

#[test]
fn rounded_float_equality_is_not_an_unrounded_static_branch_certificate() {
    for source in [
        "meta fn checked(){let value=Ok(7);let rounded:f32=16777217;loop {if rounded==16777216 {last}else {assert(value is Ok(7));last}}}",
        "meta fn checked(){let value=Ok(7);let rounded:f32=16777217;if rounded==16777216 {()}else {assert(value is Ok(7))};()}",
    ] {
        let value = report(source, false);
        assert_eq!(value["status"], "not-implemented", "{source}\n{value}");
    }
}
