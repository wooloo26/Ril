use std::{fs, process::Command};
fn report(source: &str, execute: bool) -> serde_json::Value {
    let dir = tempfile::tempdir().unwrap();
    let input = dir.path().join("static_results.ril");
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
    serde_json::from_slice(&output.stdout).unwrap_or_else(|_| {
        panic!(
            "{:?}\n{}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}
fn executes(source: &str) {
    let value = report(source, true);
    assert_eq!(value["status"], "executed", "{value}");
    assert_eq!(value["runtime"], "returned-unit", "{value}");
}

#[test]
fn checked_static_results_and_their_aliases_reach_native_constants() {
    executes(
        r#"
meta let ROOT={
    let value:Result<f32,str>=Ok(18014399583223809)
    assert(value is Ok(18014400656965632.0f32))
    (value,value)
}
pub fn test_native() &{ROOT}{
    assert(ROOT.0 is Ok(18014400656965632.0f32))
    assert(ROOT.1 is Ok(18014400656965632.0f32))
    let copied=clone(ROOT)
    assert(copied.0 is Ok(18014400656965632.0f32))
}
"#,
    );
}

#[test]
fn nested_results_preserve_both_tags_and_new_copy_duties() {
    executes(
        r#"
meta let ROOT:Result<Result<int,str>,str>={
    let inner=Ok(7)
    let outer=Ok(inner)
    assert(outer is Ok(Ok(7)))
    outer
}
pub fn test_native() &{ROOT}{
    assert(ROOT is Ok(Ok(7)))
    let copied=clone(ROOT)
    assert(copied is Ok(Ok(7)))
}
"#,
    );
}

#[test]
fn both_meta_return_tags_have_their_own_checked_publication() {
    executes(
        r#"
meta fn make(flag:bool)->Result<int,str>{if flag{Ok(7)}else{Err("bad")}}
meta let FIRST={let value=make(true);assert(value is Ok(7));value}
meta let SECOND={let value=make(false);assert(value is Err("bad"));value}
pub fn test_native() &{FIRST,SECOND}{
    assert(FIRST is Ok(7))
    assert(SECOND is Err("bad"))
}
"#,
    );
}

#[test]
fn unrelated_producers_copies_and_unvisited_definition_paths_are_rejected() {
    for source in [
        "meta fn bad(flag:bool){let value=Ok(7);if flag{assert(value is Ok(_))};()}\nmeta let _=bad(true)",
        "meta let _={let inner=Ok(7);let outer=Ok(inner);assert(outer is Ok(_))}",
        "meta let ROOT:Result<int,str>={let value=Ok(7);assert(value is Ok(7));value}\nfn bad() &{ROOT}{let copied=clone(ROOT)}",
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
fn pending_static_publication_is_explicitly_incomplete() {
    let value = report(
        "meta let ROOT:Result<int,str>=Ok(7)\nfn later() &{ROOT}{assert(ROOT is Ok(7))}",
        false,
    );
    assert_eq!(value["status"], "not-implemented", "{value}");
}
