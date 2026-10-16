use std::{fs, process::Command};

fn run(source: &str) -> serde_json::Value {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("nested_result.ril");
    fs::write(&input, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(input)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    serde_json::from_slice(&output.stdout).unwrap_or_else(|_| {
        panic!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

fn executes(source: &str) {
    let report = run(source);
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], "returned-unit", "{report}");
    assert_eq!(report["exit"], 0, "{report}");
}

fn source(tail: &str, flag: bool) -> String {
    format!(
        "fn example(flag:bool){{let value:Result<int,str>=Ok(1);let outer:Result<Result<int,str>,str>=if flag{{Ok(value)}}else{{Err(\"closed\")}};{tail}}}\npub fn test_native(){{example({flag})}}"
    )
}

#[test]
fn channel_receives_check_the_nested_producer_actually_carried_by_each_endpoint() {
    let source = include_str!("../../ril-compiler/tests/fixtures/nested_result_channel.ril")
        .replace("fn example()", "pub fn test_native()");
    executes(&source);
}

#[test]
fn a_successful_nested_test_can_be_used_through_its_boolean_value() {
    executes(&source(
        "let tested=outer is Ok(Ok(1));assert(tested)",
        true,
    ));
}

#[test]
fn nested_expected_expressions_execute_once() {
    executes(
        r#"
fn example(flag:bool){
    var calls=0
    let value:Result<int,str>=Ok(1)
    let outer:Result<Result<int,str>,str>=if flag{Ok(value)}else{Err("closed")}
    assert(outer is Ok(Ok({calls+=1;1})))
    assert(calls==1)
}
pub fn test_native(){example(true)}
"#,
    );
}

#[test]
fn an_unconsumed_or_wrapped_boolean_does_not_check_the_unreached_inner_result() {
    for tail in [
        "let tested=outer is Ok(Ok(1))",
        "let tested=outer is Ok(Ok(1));let wrapped=Some(tested);assert(wrapped is Some(_))",
    ] {
        let report = run(&source(tail, false));
        assert_eq!(report["status"], "rejected", "{report}");
        assert!(
            report["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|diagnostic| diagnostic["code"] == "E0720"),
            "{report}"
        );
    }
}
