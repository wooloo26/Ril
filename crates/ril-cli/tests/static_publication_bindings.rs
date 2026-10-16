//! Native observations of lexically distinct sealed static publications.
use std::{fs, process::Command};

fn run(command: &str, source: &str) -> serde_json::Value {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("publication.ril");
    fs::write(&input, source).unwrap();
    let mut compiler = Command::new(env!("CARGO_BIN_EXE_ril"));
    compiler.arg(command).arg(input).arg("--json");
    if command == "test" {
        compiler.args(["--entry", "test_native"]);
    }
    let output = compiler.output().unwrap();
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap_or_else(|_| {
        panic!(
            "{source}\nexit={:?}\n{}\n{}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    if command == "test" {
        assert!(output.status.success(), "{source}\n{report}");
        assert_eq!(report["status"], "executed", "{report}");
        assert_eq!(report["runtime"], "returned-unit", "{report}");
        assert_eq!(report["exit"], 0, "{report}");
    }
    report
}

#[test]
fn original_reference_shadowing_source_checks_and_executes_unchanged() {
    let source = ril_test::case_source("tests/regressions/static.ril::static-reference-shadowing");
    assert_eq!(run("check", source)["status"], "accepted");
    run("test", source);
}

#[test]
fn hidden_local_alias_and_restored_outer_binding_keep_object_identity() {
    run(
        "test",
        r#"
pub fn test_native(){
    meta let VALUES=[1]
    meta let KEEP=\->VALUES
    {
        meta let VALUES=[2]
        meta let RECOVERED=KEEP()
        let mut copied=^mut clone((RECOVERED,RECOVERED,VALUES))
        copied.0[0]=9
        assert(copied.1[0]==9 && copied.2[0]==2 && RECOVERED[0]==1)
    }
    meta let RESTORED=VALUES
    let mut copied=^mut clone((VALUES,RESTORED))
    copied.0[0]=7
    assert(copied.1[0]==7 && VALUES[0]==1)
}
"#,
    );
}

#[test]
fn equal_local_allocations_and_repeated_calls_observe_their_actual_pool_nodes() {
    run(
        "test",
        r#"
fn selected()->[]int{meta let VALUES=[1];VALUES}
pub fn test_native(){
    meta let FIRST=[1]
    meta let SECOND=[1]
    let mut distinct=^mut clone((FIRST,SECOND))
    distinct.0[0]=9
    assert(distinct.1[0]==1 && FIRST[0]==1)
    let mut shared=^mut clone((selected(),selected()))
    shared.0[0]=7
    assert(shared.1[0]==7 && selected()[0]==1)
}
"#,
    );
}

#[test]
fn branch_and_iteration_publications_do_not_replace_the_outer_typed_array() {
    run(
        "test",
        r#"
pub fn test_native(){
    meta let VALUES:[2]u8=[254,255]
    if true{meta let VALUES=[2];assert(VALUES[0]==2)}else{meta let VALUES=[3];assert(VALUES[0]==3)}
    for [1] as value{meta let VALUES=[4];assert(VALUES[0]==4 && value==1)}
    while false{meta let VALUES=[5];assert(VALUES[0]==5)}
    match true{true->{meta let VALUES=[6];assert(VALUES[0]==6)},false->{}}
    meta let RESTORED=VALUES
    let mut copied=^mut clone((VALUES,RESTORED))
    copied.0[0]=253u8
    assert(copied.1[0]==253u8 && VALUES[0]==254u8 && VALUES[1]==255u8)
}
"#,
    );
}

#[test]
fn unchecked_results_and_readonly_local_constants_are_check_only_negatives() {
    for (source, codes) in [
        (
            "fn bad(){meta let VALUES=[1];VALUES[0]=2}",
            &["E0520", "E0522", "E0528"][..],
        ),
        (
            "meta let VALUES={let result:Result<int,str>=Ok(1);[1]}",
            &["E0720"][..],
        ),
    ] {
        let report = run("check", source);
        assert_eq!(report["status"], "rejected", "{report}");
        assert!(
            report["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|diagnostic| codes.contains(&diagnostic["code"].as_str().unwrap())),
            "{report}"
        );
    }
    let report = run(
        "check",
        "fn bad(){meta let VALUES={let result:Result<int,str>=Ok(1);[result]}}",
    );
    assert_eq!(report["status"], "not-implemented", "{report}");
    assert!(
        report["reason"]["detail"]
            .as_str()
            .unwrap()
            .contains("local meta Result publication"),
        "{report}"
    );
    let report = run(
        "check",
        "meta let VALUES={let result:Result<int,str>=Ok(1);[result]}",
    );
    assert_eq!(report["status"], "not-implemented", "{report}");
    assert!(
        report["reason"]["detail"]
            .as_str()
            .unwrap()
            .contains("pending static Result publication"),
        "{report}"
    );
}
