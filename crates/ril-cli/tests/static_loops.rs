//! Real CLI quotas and native publication from immutable static loops.
use std::{
    fs,
    process::{Command, ExitStatus},
};

fn run(command: &str, source: &str, budget: u64) -> (ExitStatus, serde_json::Value) {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("static-loops.ril");
    fs::write(&path, source).unwrap();
    let mut compiler = Command::new(env!("CARGO_BIN_EXE_ril"));
    compiler
        .arg(command)
        .arg(&path)
        .args(["--json", "--static-budget", &budget.to_string()]);
    if command == "test" {
        compiler.args(["--entry", "test_native"]);
    }
    let output = compiler.output().unwrap();
    let report = serde_json::from_slice(&output.stdout).unwrap_or_else(|_| {
        panic!(
            "{source}\nexit={:?}\n{}\n{}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    (output.status, report)
}
fn accepted(source: &str, budget: u64) {
    let (status, report) = run("check", source, budget);
    assert!(status.success(), "{source}\n{report}");
    assert_eq!(report["status"], "accepted", "{report}");
}
fn rejected(source: &str, budget: u64, code: &str) {
    let (status, report) = run("check", source, budget);
    assert!(!status.success(), "{source} was accepted");
    assert_eq!(report["status"], "rejected", "{report}");
    assert!(
        report["diagnostics"]
            .as_array()
            .unwrap()
            .iter()
            .any(|item| item["code"] == code),
        "{report}"
    );
}
fn native(source: &str, budget: u64) {
    let (status, report) = run("test", source, budget);
    assert!(status.success(), "{source}\n{report}");
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], "returned-unit", "{report}");
    assert_eq!(report["exit"], 0, "{report}");
}

#[test]
fn four_original_ni_sources_check_and_publish_native_values() {
    for source in [
        include_str!("fixtures/static_loop_last.ril"),
        include_str!("fixtures/static_for_return.ril"),
        include_str!("fixtures/static_while_false.ril"),
    ] {
        accepted(source, 100_000);
        native(
            &format!("{source}\npub fn test_native() &{{VALUE}}{{assert(VALUE==7)}}"),
            100_000,
        );
    }
    let source = include_str!("fixtures/static_type_loop.ril");
    accepted(source, 100_000);
    native(
        &format!("{source}\npub fn test_native(){{assert(identity(7)==7)}}"),
        100_000,
    );
}

#[test]
fn cli_event_quota_permits_the_last_event_and_charges_terminal_tests() {
    for (source, quota) in [
        ("meta fn one()->int{loop{last 7}}\nmeta let VALUE=one()", 2),
        (
            "meta fn walk(){for [1,2] as value{next}}\nmeta let _=walk()",
            4,
        ),
        ("meta fn walk(){while false{next}}\nmeta let _=walk()", 2),
        (
            "meta fn walk(){for [] as value{next}}\nmeta let _=walk()",
            2,
        ),
        (
            "meta fn walk(){for [1,2] as value{last}}\nmeta let _=walk()",
            2,
        ),
    ] {
        rejected(source, quota - 1, "E0811");
        accepted(source, quota);
    }
    native(
        "meta fn one()->int{loop{last 7}}\nmeta let VALUE=one()\npub fn test_native() &{VALUE}{assert(VALUE==7)}",
        2,
    );
}

#[test]
fn fresh_iteration_declaration_groups_keep_their_own_captures() {
    native(
        r#"
meta fn make(values:[]int)->fn()->int{
    for values as value{return get where meta fn get()->int{value}}
    \->0
}
meta let FIRST=make([7])
meta let SECOND=make([9])
meta let FIRST_VALUE=FIRST()
meta let SECOND_VALUE=SECOND()
pub fn test_native() &{FIRST_VALUE,SECOND_VALUE}{assert(FIRST_VALUE==7 && SECOND_VALUE==9)}
"#,
        100_000,
    );
}

#[test]
fn maximum_inclusive_typed_range_finishes_without_an_overflow_step() {
    let source = "meta fn byte()->u8{for 254u8..=255u8 as value{assert(value>=254u8)};255}\nmeta let VALUE=byte()";
    rejected(source, 3, "E0811");
    accepted(source, 4);
    native(
        &format!("{source}\npub fn test_native() &{{VALUE}}{{assert(VALUE==255u8)}}"),
        4,
    );
}

#[test]
fn last_keeps_constant_graph_sharing_and_native_copy_isolation() {
    native(
        r#"
meta fn graph()->([2]int,[2]int){let shared:[2]int=[1,2];loop{last(shared,shared)}}
meta let GRAPH=graph()
pub fn test_native() &{GRAPH}{
    let mut copied=^mut clone(GRAPH)
    copied.0[0]=9
    assert(copied.1[0]==9 && GRAPH.0[0]==1)
}
"#,
        100_000,
    );
}

#[test]
fn helper_control_and_unchecked_results_are_rejected_without_execution() {
    for source in [
        "meta fn helper(){next}\nmeta fn outer(){loop{helper();last}}\nmeta let _=outer()",
        "meta fn outer()->int{loop{(\\->last 7)();last 9}}\nmeta let VALUE=outer()",
        "type Bad=\\T->{last type<T>}\ntype Outer=\\T->{loop{last Bad<T>}}\ntype Selected=Outer<int>",
    ] {
        rejected(source, 100, "E0707");
    }
    rejected(
        "meta fn bad(){loop{let result:Result<int,str>=Ok(1);last}}\nmeta let _=bad()",
        100,
        "E0720",
    );
    rejected("meta fn spin(){loop{next}}\nmeta let _=spin()", 10, "E0811");
}
