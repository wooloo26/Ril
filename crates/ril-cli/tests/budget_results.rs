use std::{fs, process::Command};

fn run(source: &str) -> serde_json::Value {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("budget_results.ril");
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
}

#[test]
fn normal_and_recovery_result_producers_are_checked_after_return() {
    executes(
        r#"
fn produce(limit:int)->Result<int,str>{
    with Div::exhausted()->Err("fuel")
    Div::budget(limit,\->Ok(7))
}
pub fn test_native(){
    assert(produce(0) is Err("fuel"))
    assert(produce(1) is Ok(7))
    assert(produce(100) is Ok(7))
}
"#,
    );
}

#[test]
fn nested_result_carriers_keep_each_exit_producer_and_each_index() {
    executes(
        r#"
fn produce(limit:int)->{values:[]Result<int,str>}{
    with Div::exhausted()->.{values:[Err("fuel"),Err("fuel")]}
    Div::budget(limit,\->.{values:[Ok(7),Ok(9)]})
}
pub fn test_native(){
    let exhausted=produce(0)
    assert(exhausted.values[0] is Err("fuel"))
    assert(exhausted.values[1] is Err("fuel"))
    let exact=produce(1)
    assert(exact.values[0] is Ok(7))
    assert(exact.values[1] is Ok(9))
    let plenty=produce(100)
    assert(plenty.values[0] is Ok(7))
    assert(plenty.values[1] is Ok(9))
}
"#,
    );
}

#[test]
fn an_existing_result_can_return_unchanged_through_either_budget_exit() {
    executes(
        r#"
fn relay(limit:int,value:Result<int,str>)->Result<int,str>{
    with Div::exhausted()->value
    Div::budget(limit,\->value)
}
pub fn test_native(){
    let first:Result<int,str>=Ok(7)
    assert(relay(0,first) is Ok(7))
    let second:Result<int,str>=Err("original")
    assert(relay(1,second) is Err("original"))
    let third:Result<int,str>=Ok(9)
    assert(relay(100,third) is Ok(9))
}
"#,
    );
}

#[test]
fn exhaustion_cannot_borrow_an_inspection_from_the_unexecuted_action_suffix() {
    let report = run(r#"
fn dummy(){}
pub fn test_native(){(\->{
    let result:Result<int,str>=Err("uninspected")
    {with Div::exhausted()->();Div::budget(1,\->{dummy();assert(result is Err(_));assert(false)})}
})()}
"#);
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
