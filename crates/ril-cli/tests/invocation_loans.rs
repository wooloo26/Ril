use std::{fs, process::Command};

const PREFIX: &str = "type Cell={mut value:int}\ntype Action=fn()->() &mut &closure\nfn make(^mut cell:Cell)->Action &^mut &capture{\\->{cell.value+=1}}\n";
fn report(source: &str, execute: bool) -> serde_json::Value {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("invocation_loans.ril");
    fs::write(&input, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_ril"));
    command
        .arg(if execute { "test" } else { "check" })
        .arg(&input)
        .arg("--json");
    if execute {
        command.args(["--entry", "test_native"]);
    }
    let output = command.output().unwrap();
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "{error}\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}
#[test]
fn escaped_shared_closures_and_the_original_root_mutate_sequentially() {
    let source = format!(
        "{PREFIX}pub fn test_native(){{let mut cell=Cell.{{value:0}};let mut first=make(^mut cell);let mut second=make(^mut cell);first();second();cell.value+=10;first();assert(cell.value==13);let mut alias=^mut second;alias();assert(cell.value==14)}}"
    );
    let report = report(&source, true);
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], "returned-unit", "{report}");
    assert_eq!(report["exit"], 0, "{report}");
}
#[test]
fn a_still_active_mutable_argument_cannot_alias_a_retained_capture() {
    let source = format!(
        "{PREFIX}fn tick(mut cell:Cell)&mut{{cell.value+=1}}\nfn apply(mut target:Cell,mut action:Action)&mut{{tick(mut target);action()}}\npub fn test_native(){{let mut cell=Cell.{{value:0}};let mut action=make(^mut cell);apply(mut cell,mut action)}}"
    );
    // Invalid overlapping access is compiled only, never executed.
    let report = report(&source, false);
    assert_eq!(report["status"], "rejected", "{report}");
    assert!(
        report["diagnostics"]
            .as_array()
            .unwrap()
            .iter()
            .any(|diagnostic| diagnostic["code"] == "E0523"),
        "{report}"
    );
}
