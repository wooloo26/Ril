use std::{fs, process::Command};

const PREFIX: &str = "type Cell={mut value:int}\ntype Reader=fn(mut Cell,int)->int &mut &closure\nfn make(source:Cell)->Reader &capture{\\mut target:Cell,padding:int->{let observed=source.value;target.value+=1;observed+padding}}\n";

fn run(source: &str, operation: &str) -> (bool, serde_json::Value) {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("closure-exclusivity.ril");
    fs::write(&path, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_ril"));
    command.arg(operation).arg(&path).arg("--json");
    if operation == "test" {
        command.args(["--entry", "test_native"]);
    }
    let output = command.output().unwrap();
    let report = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "{error}\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    (output.status.success(), report)
}

#[test]
fn disjoint_closure_arguments_execute_for_each_real_factory_object() {
    let source = format!(
        "{PREFIX}pub fn test_native(){{let mut source=Cell.{{value:10}};source.value+=0;let mut other=Cell.{{value:0}};make(source);let view first=make(source);let view second=make(source);assert(first(mut other,1)==11);assert(second(mut other,2)==12);assert(first(mut other,3)==13);assert(other.value==3);assert(source.value==10)}}"
    );
    let (success, report) = run(&source, "test");
    assert!(success, "{report}");
    assert_eq!(report["runtime"], "returned-unit", "{report}");
    assert_eq!(report["exit"], 0, "{report}");
}

#[test]
fn captured_source_conflicts_are_checked_without_running_the_program() {
    for body in [
        "let view action=make(source);let result=action(mut source,1)",
        "let view first=make(source);let view second=make(source);let a=first(mut other,1);let b=second(mut source,2)",
        "let view action=make(source);let first=action(mut other,1);let second=action(mut source,2)",
    ] {
        let source = format!(
            "{PREFIX}pub fn test_native(){{let mut source=Cell.{{value:10}};source.value+=0;let mut other=Cell.{{value:0}};other.value+=0;{body}}}"
        );
        let (success, report) = run(&source, "check");
        assert!(!success, "{report}");
        assert_eq!(report["status"], "rejected", "{report}");
        assert!(
            report["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|diagnostic| diagnostic["code"] == "E0524"),
            "{report}"
        );
    }
}
