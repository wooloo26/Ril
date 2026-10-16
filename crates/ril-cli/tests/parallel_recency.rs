use std::{fs, process::Command};

const PREFIX: &str = "use ril/parallel\ntype Cell={mut value:int,mut other:int}\nfn cell()->Cell{Cell.{value:0,other:0}}\nfn separate()->Cell{Cell.{value:0,other:0}}\n";

fn run(source: &str, operation: &str) -> (bool, serde_json::Value) {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("parallel_recency.ril");
    fs::write(&input, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_ril"));
    command.arg(operation).arg(&input).arg("--json");
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
fn native_disjoint_writes_survive_unrelated_allocation_history() {
    for body in [
        "let mut left=cell();let mut right=separate();let _=Parallel::join(\\->{left.value+=1},\\->{let unused=cell();right.value+=1});assert(left.value==1&&right.value==1)",
        "let mut left=cell();let mut right=separate();let _=Parallel::join(\\->{left.value+=1;let unused=cell()},\\->{right.value+=1});assert(left.value==1&&right.value==1)",
        "let mut shared=cell();let _=Parallel::join(\\->{shared.value+=1},\\->{let unused=cell();shared.other+=1});assert(shared.value==1&&shared.other==1)",
        "let mut shared=cell();let _=Parallel::join(\\->{shared.value+=1;let unused=cell()},\\->{shared.other+=1});assert(shared.value==1&&shared.other==1)",
        "let values=Parallel::map([1,2],\\n->{let mut local=cell();local.value+=1;let unused=cell();n});assert(values==[1,2])",
    ] {
        let source = format!("{PREFIX}pub fn test_native(){{for [0,1] as index{{{body}}}}}");
        let (success, report) = run(&source, "test");
        assert!(success, "{body}: {report}");
        assert_eq!(report["runtime"], "returned-unit", "{report}");
        assert_eq!(report["exit"], 0, "{report}");
    }
}

#[test]
fn compiler_rejects_racing_callbacks_even_when_unrelated_allocations_intervene() {
    for (left, right) in [
        ("shared.value+=1", "let unused=cell();shared.value+=1"),
        ("shared.value+=1;let unused=cell()", "shared.value+=1"),
    ] {
        let source = format!(
            "{PREFIX}pub fn test_native(){{for [0,1] as index{{let mut shared=cell();let _=Parallel::join(\\->{{{left}}},\\->{{{right}}})}}}}"
        );
        // These programs are checked only; a rejected data race is never run.
        let (success, report) = run(&source, "check");
        assert!(!success, "{report}");
        assert_eq!(report["status"], "rejected", "{report}");
        assert!(
            report["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|diagnostic| diagnostic["code"] == "E0619"),
            "{report}"
        );
    }
}
