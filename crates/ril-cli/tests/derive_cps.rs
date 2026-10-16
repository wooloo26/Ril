//! Functional updates preserve their draft while native callbacks suspend.
use std::{fs, process::Command};

fn execution(source: &str) -> serde_json::Value {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("derive.ril");
    fs::write(&input, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(input)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap_or_else(|_| {
        panic!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    assert_eq!(report["status"], "executed", "{report}");
    report
}

fn executes(source: &str) {
    let report = execution(source);
    assert_eq!(report["runtime"], "returned-unit", "{report}");
}

#[test]
fn derived_process_command_spawns_waits_terminates_and_runs_scoped_child() {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("child.ril");
    let child = directory
        .path()
        .join(if cfg!(windows) { "child.exe" } else { "child" });
    fs::write(&input, "pub fn main(){}").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("build")
        .arg(input)
        .args(["--unit", "executable", "--output"])
        .arg(&child)
        .arg("--json")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let child = serde_json::to_string(&child.to_string_lossy()).unwrap();
    executes(&format!(
        r#"
use ril/process
use ril/path
use ril/os
pub fn test_native() @Fiber {{
    let command = Process::command(Path::from_string({child}), []) |> derive \mut draft -> {{
        draft.stdout = Process::OutputMode::Null
        draft.stderr = Process::OutputMode::Null
    }}
    let mut child = Process::spawn(command) ?? \_error -> panic("spawn")
    let first = Process::wait(mut child) ?? \_error -> panic("wait")
    let second = Process::wait(mut child) ?? \_error -> panic("wait again")
    assert(Process::success(first) && first == second)
    assert(Process::terminate(mut child) is Ok())
    let result = Process::with_child(command, \mut handle -> Process::wait(mut handle))
    assert(result is Ok(Process::ExitStatus::Exited(0u32)))
}}
"#
    ));
}

#[test]
fn cps_derive_keeps_aliases_and_original_input_across_recipe_effects_and_collection() {
    executes(
        r#"
eff Read { get() -> int }
type Cell = {mut value:int}
pub fn test_native() {
    let shared = Cell.{value:1}
    let base = .{left:shared, right:shared}
    let changed = base |> derive \mut draft -> {
        for 0..1200 as index { let unused=[index,index+1] }
        with Read::get()->resume 2
        draft.left.value += Read::get()
    }
    assert(changed.left.value == 3 && changed.right.value == 3)
    assert(base.left.value == 1 && shared.value == 1)
}
"#,
    );
}

#[test]
fn cps_derive_charges_the_recipe_entry_once_under_a_budget() {
    executes(
        r#"
fn updated()->int {
    let original = .{value:1}
    let changed = original |> derive \mut draft -> {draft.value=2}
    changed.value
}

fn measured(limit:int)->?int {with Div::exhausted()->None;Some(Div::budget(limit,updated))}
pub fn test_native(){
    assert(measured(0)==None && measured(1)==None && measured(2)==Some(2))
}
"#,
    );
}

#[test]
fn an_existing_effectful_recipe_selects_cps_for_the_transitive_derive_caller() {
    executes(
        r#"
eff Read { get() -> int }
type Cell = {mut value:int}
fn adjust(mut draft:Cell) @Read &mut {draft.value += Read::get()}
fn updated()->Cell @Read {let base=Cell.{value:1};base |> derive adjust}
pub fn test_native(){with Read::get()->resume 2;assert(updated().value==3)}
"#,
    );
}

#[test]
fn an_aborted_derive_recipe_preserves_inputs_and_committed_outside_writes() {
    executes(
        r#"
eff Stop { now() -> () }
type Cell = {mut value:int}
var trace = 0
fn change(mut draft:Cell) @Stop &mut {
    draft.value = 9
    Stop::now()
    panic("abandoned recipe continued")
}
pub fn test_native() &{mut trace} {
    let base = Cell.{value:1}
    let answer = {with Stop::now()->{trace=1;7};let changed=base |> derive change;trace=2;changed.value}
    assert(answer==7 && trace==1 && base.value==1)
}
"#,
    );
}
