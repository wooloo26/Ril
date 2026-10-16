//! Fatal cleanup faults retain their first completed pair of causes.
use std::{fs, process::Command};

fn executes(outer_exit: &str) {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("cleanup_faults.ril");
    let source = r#"
use ril/concurrent::{scope, TaskFault, UnwindCause}
type Guard = { on_close: fn() -> () }
fn inner_cleanup() {
    let scoped remaining = Guard.{ on_close: \-> panic("inner remaining cleanup ran") }
    let scoped failing = Guard.{ on_close: \-> panic("inner cleanup") }
    panic("inner body")
}
pub fn test_native() @Concurrent {
    let result = scope \mut s -> {
        let child = s.fork(\-> {
            let scoped remaining = Guard.{ on_close: \-> panic("outer remaining cleanup ran") }
            let scoped failing = Guard.{ on_close: inner_cleanup }
            OUTER_EXIT
        })
        child.join()
    }
    match result {
        Err(TaskFault::DoubleFaultFatal(info)) -> {
            match info.primary {
                UnwindCause::Panicked(primary) -> {
                    if primary.message != "inner body" { panic(primary.message) }
                },
                _ -> panic("inner primary cause was replaced"),
            }
            if info.cleanup.message != "inner cleanup" { panic(info.cleanup.message) }
        },
        _ -> panic("inner double fault was not contained by its task scope"),
    }
}
"#
    .replace("OUTER_EXIT", outer_exit);
    fs::write(&input, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&input)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], "returned-unit", "{report}");
}

#[test]
fn nested_double_fault_on_normal_exit_abandons_remaining_cleanup() {
    executes("()");
}

#[test]
fn nested_double_fault_during_panic_preserves_the_inner_causes() {
    executes("panic(\"outer body\")");
}
