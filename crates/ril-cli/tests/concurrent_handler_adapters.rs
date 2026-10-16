//! Bound system methods keep their receiver without retaining unrelated handlers.
use std::{fs, process::Command};

fn report(source: &str, operation: &str) -> serde_json::Value {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("adapters.ril");
    fs::write(&input, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_ril"));
    command.arg(operation).arg(input).arg("--json");
    if operation == "test" {
        command.args(["--entry", "test_native"]);
    }
    let result = command.output().unwrap();
    serde_json::from_slice(&result.stdout).unwrap_or_else(|_| {
        panic!(
            "{}\n{}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        )
    })
}

#[test]
fn fork_and_join_adapters_created_under_an_unrelated_handler_keep_their_receivers() {
    let outcome = report(
        r#"
use ril/concurrent::{scope, TaskFault}
eff Read { get() -> int }
pub fn test_native() @Concurrent {
    let result = scope \mut s -> {
        with Read::get() -> resume 7
        let fork = s.fork
        let child = fork(\->42)
        let join = child.join
        let value = join()?
        assert(Read::get() == 7)
        Ok(value)
    }
    assert(result is Ok(42))
}
"#,
        "test",
    );
    assert_eq!(outcome["status"], "executed", "{outcome}");
    assert_eq!(outcome["runtime"], "returned-unit", "{outcome}");
}

#[test]
fn empty_adapter_selection_does_not_authorize_a_child_to_inherit_user_handlers() {
    let outcome = report(
        r#"
use ril/concurrent::{scope, TaskFault}
eff Read { get() -> int }
pub fn test_native() @Concurrent {
    let result = scope \mut s -> {
        with Read::get() -> resume 7
        let fork = s.fork
        let child = fork(\->Read::get())
        child.join()
    }
    assert(result is Ok(7))
}
"#,
        "check",
    );
    assert_eq!(outcome["status"], "rejected", "{outcome}");
    assert!(
        outcome["diagnostics"]
            .as_array()
            .unwrap()
            .iter()
            .any(|diagnostic| diagnostic["code"] == "E0615"),
        "{outcome}"
    );
}
