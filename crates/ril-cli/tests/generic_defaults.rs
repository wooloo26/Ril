use std::{fs, process::Command};

fn executes(source: &str) {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("defaults.ril");
    fs::write(&path, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(path)
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
    assert_eq!(report["runtime"], "returned-unit", "{report}");
}

#[test]
fn generic_defaults_keep_parameter_order_and_explicit_argument_order() {
    executes(include_str!(
        "fixtures/generic_defaults/scalars_and_order.ril"
    ));
}

#[test]
fn default_handlers_use_the_callee_substitution_and_actual_parameters() {
    executes(include_str!("fixtures/generic_defaults/local_handler.ril"));
}

#[test]
fn default_budgets_keep_their_actual_handler_and_callee_proofs() {
    executes(include_str!("fixtures/generic_defaults/local_budget.ril"));
}

#[test]
fn default_created_recipes_survive_creation_and_keep_distinct_captures() {
    executes(include_str!(
        "fixtures/generic_defaults/retained_closure.ril"
    ));
}

#[test]
fn supplied_only_instances_do_not_materialize_an_unexecuted_default_closure() {
    executes(include_str!("fixtures/generic_defaults/supplied_only.ril"));
}

#[test]
fn defaults_can_call_a_closed_generic_helper_in_their_own_handler_context() {
    executes(include_str!("fixtures/generic_defaults/transitive.ril"));
}
