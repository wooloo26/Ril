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
    executes(ril_test::case_source(
        "tests/regressions/defaults.ril::scalars-and-order",
    ));
}

#[test]
fn default_handlers_use_the_callee_substitution_and_actual_parameters() {
    executes(ril_test::case_source(
        "tests/regressions/defaults.ril::local-handler",
    ));
}

#[test]
fn default_budgets_keep_their_actual_handler_and_callee_proofs() {
    executes(ril_test::case_source(
        "tests/regressions/defaults.ril::local-budget",
    ));
}

#[test]
fn default_created_recipes_survive_creation_and_keep_distinct_captures() {
    executes(ril_test::case_source(
        "tests/regressions/defaults.ril::retained-closure",
    ));
}

#[test]
fn supplied_only_instances_do_not_materialize_an_unexecuted_default_closure() {
    executes(ril_test::case_source(
        "tests/regressions/defaults.ril::supplied-only",
    ));
}

#[test]
fn defaults_can_call_a_closed_generic_helper_in_their_own_handler_context() {
    executes(ril_test::case_source(
        "tests/regressions/defaults.ril::transitive",
    ));
}
