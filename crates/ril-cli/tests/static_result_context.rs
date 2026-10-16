#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn complete_result_contexts_and_transferred_results_execute() {
    for (source, name) in [
        (
            ril_test::case_source("tests/regressions/static.ril::positive"),
            "complete static result contexts",
        ),
        (
            ril_test::case_source("tests/regressions/static.ril::result-transfer"),
            "contextual Result producer transfer",
        ),
        (
            ril_test::case_source("tests/regressions/static.ril::computed-alias"),
            "frozen computed alias result context",
        ),
    ] {
        native_probe::executes(source, name);
    }
}
