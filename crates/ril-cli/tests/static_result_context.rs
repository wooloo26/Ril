#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn complete_result_contexts_and_transferred_results_execute() {
    for (source, name) in [
        (
            include_str!("../../ril-compiler/tests/fixtures/static_result_context/positive.ril"),
            "complete static result contexts",
        ),
        (
            include_str!(
                "../../ril-compiler/tests/fixtures/static_result_context/result_transfer.ril"
            ),
            "contextual Result producer transfer",
        ),
        (
            include_str!(
                "../../ril-compiler/tests/fixtures/static_result_context/computed_alias.ril"
            ),
            "frozen computed alias result context",
        ),
    ] {
        native_probe::executes(source, name);
    }
}
