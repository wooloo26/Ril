#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn contextual_static_results_keep_the_producer_through_nested_receiving() {
    native_probe::executes(
        include_str!("../../ril-compiler/tests/fixtures/static_result_context_flow.ril"),
        "static result contexts preserve the original producer across calls and Optional fallback",
    );
    native_probe::executes(
        include_str!("../../ril-compiler/tests/fixtures/static_result_context_containers.ril"),
        "static result contexts preserve the producer through array, record, map and match",
    );
    native_probe::executes(
        include_str!("../../ril-compiler/tests/fixtures/static_result_context_shadow.ril"),
        "static result contexts retain the nearest lexical dimension",
    );
}
