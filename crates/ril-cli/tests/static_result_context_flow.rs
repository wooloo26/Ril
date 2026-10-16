#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn contextual_static_results_keep_the_producer_through_nested_receiving() {
    native_probe::executes(
        ril_test::case_source("tests/regressions/static.ril::static-result-context-flow"),
        "static result contexts preserve the original producer across calls and Optional fallback",
    );
    native_probe::executes(
        ril_test::case_source("tests/regressions/static.ril::static-result-context-containers"),
        "static result contexts preserve the producer through array, record, map and match",
    );
    native_probe::executes(
        ril_test::case_source("tests/regressions/static.ril::static-result-context-shadow"),
        "static result contexts retain the nearest lexical dimension",
    );
}
