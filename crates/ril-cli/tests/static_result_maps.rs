#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn exact_static_map_lookups_execute_with_original_result_members() {
    native_probe::executes(
        ril_test::case_source("tests/regressions/static.ril::static-result-map-lookup"),
        "static exact map lookup preserves each original Result",
    );
}
