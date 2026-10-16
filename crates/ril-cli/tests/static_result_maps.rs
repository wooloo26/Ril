#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn exact_static_map_lookups_execute_with_original_result_members() {
    native_probe::executes(
        include_str!("../../ril-compiler/tests/fixtures/static_result_map_lookup.ril"),
        "static exact map lookup preserves each original Result",
    );
}
