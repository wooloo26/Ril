#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn generic_mutable_scalar_stores_are_visible_through_the_actual_caller_object() {
    native_probe::executes(
        ril_test::case_source("tests/regressions/record-bounds.ril::write-scalar"),
        "bounded scalar writes preserve caller object and unrelated field",
    );
}
