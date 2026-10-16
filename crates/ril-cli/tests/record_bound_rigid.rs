#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn actual_nested_rigid_tuple_field_and_shared_residual_forwarding_execute() {
    for (name, source) in [
        (
            "rigid tuple",
            ril_test::case_source("tests/regressions/record-bounds.ril::nested-rigid-tuple"),
        ),
        (
            "rigid field",
            ril_test::case_source("tests/regressions/record-bounds.ril::nested-rigid-field"),
        ),
        (
            "rigid shared row",
            ril_test::case_source("tests/regressions/record-bounds.ril::nested-rigid-shared-row"),
        ),
    ] {
        native_probe::executes(source, name);
    }
}
