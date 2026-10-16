#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn actual_nested_rigid_tuple_field_and_shared_residual_forwarding_execute() {
    for (name, source) in [
        (
            "rigid tuple",
            include_str!("../../ril-compiler/tests/fixtures/record_bounds/nested_rigid_tuple.ril"),
        ),
        (
            "rigid field",
            include_str!("../../ril-compiler/tests/fixtures/record_bounds/nested_rigid_field.ril"),
        ),
        (
            "rigid shared row",
            include_str!(
                "../../ril-compiler/tests/fixtures/record_bounds/nested_rigid_shared_row.ril"
            ),
        ),
    ] {
        native_probe::executes(source, name);
    }
}
