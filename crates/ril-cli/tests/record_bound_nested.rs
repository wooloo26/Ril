#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn actual_tuple_field_forwarding_alias_and_fixed_structural_selections_execute() {
    for (label, source) in [
        (
            "tuple",
            include_str!("../../ril-compiler/tests/fixtures/record_bounds/nested_tuple.ril"),
        ),
        (
            "field",
            include_str!("../../ril-compiler/tests/fixtures/record_bounds/nested_field.ril"),
        ),
        (
            "mixed",
            include_str!("../../ril-compiler/tests/fixtures/record_bounds/nested_mixed.ril"),
        ),
        (
            "tuple forward",
            include_str!(
                "../../ril-compiler/tests/fixtures/record_bounds/nested_tuple_forward.ril"
            ),
        ),
        (
            "field forward",
            include_str!(
                "../../ril-compiler/tests/fixtures/record_bounds/nested_field_forward.ril"
            ),
        ),
        (
            "fixed",
            include_str!("../../ril-compiler/tests/fixtures/record_bounds/nested_fixed.ril"),
        ),
        (
            "alias",
            include_str!("../../ril-compiler/tests/fixtures/record_bounds/nested_alias.ril"),
        ),
        (
            "readonly",
            include_str!("../../ril-compiler/tests/fixtures/record_bounds/nested_readonly.ril"),
        ),
        (
            "shared row",
            include_str!("../../ril-compiler/tests/fixtures/record_bounds/nested_shared_row.ril"),
        ),
    ] {
        native_probe::executes(source, label);
    }
}
