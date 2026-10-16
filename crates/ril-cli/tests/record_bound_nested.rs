#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn actual_tuple_field_forwarding_alias_and_fixed_structural_selections_execute() {
    for (label, source) in [
        (
            "tuple",
            ril_test::case_source("tests/regressions/record-bounds.ril::nested-tuple"),
        ),
        (
            "field",
            ril_test::case_source("tests/regressions/record-bounds.ril::nested-field"),
        ),
        (
            "mixed",
            ril_test::case_source("tests/regressions/record-bounds.ril::nested-mixed"),
        ),
        (
            "tuple forward",
            ril_test::case_source("tests/regressions/record-bounds.ril::nested-tuple-forward"),
        ),
        (
            "field forward",
            ril_test::case_source("tests/regressions/record-bounds.ril::nested-field-forward"),
        ),
        (
            "fixed",
            ril_test::case_source("tests/regressions/record-bounds.ril::nested-fixed"),
        ),
        (
            "alias",
            ril_test::case_source("tests/regressions/record-bounds.ril::nested-alias"),
        ),
        (
            "readonly",
            ril_test::case_source("tests/regressions/record-bounds.ril::nested-readonly"),
        ),
        (
            "shared row",
            ril_test::case_source("tests/regressions/record-bounds.ril::nested-shared-row"),
        ),
    ] {
        native_probe::executes(source, label);
    }
}
