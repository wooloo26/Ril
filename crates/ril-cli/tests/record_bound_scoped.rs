#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn fixed_empty_inner_callable_mode_and_immutable_scoped_sources_execute() {
    for (name, source) in [
        (
            "scoped fixed",
            ril_test::case_source("tests/regressions/record-bounds.ril::nested-rigid-fixed"),
        ),
        (
            "scoped empty inner dimension",
            ril_test::case_source(
                "tests/regressions/record-bounds.ril::scoped-empty-inner-dimension",
            ),
        ),
        (
            "scoped callable mode",
            ril_test::case_source("tests/regressions/record-bounds.ril::scoped-callable-mut"),
        ),
        (
            "scoped immutable field",
            ril_test::case_source("tests/regressions/record-bounds.ril::scoped-immutable-field"),
        ),
    ] {
        native_probe::executes(source, name);
    }
}
