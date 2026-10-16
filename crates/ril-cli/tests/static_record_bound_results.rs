#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn static_bounds_and_transported_callable_interfaces_execute() {
    for (label, source) in [
        (
            "static bound numeric construction with callable default",
            ril_test::case_source(
                "tests/regressions/static.ril::static-bound-callable-construction",
            ),
        ),
        (
            "static bound projection",
            ril_test::case_source("tests/regressions/static.ril::static-bound-projection"),
        ),
        (
            "static bound Result inspection",
            ril_test::case_source("tests/regressions/static.ril::static-bound-result-inspection"),
        ),
        (
            "static generic callable",
            ril_test::case_source(
                "tests/regressions/static.ril::static-generic-callable-receiving",
            ),
        ),
        (
            "static generic wrapper",
            ril_test::case_source("tests/regressions/static.ril::static-generic-callable-wrapper"),
        ),
    ] {
        native_probe::executes(source, label);
    }
}
