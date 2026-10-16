#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn static_bounds_and_transported_callable_interfaces_execute() {
    for (label, source) in [
        (
            "static bound numeric construction with callable default",
            include_str!(
                "../../ril-compiler/tests/fixtures/static_bound_callable_construction.ril"
            ),
        ),
        (
            "static bound projection",
            include_str!("../../ril-compiler/tests/fixtures/static_bound_projection.ril"),
        ),
        (
            "static bound Result inspection",
            include_str!("../../ril-compiler/tests/fixtures/static_bound_result_inspection.ril"),
        ),
        (
            "static generic callable",
            include_str!("../../ril-compiler/tests/fixtures/static_generic_callable_receiving.ril"),
        ),
        (
            "static generic wrapper",
            include_str!("../../ril-compiler/tests/fixtures/static_generic_callable_wrapper.ril"),
        ),
    ] {
        native_probe::executes(source, label);
    }
}
