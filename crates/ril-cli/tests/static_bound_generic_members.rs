#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn bounded_member_type_dependencies_and_callable_interfaces_execute() {
    native_probe::executes(
        ril_test::case_source("tests/regressions/static.ril::static-bound-generic-members"),
        "bounded member type dependencies",
    );
}
