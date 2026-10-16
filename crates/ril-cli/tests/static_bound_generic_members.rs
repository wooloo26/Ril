#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn bounded_member_type_dependencies_and_callable_interfaces_execute() {
    native_probe::executes(
        include_str!("../../ril-compiler/tests/fixtures/static_bound_generic_members.ril"),
        "bounded member type dependencies",
    );
}
