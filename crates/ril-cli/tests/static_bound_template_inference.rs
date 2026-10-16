#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn symbolic_alias_map_and_callable_template_members_execute() {
    native_probe::executes(
        include_str!("../../ril-compiler/tests/fixtures/static_bound_template_inference.ril"),
        "symbolic alias, map and callable template members",
    );
}
