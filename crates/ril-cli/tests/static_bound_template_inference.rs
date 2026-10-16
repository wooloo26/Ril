#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn symbolic_alias_map_and_callable_template_members_execute() {
    native_probe::executes(
        ril_test::case_source("tests/regressions/static.ril::static-bound-template-inference"),
        "symbolic alias, map and callable template members",
    );
}
