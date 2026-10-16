#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn const_roles_and_transferred_results_survive_lexical_shadows() {
    native_probe::executes(
        include_str!("../../ril-compiler/tests/fixtures/static_const_result_flow.ril"),
        "static const roles and Result flow",
    );
}
