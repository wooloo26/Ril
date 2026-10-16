#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn const_roles_and_transferred_results_survive_lexical_shadows() {
    native_probe::executes(
        ril_test::case_source("tests/regressions/static.ril::static-const-result-flow"),
        "static const roles and Result flow",
    );
}
