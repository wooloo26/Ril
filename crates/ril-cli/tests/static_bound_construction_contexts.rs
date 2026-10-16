#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn fresh_structural_numeric_and_slot_contexts_execute() {
    native_probe::executes(
        include_str!("../../ril-compiler/tests/fixtures/static_bound_fresh_construction.ril"),
        "fresh structural constructors",
    );
}
