//! Symbolic constructor payloads keep their declaration views and shape bounds.
use ril_compiler::{CheckOptions, Session, hir::VerifiedProgram};

fn fixture(case: &str, target: &str) -> VerifiedProgram {
    let source = ril_test::case_bytes(case);
    let snapshot = Session::with_options(
        source.to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .analyze();
    let diagnostics = format!("{:?}; {:?}", snapshot.diagnostics(), snapshot.unresolved());
    snapshot
        .into_verified()
        .unwrap_or_else(|error| panic!("{target} {case}: {error:?}; {diagnostics}"))
}

#[test]
fn symbolic_constructor_payload_shapes_reach_core_on_both_layouts() {
    for target in ["pointer32", "pointer64"] {
        let program = fixture(
            "tests/regressions/formal-shapes.ril::optional-array-shapes-pointer64",
            target,
        );
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}
