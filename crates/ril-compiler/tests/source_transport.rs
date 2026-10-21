//! Original schemas survive explicit selection, views and generic forwarding.
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn accepts(name: &str) {
    let source = ril_test::case_source(&format!("tests/regressions/source-transport.ril::{name}"));
    for layout in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: layout.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|outcome| panic!("{name}, {layout}: {outcome:?}"));
        ril_compiler::lower::lower_core(&program)
            .unwrap_or_else(|error| panic!("{name}, {layout}: {error:?}"));
    }
}

fn rejects(name: &str, code: &str) {
    let source = ril_test::case_source(&format!("tests/regressions/source-transport.ril::{name}"));
    for layout in ["pointer32", "pointer64"] {
        let outcome = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: layout.into(),
                ..Default::default()
            },
        )
        .check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
            "{name}, {layout}: {outcome:?}"
        );
    }
}

#[test]
fn explicit_empty_inner_dimension() {
    rejects("explicit-empty-inner-dimension", "E0301");
}

#[test]
fn explicit_record_field_dimension() {
    rejects("explicit-record-field-dimension", "E0301");
}

#[test]
fn fresh_record_construction() {
    accepts("fresh-record-construction");
}

#[test]
fn fresh_tuple_construction() {
    accepts("fresh-tuple-construction");
}

#[test]
fn partial_static_argument_inference() {
    accepts("partial-static-argument-inference");
}

#[test]
fn callable_view_cannot_regain_default() {
    rejects("callable-view-cannot-regain-default", "E0314");
}

#[test]
fn excess_static_arguments() {
    rejects("excess-static-arguments", "E0340");
}

#[test]
fn generic_array_return() {
    accepts("generic-array-return");
}

#[test]
fn bounded_record_tuple_return() {
    accepts("bounded-record-tuple-return");
}

#[test]
fn unrelated_generic_return() {
    rejects("unrelated-generic-return", "E0301");
}

#[test]
fn composed_row_with_array_and_callback() {
    accepts("composed-row-with-array-and-callback");
}
