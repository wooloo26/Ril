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
fn symbolic_type_through_three_frames() {
    accepts("symbolic-type-through-three-frames");
}

#[test]
fn open_record_through_generic_identity() {
    accepts("open-record-through-generic-identity");
}

#[test]
fn generic_literal_collections_keep_their_real_type_uid_and_nested_sources() {
    accepts("generic-literal-collection-source-graphs");
}

#[test]
fn inferred_literal_arrays_keep_dynamic_outer_coordinates() {
    rejects("inferred-literal-array-remains-dynamic", "E0301");
}

#[test]
fn literal_maps_preserve_stored_empty_inner_dimensions() {
    rejects("literal-map-keeps-stored-inner-dimensions", "E0301");
}

#[test]
fn const_nominal_formals_retain_their_actual_static_value_and_sort() {
    accepts("const-nominal-formal-source-graph");
    rejects("const-nominal-formal-value-conflict", "E0301");
    rejects("const-nominal-formal-sort-conflict", "E0323");
}

#[test]
fn nested_type_receipts_cannot_substitute_an_intermediate_frames_own_binder() {
    use ril_compiler::sema::{
        effect_identity::{ArgumentKey, StaticBinderSort},
        model::Ty,
        validate::{ValidationIssueKind, solved_facts},
    };
    let source = ril_test::case_source(
        "tests/regressions/source-transport.ril::symbolic-type-through-three-frames",
    );
    for layout in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: layout.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap();
        let facts = program.facts();
        solved_facts(facts).unwrap();
        let definition = |name| {
            facts
                .functions
                .iter()
                .find(|function| function.syntax.name == name)
                .unwrap()
                .definition
        };
        let identity = definition("identity");
        let forward = definition("forward");
        let outer = definition("outer");
        let inner = facts
            .copy_invocations
            .iter()
            .find(|call| {
                if call.target != identity
                    || !call
                        .entry
                        .arguments
                        .first()
                        .is_some_and(|argument| matches!(&argument.value().ty, Ty::Generic(_)))
                {
                    return false;
                }
                let Some(parent) = call
                    .parent
                    .and_then(|id| facts.copy_invocations.get(id.0 as usize))
                else {
                    return false;
                };
                parent.target == forward
                    && parent
                        .parent
                        .and_then(|id| facts.copy_invocations.get(id.0 as usize))
                        .is_some_and(|call| call.target == outer)
            })
            .unwrap();
        let parent = inner.parent.unwrap();
        let binder = |definition| {
            facts
                .generic_binders
                .values()
                .find(|binder| binder.definition == definition && binder.index == 0)
                .unwrap()
                .identity
                .clone()
        };
        let outer_binder = binder(outer);
        let intermediate_binder = binder(forward);
        let receipt = facts
            .effect_invocations
            .iter()
            .find(|row| row.invocation == Some(inner.id))
            .unwrap();
        assert!(matches!(&receipt.arguments[0].key,
            Some(ArgumentKey::Binder { identity, sort: StaticBinderSort::Type })
                if identity == &outer_binder));

        for rewrite_parent in [false, true] {
            let mut changed = facts.clone();
            for receipt in changed.effect_invocations.iter_mut().filter(|row| {
                row.invocation == Some(inner.id)
                    || (rewrite_parent && row.invocation == Some(parent))
            }) {
                receipt.arguments[0].key = Some(ArgumentKey::Binder {
                    identity: intermediate_binder.clone(),
                    sort: StaticBinderSort::Type,
                });
                let syntax = receipt.arguments[0].syntax.as_mut().unwrap();
                syntax.kind = ril_syntax::ast::TypeKind::Name {
                    path: vec![format!("\0effect-binder:{intermediate_binder}")],
                    arguments: vec![],
                };
            }
            let errors = solved_facts(&changed).unwrap_err();
            assert!(
                errors.iter().any(|issue| matches!(&issue.kind,
                ValidationIssueKind::RecordBound(message) if message.contains("explicit"))),
                "{layout}: {errors:?}"
            );
        }
    }
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

#[test]
fn row_remainders_cannot_forget_empty_inner_dimensions() {
    rejects("row-remainder-empty-inner-dimension-conflict", "E0301");
    rejects("explicit-row-remainder-dimension-conflict", "E0301");
}

#[test]
fn original_headers_preserve_nested_const_arguments() {
    accepts("nested-const-original-headers");
    rejects("nested-const-callback-value-conflict", "E0301");
    rejects("nested-const-header-sort-conflict", "E0323");
}
