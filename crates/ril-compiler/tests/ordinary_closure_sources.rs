//! Lambda Source types retain their real creator, body and parameter scopes.
use ril_compiler::sema::{SemanticFacts, facts::ScopeId, validate::solved_facts};
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn step_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-observations.ril::closure-captured-step")
}

fn verified(source: &str) -> SemanticFacts {
    let mut facts = None;
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|outcome| panic!("{source}\n{outcome:?}"));
        solved_facts(program.facts()).unwrap();
        ril_compiler::lower::lower_core(&program).unwrap();
        facts = Some(program.facts().clone());
    }
    facts.unwrap()
}

#[test]
fn real_lambda_bodies_and_immutable_generic_locals_supply_complete_source() {
    for source in [
        step_fixture(),
        ril_test::case_source("tests/regressions/source-observations.ril::closure-generic-return"),
        ril_test::case_source(
            "tests/regressions/source-observations.ril::generic-immutable-empty-local",
        ),
        ril_test::case_source(
            "tests/regressions/source-observations.ril::generic-tuple-projection",
        ),
    ] {
        verified(source);
    }
}

#[test]
fn an_open_public_fn_view_does_not_recover_the_original_parameter_view() {
    let source = ril_test::case_source(
        "tests/regressions/source-observations.ril::reject-open-fn-fixed-recovery",
    );
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected {diagnostics}
        if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
        "{source}\n{outcome:?}"
    );
}

#[test]
fn closure_activation_and_formal_owner_cannot_be_deleted_or_borrowed() {
    let facts = verified(step_fixture());
    let probe = facts
        .closure_invocations
        .iter()
        .find(|call| call.probe && call.activation.is_some())
        .unwrap();
    let activation = probe.activation.unwrap();
    let parameter = facts.closures[probe.closure].parameters[0].pattern.span;
    let mut changed = facts.clone();
    changed.closure_invocations[probe.id.0 as usize].activation = None;
    assert!(solved_facts(&changed).is_err());
    let mut changed = facts.clone();
    changed
        .bindings
        .iter_mut()
        .find(|binding| {
            binding.parameter && binding.owner == activation && binding.span == parameter
        })
        .unwrap()
        .owner = ScopeId(0);
    assert!(solved_facts(&changed).is_err());
    let mut changed = facts.clone();
    changed
        .bindings
        .iter_mut()
        .find(|binding| {
            binding.parameter && binding.owner == activation && binding.span == parameter
        })
        .unwrap()
        .context
        .closure_invocation = None;
    assert!(solved_facts(&changed).is_err());
}

#[test]
fn captured_named_headers_keep_their_own_type_selection_at_each_entry() {
    for source in [
        ril_test::case_source(
            "tests/regressions/source-observations.ril::named-generic-captured-header-where",
        ),
        ril_test::case_source(
            "tests/regressions/source-observations.ril::named-generic-distinct-instances-where",
        ),
    ] {
        verified(source);
    }
}

#[test]
fn open_callable_rows_survive_real_product_operands() {
    for source in [
        ril_test::case_source(
            "tests/regressions/source-observations.ril::callable-product-open-row",
        ),
        ril_test::case_source("tests/regressions/record-bounds.ril::scoped-callable-mut"),
    ] {
        verified(source);
    }
}

#[test]
fn a_creation_probe_cannot_be_relabelled_as_an_unrecorded_runtime_call() {
    let facts = verified(step_fixture());
    let probe = facts
        .closure_invocations
        .iter()
        .find(|invocation| {
            invocation.probe
                && facts.closures[invocation.closure]
                    .parameters
                    .iter()
                    .all(|parameter| parameter.ty.is_some())
        })
        .unwrap();
    let mut changed = facts.clone();
    changed.closure_invocations[probe.id.0 as usize].probe = false;
    assert!(solved_facts(&changed).is_err());
}
