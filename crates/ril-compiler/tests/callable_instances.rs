//! Explicit selections belong to function values, including phantom parameters.
use ril_compiler::sema::SemanticFacts;
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn verified(case: &str, target: &str) -> SemanticFacts {
    let program = Session::with_options(
        ril_test::case_bytes(case).to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap_or_else(|outcome| panic!("{case} {target}: {outcome:?}"));
    let facts = program.facts().clone();
    let core = ril_compiler::lower::lower_core(&program)
        .unwrap_or_else(|error| panic!("{case} {target}: {error:?}"));
    if target == "pointer64" {
        let entry = if facts
            .functions
            .iter()
            .any(|f| f.syntax.name == "test_instances")
        {
            "test_instances"
        } else {
            "test_native"
        };
        ril_codegen::lower::lower_native_with_entry(&core, entry).unwrap();
    }
    facts
}

#[test]
fn explicit_sources_preserve_complete_types_through_core() {
    for name in [
        "scoped-symbolic-array-explicit",
        "scoped-symbolic-empty-explicit",
        "scoped-symbolic-callable-explicit",
        "explicit-named-prefix",
    ] {
        for target in ["pointer32", "pointer64"] {
            verified(
                &format!("tests/regressions/record-bounds.ril::{name}"),
                target,
            );
        }
    }
}

#[test]
fn instances_survive_storage_aliases_defaults_products_and_capture() {
    for target in ["pointer32", "pointer64"] {
        verified(
            "tests/regressions/callable-instances.ril::transport-pointer64",
            target,
        );
    }
}

#[test]
fn runtime_instantiation_preserves_computation_and_partial_choices() {
    for case in [
        "runtime-selection-pointer64",
        "nearby-instance-pointer64",
        "unused-templates-pointer64",
        "instantiation-budget-pointer64",
    ] {
        for target in ["pointer32", "pointer64"] {
            verified(
                &format!("tests/regressions/callable-instances.ril::{case}"),
                target,
            );
        }
    }
}

#[test]
fn phantom_selections_remain_distinct_without_data_parameters() {
    for target in ["pointer32", "pointer64"] {
        let facts = verified(
            "tests/regressions/callable-instances.ril::phantom-pointer64",
            target,
        );
        let definition = facts
            .functions
            .iter()
            .find(|f| f.syntax.name == "read")
            .unwrap()
            .definition;
        let selected = facts
            .copy_invocations
            .iter()
            .filter(|call| call.target == definition && !call.declaration_probe)
            .map(|call| {
                call.instance
                    .as_ref()
                    .expect("actual target retains its instance")
            })
            .collect::<Vec<_>>();
        assert!(selected.len() >= 2);
        assert!(selected.iter().any(|instance| instance != &selected[0]));
    }
}

#[test]
fn static_selections_cannot_be_replaced_or_erase_inference_obligations() {
    for (name, code) in [
        ("reject-immediate-type", "E0301"),
        ("reject-immediate-extent", "E0301"),
        ("reject-stored-dimension", "E0301"),
        ("reject-incompatible-view", "E0301"),
        ("reject-undetermined-error", "E0344"),
        ("reject-excess-arguments", "E0340"),
        ("reject-closed-view-generics", "E0340"),
        ("reject-phantom-effect-view", "E0534"),
    ] {
        let case = format!("tests/regressions/callable-instances.ril::{name}");
        for target in ["pointer32", "pointer64"] {
            let outcome = Session::with_options(
                ril_test::case_bytes(&case).to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
                "{case} {target}: {outcome:?}"
            );
        }
    }
}
