use ril_compiler::sema::application_effect::{EntryOrigin, InputOrigin};
use ril_compiler::{CheckOptions, Session};

fn verified(name: &str, layout: &str) -> ril_compiler::hir::VerifiedProgram {
    let source = ril_test::case_source(&format!("tests/regressions/callable-inputs.ril::{name}"));
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: layout.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap_or_else(|outcome| panic!("{name} {layout}: {outcome:?}"))
}

#[test]
fn original_inputs_cross_ordinary_and_generated_callable_entries_on_both_layouts() {
    for layout in ["pointer32", "pointer64"] {
        for name in [
            "inferred-fixed-input",
            "derive-clone-view",
            "derive-repeated-activation",
            "derive-construction",
            "derive-nested-fixed-input",
            "derive-named-construction",
            "derive-named-repeated-activation",
            "derive-distinct-targets",
        ] {
            let program = verified(name, layout);
            let _core = ril_compiler::lower::lower_core(&program).unwrap();
        }
    }
}

#[test]
fn a_named_recipe_receives_the_actual_resume_completion_occurrence() {
    for layout in ["pointer32", "pointer64"] {
        let program = verified("derive-resume-completion", layout);
        let _core = ril_compiler::lower::lower_core(&program).unwrap();
        let facts = program.facts();
        let hir = facts.semantic_hir.as_deref().unwrap();
        let identity = facts
            .copy_invocations
            .iter()
            .find_map(|call| {
                let EntryOrigin::Generated { inputs, .. } = &call.entry.origin else {
                    return None;
                };
                inputs.iter().find_map(|input| {
                    let InputOrigin::Copied { observation, .. } = input else {
                        return None;
                    };
                    let identity = facts.evaluations[observation.0 as usize].identity?;
                    matches!(
                        &hir.expression(identity.source)?.kind,
                        ril_compiler::hir::nodes::ExprKind::Control {
                            operation: ril_syntax::ast::ControlOperation::Resume,
                            ..
                        }
                    )
                    .then_some(identity)
                })
            })
            .expect("derive must consume the actual resume completion occurrence");
        assert_eq!(
            facts.activations[identity.activation.0 as usize].kind,
            ril_compiler::sema::application_effect::ActivationKind::ControlTransfer
        );
    }
}

#[test]
fn an_inferred_protected_answer_keeps_its_source_through_an_inline_recipe() {
    for layout in ["pointer32", "pointer64"] {
        let program = verified("derive-resumed-answer", layout);
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

#[test]
fn original_dimensions_permissions_and_draft_escape_rules_still_reject() {
    for layout in ["pointer32", "pointer64"] {
        for (name, code) in [
            ("derive-nested-dimension-mismatch", "E0301"),
            ("inferred-read-cannot-write", "E0520"),
            ("derive-live-input", "E0536"),
            ("derive-draft-escape", "E0607"),
            ("derive-named-dimension-mismatch", "E0301"),
            ("derive-copy-cannot-reopen-construction", "E0301"),
            ("derive-named-draft-escape", "E0607"),
        ] {
            let source =
                ril_test::case_source(&format!("tests/regressions/callable-inputs.ril::{name}"));
            let outcome = Session::with_options(
                source.as_bytes().to_vec(),
                CheckOptions {
                    target: layout.into(),
                    ..Default::default()
                },
            )
            .check();
            assert!(
                matches!(&outcome, ril_compiler::CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
                "{name} {layout}: {outcome:?}"
            );
        }
    }
}
