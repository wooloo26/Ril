use ril_compiler::{CheckOptions, Session};

fn verified(case: &str, target: &str) -> ril_compiler::hir::VerifiedProgram {
    let program = Session::with_options(
        ril_test::case_bytes(case).to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap_or_else(|error| panic!("{case}/{target}: {error:?}"));
    ril_compiler::lower::lower_core(&program).unwrap();
    program
}

#[test]
fn abrupt_defaults_keep_their_prefix_without_inventing_a_body_entry() {
    for target in ["pointer32", "pointer64"] {
        let program = verified(
            "tests/regressions/application-results.ril::early-formal-before-abrupt-default",
            target,
        );
        let facts = program.facts();
        let default = facts
            .default_uses
            .iter()
            .find(|default| {
                matches!(
                    default.owner,
                    Some(ril_compiler_core::ids::CallableOwner::Lambda(_))
                ) && !default.evaluation_complete
                    && matches!(
                        default.origin,
                        ril_compiler::sema::default_uses::DefaultOrigin::Call(_)
                    )
            })
            .expect("an actually evaluated abrupt lambda default");
        let ril_compiler::sema::default_uses::DefaultOrigin::Call(event) = default.origin else {
            unreachable!()
        };
        let root = default.result_expression.unwrap();
        assert_eq!(
            facts.evaluations[root].context.default_use,
            Some(default.id)
        );
        assert!(facts.bindings.iter().any(
            |binding| binding.name == "seen" && binding.owner == facts.evaluations[root].scope
        ));
        assert!(!facts.closure_invocations.iter().any(|call|
            matches!(call.entry.origin, ril_compiler::sema::application_effect::EntryOrigin::Application(actual) if actual == event)));
        assert!(default.entered.is_empty());
    }
}
