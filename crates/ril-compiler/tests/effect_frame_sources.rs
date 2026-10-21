//! Handler receivers have their own actual frame and complete Source header.
use ril_compiler::{CheckOptions, Session};

fn accepts(case: &str) {
    let source = ril_test::case_source(&format!("tests/conformance/effects.ril::{case}"));
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|error| panic!("{case}, {target}: {error:?}"));
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

#[test]
fn zero_argument_and_forwarded_handlers_keep_their_actual_activation() {
    for case in [
        "deep-resumption",
        "outer-handler-forwarding",
        "system-yield-local-handling",
    ] {
        accepts(case);
    }
}

#[test]
fn operation_parameters_use_their_operation_header() {
    for case in [
        "accept-handler-parameter-mode",
        "accept-ended-operation-loan",
    ] {
        accepts(case);
    }
}

#[test]
fn operation_and_resume_boundaries_keep_complete_source_views() {
    for case in ["fixed-operation-view", "generic-operation-view"] {
        let source = ril_test::case_source(&format!(
            "tests/regressions/effect-source-views.ril::{case}"
        ));
        for target in ["pointer32", "pointer64"] {
            let program = Session::with_options(
                source.as_bytes().to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|error| panic!("{case}, {target}: {error:?}"));
            ril_compiler::lower::lower_core(&program).unwrap();
        }
    }
    for case in [
        "reject-operation-hidden-dimension",
        "reject-resumption-hidden-dimension",
    ] {
        let source = ril_test::case_source(&format!(
            "tests/regressions/effect-source-views.ril::{case}"
        ));
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome, ril_compiler::CompilationOutcome::Rejected {diagnostics} if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
            "{case}: {outcome:?}"
        );
    }
}

#[test]
fn operation_receivers_replay_original_context_and_signature_after_fact_mutation() {
    use ril_compiler::sema::{
        application_effect::EntryOrigin, model::Ty, scopes::ScopeOrigin, validate::solved_facts,
    };
    let source = ril_test::case_source("tests/conformance/effects.ril::deep-resumption");
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = program.facts();
    let scope = facts
        .scopes
        .records()
        .find_map(|record| match &record.origin {
            ScopeOrigin::Operation(entry)
                if matches!(entry.origin, EntryOrigin::Application(_)) =>
            {
                Some(record.id)
            }
            _ => None,
        })
        .expect("a performed operation must retain its own receiver");
    let operation = match &facts.scopes.get(&scope).unwrap().origin {
        ScopeOrigin::Operation(entry) => entry.operation,
        _ => unreachable!(),
    };
    for mutation in 0..8 {
        let mut changed = facts.clone();
        let ScopeOrigin::Operation(entry) = &mut changed.scopes.get_mut(&scope).unwrap().origin
        else {
            unreachable!()
        };
        match mutation {
            0 => changed.scopes.get_mut(&scope).unwrap().origin = ScopeOrigin::Unresolved,
            1 => entry.origin = EntryOrigin::DeclarationProbe,
            2 => entry.handler = usize::MAX,
            3 => entry.operation = u64::MAX,
            4 => entry.parent = None,
            5 => entry.context.invocation = None,
            6 => {
                changed
                    .operations
                    .values_mut()
                    .find(|op| op.identity == operation)
                    .unwrap()
                    .result = Ty::Bool
            }
            _ => {
                changed
                    .operations
                    .values_mut()
                    .find(|op| op.identity == operation)
                    .unwrap()
                    .source
                    .as_mut()
                    .unwrap()
                    .index = u32::MAX
            }
        }
        assert!(
            solved_facts(&changed).is_err(),
            "mutation {mutation} issued an unchecked operation receiver"
        );
    }
    let mut reordered = facts.clone();
    reordered.invocation_expressions.reverse();
    solved_facts(&reordered).unwrap();
}
