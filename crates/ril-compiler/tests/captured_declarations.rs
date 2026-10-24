use ril_compiler::{CheckOptions, Session, sema::validate::solved_facts};

#[test]
fn handlers_receive_in_their_declaration_environment_during_foreign_generic_calls() {
    let source =
        ril_test::case_source("tests/regressions/effects.ril::handler-declaration-environment");
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap();
        let facts = program.facts();
        assert!(!facts.handlers.is_empty());
        for handler in &facts.handlers {
            assert!(handler.typing_environment.generic_context.contains_key("T"));
            assert!(!handler.typing_environment.generic_context.contains_key("U"));
            assert_eq!(
                handler.lexical,
                *handler.typing_environment.contract_bindings()
            );
        }
        solved_facts(facts).unwrap();
        ril_compiler::lower::lower_core(&program).unwrap();
        let mut damaged = facts.clone();
        damaged.handlers[0].typing_environment = Default::default();
        assert!(solved_facts(&damaged).is_err());
    }
}

#[test]
fn defaults_receive_earlier_arguments_in_a_preparation_scope_before_body_entry() {
    let source = ril_test::case_source(
        "tests/regressions/evaluation-identity.ril::closure-default-uses-earlier-actual",
    );
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap();
        let facts = program.facts();
        let receipt = &facts.default_uses[0];
        let preparation = facts.evaluations[receipt.result_expression.unwrap()].scope;
        let earlier = facts
            .bindings
            .iter()
            .position(|binding| {
                binding.parameter && binding.owner == preparation && binding.name == "left"
            })
            .unwrap();
        assert!(facts.bindings[earlier].context.closure_invocation.is_none());
        ril_compiler::lower::lower_core(&program).unwrap();
        let mut damaged = facts.clone();
        damaged.default_uses[0].result_expression = None;
        assert!(solved_facts(&damaged).is_err());
        let mut damaged = facts.clone();
        damaged.bindings[earlier].context.owner =
            Some(ril_compiler_core::ids::CallableOwner::Global);
        assert!(solved_facts(&damaged).is_err());
    }
}

#[test]
fn closure_defaults_keep_lexical_captures_and_ordered_parameter_environments() {
    let source = ril_test::case_source(
        "tests/regressions/evaluation-identity.ril::closure-default-lexical-environment",
    );
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap();
        solved_facts(program.facts()).unwrap();
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

#[test]
fn default_captures_require_the_original_preparation_scope_and_declaration() {
    use ril_compiler::sema::{copy_contract::CopyInvocationStatus, default_uses::DefaultOrigin};
    use ril_compiler_core::ids::CallableOwner;
    let source =
        ril_test::case_source("tests/regressions/closure-occurrences.ril::default-capture");
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap();
        let facts = program.facts();
        ril_compiler::lower::lower_core(&program).unwrap();
        let receipt = facts
            .default_uses
            .iter()
            .find(|receipt| {
                receipt.origin == DefaultOrigin::DeclarationProbe && receipt.parameter == 1
            })
            .unwrap();
        let id = receipt.id.0 as usize;
        let token = receipt.result_expression.unwrap();
        let scope = facts.evaluations[token].scope;
        let binding = facts
            .bindings
            .iter()
            .position(|binding| {
                binding.parameter && binding.owner == scope && binding.name == "value"
            })
            .unwrap();
        let closure = facts
            .closures
            .iter()
            .position(|closure| {
                closure.creation_default == Some(receipt.id) && closure.captures.contains(&binding)
            })
            .unwrap();
        let actual = facts
            .default_uses
            .iter()
            .find(|receipt| matches!(receipt.origin, DefaultOrigin::Call(_)))
            .unwrap();
        assert_ne!(
            scope,
            facts.evaluations[actual.result_expression.unwrap()].scope
        );
        for mutation in 0..8 {
            let mut changed = facts.clone();
            match mutation {
                0 => {
                    changed.evaluations[token].scope =
                        facts.evaluations[actual.result_expression.unwrap()].scope
                }
                1 => changed.default_uses[id].owner = Some(CallableOwner::Global),
                2 => changed.default_uses[id].parameter = 0,
                3 => changed.bindings[binding].context.owner = Some(CallableOwner::Global),
                4 => {
                    changed.default_uses[id].entered.push(actual.entered[0]);
                    changed.default_uses[id].status = CopyInvocationStatus::Completed;
                }
                5 => changed.default_uses[id].result_expression = actual.result_expression,
                6 => {
                    let owner = changed.closures[closure].site.map(CallableOwner::Lambda);
                    changed.evaluations[token].context.owner = owner;
                    changed.invocation_expressions[token].context.owner = owner;
                }
                7 => {
                    changed.closures[closure].captures.remove(&binding);
                    changed.closures[closure].lexical.remove("value");
                }
                _ => unreachable!(),
            }
            assert!(
                solved_facts(&changed).is_err(),
                "{target}: preparation mutation {mutation}"
            );
        }
    }
}
