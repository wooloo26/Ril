use ril_compiler::{CompilationOutcome, Session};

#[test]
fn optional_zero_input_callbacks_keep_their_independent_input_proof() {
    let source = "fn example(value:?(fn()->int))->int{(value ?? (\\->{return 1}))()}";
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            ril_compiler::CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|error| panic!("{target}: {error:?}"));
        ril_compiler::lower::lower_core(&program).unwrap();
        let mut facts = program.facts().clone();
        let callee = facts
            .copy_call_events
            .iter()
            .filter_map(|event| event.callee_expression)
            .map(|index| &facts.expressions[index].value)
            .find(|value| {
                value.callables.iter().any(|callable| {
                    matches!(callable, ril_compiler::sema::model::Callable::Symbolic(..))
                })
            })
            .unwrap();
        let roots: Vec<_> = callee
            .callback_parameters
            .union(&callee.sources)
            .copied()
            .collect();
        assert!(!roots.is_empty());
        for root in roots {
            facts.bindings[root].pattern = None;
        }
        assert!(ril_compiler::sema::validate::solved_facts(&facts).is_err());
    }
}

#[test]
fn invoked_formal_bound_can_explain_a_declared_named_row() {
    let source = ril_test::case_source(
        "tests/regressions/source-observations.ril::callable-product-open-row",
    );
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    ril_compiler::lower::lower_core(&program).unwrap();
}

#[test]
fn unused_open_unrelated_or_narrowed_callbacks_never_justify_a_concrete_root() {
    for source in [
        "var calls=0\nfn wrong(action:fn()->()&{mut calls})&{mut calls}{}",
        "var calls=0\nfn wrong(action:fn()->())&{mut calls}{action()}",
        "var calls=0\nvar other=0\nfn wrong(action:fn()->()&{mut other})&{mut calls}{action()}",
        "var calls=0\nfn wrong(action:fn()->()&{mut calls})&{mut calls}{let pure:fn()->()&{}=action;pure()}",
        "var calls=0\nfn wrong(action:fn()->()&{mut calls})&{mut calls}{if false{action()}}",
        "var calls=0\nfn wrong(action:fn()->()&{mut calls})&{mut calls}{let view ignored=\\->action()}",
        "var calls=0\nfn wrong(action:fn()->()&{mut calls})&{mut calls}{let read:fn()->()&{calls}=action;read()}",
        "var calls=0\nfn wrong(action:fn()->()&{mut calls})&{mut calls}{with Div::exhausted()->();let _=Div::budget(0,action)}",
    ] {
        let result = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&result,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0529")),
            "{source}: {result:?}"
        );
    }
}

#[test]
fn forwarded_formal_calls_keep_their_entered_occurrences() {
    let source = "var calls=0\nfn step()&{mut calls}{calls+=1}\nfn relay(action:fn()->()&{mut calls})&{mut calls}{action()}\nfn outer(action:fn()->()&{mut calls})&{mut calls}{relay(action)}\nfn example()&{mut calls}{outer(step)}";
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    ril_compiler::lower::lower_core(&program).unwrap();
    assert!(
        program
            .facts()
            .invocations
            .iter()
            .filter(|summary| !summary.symbolic_uses.is_empty())
            .count()
            >= 2
    );
}

#[test]
fn qualified_global_callable_aliases_keep_original_declaration_rows() {
    for (declarations, parameter) in [
        ("type Action=fn(int)->int&{mut calls}", "{step:Action}"),
        (
            "type Action=fn(int)->int&{mut calls}\ntype Tasks={step:Action}",
            "Tasks",
        ),
    ] {
        let source = format!(
            "var calls=0\n{declarations}\nfn step(value:int)->int&{{mut calls}}{{calls+=1;value}}\nfn invoke(value:{parameter})&{{mut calls}}{{assert(value.step(1)==1)}}\nfn example()&{{mut calls}}{{invoke(.{{step:step}})}}"
        );
        let program = Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

#[test]
fn alias_state_names_keep_declaration_bindings_under_shadowing() {
    let source = "var calls=0\ntype Action=fn()->()&{mut calls}\nfn step()&{mut calls}{calls+=1}\nfn invoke(action:Action)&{mut calls}{let calls=1;assert(calls==1);action()}\nfn example()&{mut calls}{invoke(step)}";
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    ril_compiler::lower::lower_core(&program).unwrap();
    let source = "var calls=0\ntype Action=fn()->()&{mut calls}\nfn step()&{mut calls}{calls+=1}\nfn example(){var calls=0;wrong(step) where fn wrong(action:Action)&{mut calls}{action()}}";
    let result = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&result,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0529")),
        "{source}: {result:?}"
    );
}

#[test]
fn qualified_formal_rows_reach_core_on_both_pointer_layouts() {
    for target in ["pointer32", "pointer64"] {
        for source in [
            ril_test::case_source(
                "tests/regressions/source-observations.ril::callable-product-open-row",
            ),
            "var calls=0\nfn step()&{mut calls}{calls+=1}\nfn invoke(action:fn()->()&{mut calls})&{mut calls}{(\\->action())()}\nfn example()&{mut calls}{invoke(step)}",
        ] {
            let program = Session::with_options(
                source.as_bytes().to_vec(),
                ril_compiler::CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|error| panic!("{target} {source}: {error:?}"));
            ril_compiler::lower::lower_core(&program).unwrap();
        }
    }
}
