use ril_compiler::{CompilationOutcome, Session};

fn check(source: &str) -> CompilationOutcome {
    Session::new(source.as_bytes().to_vec()).check()
}
fn accepts(source: &str) {
    let outcome = check(source);
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{source}\n{outcome:?}"
    );
}
fn rejects(source: &str) {
    let outcome = check(source);
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720")),
        "{source}\n{outcome:?}"
    );
}

#[test]
fn constructors_inspections_and_aliases_have_one_producer() {
    accepts("meta let _={let result=Ok(7);let alias=result;assert(alias is Ok(7))}");
    accepts(
        "meta let VALUE={let result:Result<int,str>=Err(\"bad\");match result{Ok(value)->value,Err(error)->len(error)}}\nmeta let _=assert(VALUE==3)",
    );
    rejects("meta let _={let result=Ok(7);let alias=result;0}");
    rejects("meta let _={let first=Ok(7);let second=Ok(7);assert(first is Ok(7))}");
}

#[test]
fn unused_meta_definitions_still_cover_every_normal_exit() {
    rejects("meta fn ignored(){let value=Err(\"ignored\");()} ");
    rejects(
        "meta fn conditional(flag:bool){let value=Ok(1);if flag{assert(value is Ok(_))};()}\nmeta let _=conditional(true)",
    );
    accepts(
        "meta fn inspected(flag:bool){let value=Ok(1);if flag{assert(value is Ok(_))}else{assert(value is Err(_))};()}",
    );
}

#[test]
fn returns_and_parameters_transfer_actual_producers() {
    accepts(
        "meta fn make(flag:bool)->Result<int,str>{if flag{Ok(7)}else{Err(\"bad\")}}\nmeta fn read(value:Result<int,str>)->int{match value{Ok(number)->number,Err(error)->len(error)}}\nmeta let _=assert(read(make(true))==7)\nmeta let _=assert(read(make(false))==3)",
    );
    rejects("meta fn make()->Result<int,str>{Ok(7)}\nmeta let _={make();()}");
    rejects("meta fn wrong()->Result<int,str>{let unrelated=Err(\"lost\");Ok(7)}");
}

#[test]
fn nested_tag_checks_and_boolean_short_circuit_preserve_inner_duties() {
    accepts("meta let _={let result=Ok(Ok(7));let checked=result is Ok(Ok(7));assert(checked)}");
    rejects("meta let _={let inner=Ok(7);let outer=Ok(inner);assert(outer is Ok(_))}");
    rejects(
        "meta let _={let inner=Ok(7);let outer=Some(inner);let checked=outer is None;assert(!checked)}",
    );
    rejects("meta let _={let result=Ok(7);let checked=false && result is Ok(7);assert(!checked)}");
}

#[test]
fn finite_member_graphs_keep_aliases_and_distinct_results() {
    accepts("meta let _={let first=Ok(1);let carrier=(first,first);assert(carrier.0 is Ok(1))}");
    accepts(
        "meta let _={let carrier=[Ok(1),Err(\"two\")];assert(carrier[0] is Ok(1));assert(carrier[1] is Err(\"two\"))}",
    );
    rejects("meta let _={let carrier=[Ok(1),Ok(2)];assert(carrier[0] is Ok(1))}");
}

#[test]
fn known_closures_inspect_captures_only_when_called() {
    accepts("meta let _={let result=Ok(7);let inspect=\\->assert(result is Ok(7));inspect()}");
    rejects("meta let _={let result=Ok(7);let inspect=\\->assert(result is Ok(7));()}");
    rejects("meta let _={let unused=\\->{let result=Ok(7);()};()}");
}

#[test]
fn omitted_defaults_are_independently_checked_even_when_always_supplied() {
    rejects(
        "meta fn discard(value:Result<int,str>=Ok(1)){}\nmeta let _={let supplied=Ok(2);discard(supplied);assert(supplied is Ok(2))}",
    );
    accepts(
        "meta fn inspected(value:Result<int,str>=Ok(1)){assert(value is Ok(_))}\nmeta let _=inspected()",
    );
}

#[test]
fn inspected_static_results_enter_core_with_one_private_receipt_per_producer() {
    use ril_ir::constants::ConstNodeKind;
    let source = "meta let ROOT={let result:Result<int,str>=Ok(7);assert(result is Ok(7));(result,result)}\nfn use_value() &{ROOT}{assert(ROOT.0 is Ok(7))}";
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    let graph = &core.constant_graphs[0];
    let results = graph
        .nodes
        .iter()
        .filter(|node| matches!(&node.kind,ConstNodeKind::Variant{tag,..}if tag=="Prelude::Ok"))
        .collect::<Vec<_>>();
    assert_eq!(results.len(), 1);
    let tuple = graph
        .nodes
        .iter()
        .find_map(|node| {
            if let ConstNodeKind::Tuple(items) = &node.kind {
                Some(items)
            } else {
                None
            }
        })
        .unwrap();
    assert_eq!(tuple[0], tuple[1]);
    let result = verified
        .facts()
        .constant_values
        .iter()
        .find(|value| value.reference.graph == graph.id && value.reference.node == results[0].id)
        .unwrap();
    assert_eq!(result.value.results.len(), 1);
    assert!(
        verified
            .facts()
            .result_duties
            .iter()
            .any(|duty| duty.inspected)
    );
    assert!(verified.facts().explanations.causes.iter().any(|cause| {
        cause
            .description
            .contains("reached static Result tag inspection")
    }));
}

#[test]
fn a_static_receipt_does_not_inspect_a_new_clone() {
    let prefix =
        "meta let ROOT:Result<int,str>={let result=Ok(7);assert(result is Ok(7));result}\n";
    rejects(&format!(
        "{prefix}fn example() &{{ROOT}}{{let copied=clone(ROOT)}}"
    ));
    accepts(&format!(
        "{prefix}fn example() &{{ROOT}}{{let copied=clone(ROOT);assert(copied is Ok(7))}}"
    ));
    let outcome =
        check("meta let ROOT:Result<int,str>=Ok(7)\nfn example() &{ROOT}{assert(ROOT is Ok(7))}");
    assert!(
        matches!(outcome, CompilationOutcome::NotImplemented { .. }),
        "{outcome:?}"
    );
}

#[test]
fn a_small_concrete_model_agrees_on_every_normal_branch() {
    for before in [false, true] {
        for on_true in [false, true] {
            for on_false in [false, true] {
                for panic_true in [false, true] {
                    let inspect = "value is Ok(_);";
                    let source = format!(
                        "meta fn checked(flag:bool){{let value=Ok(1);{}if flag{{{}{}}}else{{{}}};()}}",
                        if before { inspect } else { "" },
                        if on_true { inspect } else { "" },
                        if panic_true { "assert(false);" } else { "" },
                        if on_false { inspect } else { "" }
                    );
                    let concrete_normal_exits = [false, true]
                        .into_iter()
                        .filter(|flag| !(*flag && panic_true));
                    let safe = concrete_normal_exits
                        .into_iter()
                        .all(|flag| before || if flag { on_true } else { on_false });
                    let outcome = check(&source);
                    assert_eq!(
                        matches!(outcome, CompilationOutcome::Accepted { .. }),
                        safe,
                        "{source}\n{outcome:?}"
                    );
                    if !safe {
                        assert!(
                            matches!(outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720"))
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn auxiliary_expression_positions_cannot_hide_result_production() {
    rejects("meta let VALUE=[7][{let ignored=Ok(1);0}]");
    rejects("meta fn bad()->int{[7][{let ignored=Ok(1);0}]}");
    for source in [
        "meta let VALUE=\"{ {let ignored=Ok(1);7} }\"",
        "type Buffer=[{let ignored=Ok(1);2}]int",
        "fn runtime(){if true{meta let VALUE={let ignored=Ok(1);7}}}",
    ] {
        assert!(
            !matches!(check(source), CompilationOutcome::Accepted { .. }),
            "{source}"
        );
    }
}

#[test]
fn old_predicates_and_equal_contents_do_not_inspect_new_producers() {
    rejects(
        "meta fn make()->Result<int,str>{Ok(7)}\nmeta let _={let first=make();let old=first is Ok(7);let second=make();assert(old)}",
    );
    rejects(
        "meta let _={let inner=Ok(1);let matched=false && inner is Ok(_);let wrapper=Some(matched);assert(wrapper is Some(_))}",
    );
    accepts(
        "meta fn inspect(value:Result<int,str>){assert(value is Ok(_))}\nmeta let RENAMED:fn(other:Result<int,str>)->()=inspect\nmeta let _=RENAMED(other:Ok(7))",
    );
}

#[test]
fn result_payload_context_keeps_selected_numeric_representation() {
    accepts(
        "meta let ROOT:Result<f32,str>={let value:Result<f32,str>=Ok(18014399583223809);assert(value is Ok(18014400656965632.0f32));value}",
    );
    accepts(
        "meta let ROOT:Result<int,str>={let value=Ok(7);assert(value is Ok(7));value}\nmeta fn read()->int{match ROOT{Ok(value)->value,Err(error)->len(error)}}\nmeta let _=assert(read()==7)",
    );
}

#[test]
fn cloned_tuple_receipts_preserve_immutable_publication() {
    accepts(
        "meta let ROOT={let value:Result<f32,str>=Ok(18014399583223809);assert(value is Ok(18014400656965632.0f32));(value,value)}\nfn test_native() &{ROOT}{let copied=clone(ROOT);assert(copied.0 is Ok(18014400656965632.0f32))}",
    );
}

#[test]
fn option_publication_does_not_turn_a_nested_result_into_its_outer_duty() {
    let prefix =
        "meta let ROOT={let value:Result<int,str>=Ok(7);assert(value is Ok(7));Some(value)}\n";
    rejects(&format!(
        "{prefix}fn bad() &{{ROOT}}{{let copy=clone(ROOT);assert(copy is Some(_))}}"
    ));
    accepts(&format!(
        "{prefix}fn good() &{{ROOT}}{{let copy=clone(ROOT);assert(copy is Some(Ok(7)))}}"
    ));
}

#[test]
fn repeated_boolean_and_tag_tests_use_the_same_input_choice() {
    accepts(
        "meta fn checked(flag:bool){let value=Ok(1);let alias=flag;if alias{assert(value is Ok(_))};if !flag{assert(value is Ok(_))};()}",
    );
    accepts(
        "meta fn checked(choice:?int){let value=Ok(1);if choice is Some(_){assert(value is Ok(_))};if choice is None{assert(value is Ok(_))};()}",
    );
    accepts(
        "meta let FLAG=true\nmeta fn checked(){let value=Ok(1);if FLAG{assert(value is Ok(_))};()}",
    );
    let outcome = check("meta fn aborted(){let value=Ok(1);1/0;()}");
    assert!(
        matches!(outcome, CompilationOutcome::NotImplemented { .. }),
        "{outcome:?}"
    );
}

#[test]
fn edits_cannot_reuse_an_old_static_inspection_receipt() {
    let checked = "meta let ROOT:Result<int,str>={let value=Ok(7);assert(value is Ok(7));value}";
    let mut session = Session::new(checked.as_bytes().to_vec());
    assert!(session.verify().is_ok());
    session.update(b"meta let ROOT:Result<int,str>=Ok(7)".to_vec());
    assert!(matches!(
        session.check(),
        CompilationOutcome::NotImplemented { .. }
    ));
    session.update(b"meta let ROOT:Result<int,str>={let value=Err(\"changed\");assert(value is Err(\"changed\"));value}".to_vec());
    assert!(session.verify().is_ok());
}

#[test]
fn only_the_resolved_prelude_constructor_can_issue_a_result_receipt() {
    accepts("type Choice{Ok(int)}\nmeta let _={let value=Prelude::Ok(1);assert(value is Ok(1))}");
    accepts("type Ok=int\nmeta let _={let value=Prelude::Ok(1);assert(value is Prelude::Ok(1))}");
    for source in [
        "type Choice{Ok(int)}\nmeta let _={let value=Prelude::Ok(1);assert(value is Choice::Ok(1))}",
        "type Ok=int\nmeta let _={let value=Prelude::Ok(1);assert(value is Ok(1))}",
        "meta let _={let value=Prelude::Ok(1);assert(value is Ok(1));Prelude::Ok(1);()}",
    ] {
        assert!(
            !matches!(check(source), CompilationOutcome::Accepted { .. }),
            "{source}"
        );
    }
}
