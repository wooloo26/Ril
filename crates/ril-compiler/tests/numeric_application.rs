use ril_compiler::{CompilationOutcome, Session};

fn assert_numeric_history_has_complete_resolutions(facts: &ril_compiler::sema::SemanticFacts) {
    use ril_compiler::sema::{model::Ty, numeric_selection::NumericHoleState};
    for fact in &facts.expressions {
        let Ty::NumericHole(id) = fact.value.ty else {
            continue;
        };
        let hole = facts.numeric_holes.get(id.0 as usize).unwrap();
        assert_eq!(hole.id, id);
        let NumericHoleState::Committed { resolution, .. } = &hole.state else {
            panic!("unresolved historical numeric expression: {fact:?}");
        };
        assert!(!resolution.dependencies.uses.is_empty());
        assert!(!resolution.dependencies.selections.is_empty());
        for selection in &resolution.dependencies.selections {
            let selected = &facts.numeric_selections[selection.0 as usize];
            assert_eq!(selected.id, *selection);
            assert!(resolution.dependencies.uses.contains(&selected.literal));
        }
    }
}

#[test]
fn receiving_type_precedes_named_generic_and_effect_instance_selection() {
    for source in [
        "fn identity<T>(value:T)->T{value}\nfn example(){let number:f32=identity(16777217)}",
        "fn choose<T>(left:T,right:T)->T{left}\nfn example(){let number:f32=choose(16777217,1+2)}",
        "fn sum(left:f32,right:f32)->f32{left+right}\nfn example(){let number=sum(1+2,3.0f32)}",
        "fn choose<T>(left:T,right:T)->T{left}\nfn example(){let number=choose(16777217,3.0f32)}",
        "fn choose<T>(left:T,right:T)->T{left}\nfn example(){let number=choose(16777217+1,3.0f32)}",
        "fn choose<T>(left:T,right:T)->T{left}\nfn peer()->f32{3.0f32}\nfn example(){let number=choose(16777217+1,peer())}",
        "fn identity<T>(value:T)->T{value}\nfn choose<T>(left:T,right:T)->T{left}\nfn example(){let number=choose(16777217+1,identity(3.0f32))}",
        "fn identity<T>(value:T)->T{value}\nfn choose<T>(left:T,right:T)->T{left}\nfn example(){let number=choose(1.0+2,identity(3.0f32))}",
        "fn identity<T>(value:T)->T{value}\nfn choose<T>(left:T,right:T)->T{left}\nfn example(){let number=choose(18446744073709551615,identity(1u64))}",
        "meta let STORED:f32=16777217\nfn identity<T>(value:T)->T{value}\nfn choose<T>(left:T,right:T)->T{left}\nfn example() &{STORED}{let number=choose(STORED+1,identity(3.0f32))}",
        "fn identity<T>(value:T)->T{value}\nfn choose<T>(left:T,right:T)->T{left}\nfn example(){let peer:f32=3;let number=choose(identity(16777217),peer)}",
        "fn accept(value:u64)->u64{value}\nfn example(){let number=accept(18446744073709551615)}",
        "fn defaults(value:f32=16777217)->f32{value}\nfn example(){let number=defaults()}",
        "fn example(){let number=(\\value:f32->value)(16777217)}",
        "fn example(){let number:?f32=Some(16777217);let result:Result<f32,str>=Ok(16777217);assert(result is Ok(_))}",
        "fn identity<T>(value:T)->T{value}\nfn outer<T>(value:T)->f32{identity(16777217)}\nfn example(){let number=outer(\"outer T is str\")}",
        "fn accept(value:f32)->f32{value}\nfn example(){let alias:fn(other:f32)->f32=accept;let number=alias(other:16777217)}",
        "eff Read<T>{get(value:T)->T}\nfn read<T>(value:T)->T @Read<T>{Read<T>::get(value)}\nfn example(){with Read<f32>::get(value)->resume value;let number:f32=read(16777217)}",
        "eff Read<T>{get(value:T)->T}\nfn example(){with Read<f32>::get(value)->resume value;let number=Read<f32>::get(16777217)}",
    ] {
        let program = Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap_or_else(|outcome| panic!("{source}: {outcome:?}"));
        assert_numeric_history_has_complete_resolutions(program.facts());
        ril_compiler::lower::lower_core(&program)
            .unwrap_or_else(|outcome| panic!("{source}: {outcome:?}"));
    }
}

#[test]
fn context_cannot_reselect_a_stored_or_suffixed_argument() {
    for source in [
        "fn identity<T>(value:T)->T{value}\nfn example(){let number:f32=identity(1int)}",
        "fn identity<T>(value:T)->T{value}\nfn example(){let stored=1;let number:f32=identity(stored)}",
        "fn accept(value:u8)->u8{value}\nfn example(){let number=accept(256)}",
        "fn identity<T>(value:T)->T{value}\nfn choose<T>(left:T,right:T)->T{left}\nfn example(){let number=choose(1.0,identity(3int))}",
        "fn identity<T>(value:T)->T{value}\nfn choose<T>(left:T,right:T)->T{left}\nfn example(){let number=choose(256,identity(3u8))}",
        "fn identity<T>(value:T)->T{value}\nfn choose<T>(left:T,right:T)->T{left}\nfn example(){let number=choose(1i8+2,identity(3u8))}",
        "meta let STORED:f32=16777217\nfn identity<T>(value:T)->T{value}\nfn example() &{STORED}{let number:f64=identity(STORED)}",
        "meta let STORED:f32=16777217\nfn identity<T>(value:T)->T{value}\nfn choose<T>(left:T,right:T)->T{left}\nfn example() &{STORED}{let number=choose(STORED+1,identity(3.0f64))}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome, CompilationOutcome::Rejected { .. }),
            "{source}: {outcome:?}"
        );
    }
}

#[test]
fn numeric_selection_does_not_reuse_a_differently_instantiated_handler() {
    let source = "eff Read<T>{get(value:T)->T}\nfn read<T>(value:T)->T @Read<T>{Read<T>::get(value)}\nfn example(){with Read<int>::get(value)->resume value;let number:f32=read(16777217)}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0612")),
        "{outcome:?}"
    );
}

#[test]
fn overflowing_selected_arithmetic_keeps_a_runtime_exit_instead_of_an_invalid_constant() {
    let source =
        ril_test::case_source("tests/conformance/numeric.ril::deferred-arithmetic-overflow");
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts: Vec<_> = program
        .facts()
        .expressions
        .iter()
        .filter(|fact| {
            fact.source_id
                .and_then(|id| program.semantic_hir().expression(id))
                .is_some_and(|node| {
                    matches!(&node.kind, ril_compiler::hir::nodes::ExprKind::Binary { operator, .. } if operator == "+")
                })
        })
        .collect();
    assert!(!facts.is_empty());
    assert!(facts.iter().all(|fact| {
        if let ril_compiler::sema::model::Ty::NumericHole(id) = fact.value.ty {
            matches!(
                &program.facts().numeric_holes[id.0 as usize].state,
                ril_compiler::sema::numeric_selection::NumericHoleState::Committed { resolution, .. }
                    if resolution.number_type == ril_compiler::numeric_literals::NumberType::I8
                        && resolution.constant.is_none()
                        && resolution.encoded.is_none()
            )
        } else {
            fact.value.ty == ril_compiler::sema::model::Ty::Int("i8".into())
                && fact.value.constant.is_none()
        }
    }));
    assert_numeric_history_has_complete_resolutions(program.facts());
    ril_compiler::lower::lower_core(&program).unwrap();
}

#[test]
fn parent_numeric_fault_and_child_cancellation_keep_distinct_result_exits() {
    let source = r#"
use ril/concurrent::{scope}
fn choose<T>(left:T,right:T)->T{left}
fn inspect<T>(value:T,result:Result<int,str>)->T{assert(result is Err(_));value}
fn example() @Concurrent {
    let result:Result<int,str>=Err("uninspected")
    let outcome=scope \mut s->{s.fork(\->());Ok(choose(1/0,inspect(3int,result)))}
    assert(outcome is Ok(_)|Err(_))
}
"#;
    // A body panic propagates outward (STD structured concurrency); only a
    // child-triggered cancellation recovers as scope Err. No normal path can
    // drop an unchecked result here: the ordinary path inspects it, while the
    // arithmetic-fault path abandons this callable's obligations.
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    ril_compiler::lower::lower_core(&program).unwrap();
    let child_fault = source.replace("s.fork(\\->())", "s.fork(\\->panic(\"child\"))");
    let outcome = Session::new(child_fault.into_bytes()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720")),
        "{outcome:?}"
    );
}
