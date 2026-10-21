use ril_compiler::{CompilationOutcome, Session};

#[test]
fn primitive_public_argument_slots_preserve_names_modes_and_numeric_context() {
    for target in ["pointer32", "pointer64"] {
        for case in [
            "named-numeric",
            "named-retention",
            "named-map-empty",
            "view-interface",
            "pipeline-order",
            "map-order",
        ] {
            let source =
                ril_test::case_source(&format!("tests/regressions/generic-builtins.ril::{case}"));
            let program = Session::with_options(
                source.as_bytes().to_vec(),
                ril_compiler::CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|error| panic!("{target} {case} {source}: {error:?}"));
            ril_compiler::lower::lower_core(&program).unwrap();
        }
        for (case, code) in [
            ("unknown-label", "E0339"),
            ("duplicate-label", "E0325"),
            ("erased-labels", "E0339"),
            ("stored-map-view", "E0301"),
        ] {
            let source =
                ril_test::case_source(&format!("tests/regressions/generic-builtins.ril::{case}"));
            let result = Session::with_options(
                source.as_bytes().to_vec(),
                ril_compiler::CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .check();
            assert!(
                matches!(&result, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic|diagnostic.code==code)),
                "{target} {case}: {result:?}"
            );
        }
    }
}

#[test]
fn primitive_bound_slots_must_follow_physical_labels_and_source_order() {
    let source = ril_test::case_source("tests/regressions/generic-builtins.ril::named-numeric");
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let event=program.facts().copy_call_events.iter().find(|event| event.callee_expression.is_some_and(|id| matches!(program.facts().expressions[id].value.callables.as_slice(),[ril_compiler::sema::model::Callable::Builtin(name)] if name=="Array::push"))).unwrap();
    for mutation in 0..3 {
        let mut facts = program.facts().clone();
        let preparation = facts
            .call_arguments
            .iter_mut()
            .find(|row| row.source_event == event.id)
            .unwrap();
        let first = preparation.supplied[&0];
        let second = preparation.supplied[&1];
        if mutation < 2 {
            preparation.supplied.insert(0, second);
            preparation.supplied.insert(1, first);
            if mutation == 1 {
                for row in &mut facts.invocation_expressions {
                    if row.expression == first.expression {
                        row.argument_of = Some((event.id, 1));
                    }
                    if row.expression == second.expression {
                        row.argument_of = Some((event.id, 0));
                    }
                }
            }
        } else {
            preparation.evaluated.swap(1, 2);
        }
        assert!(
            ril_compiler::sema::validate::solved_facts(&facts).is_err(),
            "slot/order mutation {mutation}"
        );
    }
}

fn accepted(source: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{source}: {outcome:?}"
    );
}

fn rejects(source: &str, code: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
        "{source}: {outcome:?}"
    );
}

#[test]
fn storage_descriptors_keep_fresh_factory_reception() {
    accepted(
        "type Cell={mut count:int}\nfn make(n:int)->Cell{Cell.{count:n}}\nfn example(){let append:fn(mut []Cell,Cell)->() &mut=Array::push;let factory:fn(int)->Cell=make;let mut items:[]Cell=[];append(mut items,factory(3));items[0].count+=1}",
    );
    accepted(
        "type Cell={mut count:int}\nfn example(){let insert:fn(mut []Cell,int,Cell)->() &mut=Array::insert;let mut items:[]Cell=[];insert(mut items,0,Cell.{count:3});items[0].count+=1}",
    );
    accepted(
        "type Cell={mut count:int}\nfn example(){let set:fn(mut [str:Cell],str,Cell)->() &mut=Map::set;let mut items:[str:Cell]=[:];set(mut items,\"key\",Cell.{count:3});assert(items[\"key\"]?.count==Some(3))}",
    );
}

#[test]
fn storage_descriptor_context_preserves_modes_and_type_correlations() {
    for (source, code) in [
        (
            "fn example(){let bad:fn(mut []int,str)->() &mut=Array::push}",
            "E0301",
        ),
        (
            "fn example(){let bad:fn([]int,int)->() &mut=Array::push}",
            "E0301",
        ),
        (
            "fn example(){let bad:fn(mut []int,int)->int &mut=Array::push}",
            "E0301",
        ),
        (
            "fn example(){let bad:fn(mut [str:int],int,int)->() &mut=Map::set}",
            "E0301",
        ),
        (
            "type Cell={mut count:int}\nfn example(){let append:fn(mut []Cell,Cell)->() &mut=Array::push;let item=Cell.{count:3};let mut items:[]Cell=[];append(mut items,item);items[0].count+=1}",
            "E0522",
        ),
        (
            "fn example(){let bad:fn(mut []int,int)->() &{}=Array::push}",
            "E0534",
        ),
    ] {
        rejects(source, code);
    }
}

#[test]
fn storage_descriptor_retention_remains_explicit() {
    accepted(
        "type Cell={mut count:int}\nfn example(){let append:fn(mut []Cell,^mut Cell)->() &^mut=Array::push;let mut item=Cell.{count:3};let mut items:[]Cell=[];append(mut items,^mut item);items[0].count+=1;item.count+=1}",
    );
    rejects(
        "type Cell={mut count:int}\nfn example(){let append:fn(mut []Cell,Cell)->() &mut=Array::push;let mut item=Cell.{count:3};let mut items:[]Cell=[];append(mut items,^mut item);item.count+=1}",
        "E0405",
    );
}

#[test]
fn primitive_declaration_receipts_cannot_be_deleted_swapped_or_monomorphized() {
    use ril_compiler::sema::{builtin_sources::BuiltinDeclaration, validate::solved_facts};
    use ril_compiler_core::builtin_calls::GenericBuiltin;
    let source = "fn example(){let raw=Array::push;let append:fn(mut [][0][2]int,[0][2]int)->() &mut=raw;let mut items:[][0][2]int=[];append(mut items,[])}";
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    ril_compiler::lower::lower_core(&program).unwrap();
    for mutation in 0..8 {
        let mut facts = program.facts().clone();
        let observation = facts
            .builtin_source_observations
            .iter()
            .position(|row| row.identity == "Array::push")
            .unwrap();
        match mutation {
            0 => {
                facts.builtin_source_observations.remove(observation);
            }
            1 => {
                facts.builtin_source_observations[observation].full_header =
                    BuiltinDeclaration::Generic(GenericBuiltin::ArrayInsert)
            }
            2 => facts.builtin_source_observations[observation]
                .written_formals
                .clear(),
            3 => {
                let entry = facts.builtin_source_observations[observation].expression;
                facts.expressions[entry].value.signature = Some(vec![]);
            }
            4 => facts
                .bindings
                .iter_mut()
                .find(|binding| binding.name == "append")
                .unwrap()
                .value
                .callables
                .clear(),
            5 => {
                let entry = facts.builtin_source_observations[observation].expression;
                facts.expressions[entry].value.ty = ril_compiler::sema::model::Ty::Unit;
            }
            6 | 7 => {
                let signature = if mutation == 6 {
                    "fn(mut [][0][3]int,[0][3]int)->()&mut"
                } else {
                    "fn(mut [][0][2]int,[0][2]int)->()&{}"
                };
                let replacement = Session::new(
                    format!("fn other(){{let changed:{signature}=Array::push}}").into_bytes(),
                )
                .analyze();
                let witness = replacement
                    .facts()
                    .unwrap()
                    .bindings
                    .iter()
                    .find(|binding| binding.name == "changed")
                    .unwrap()
                    .value
                    .source_type_witness
                    .clone()
                    .unwrap();
                let value = &mut facts
                    .bindings
                    .iter_mut()
                    .find(|binding| binding.name == "append")
                    .unwrap()
                    .value;
                value.source_type_witness = Some(witness);
                value.callable_bounds.clear();
            }
            _ => unreachable!(),
        }
        assert!(
            solved_facts(&facts).is_err(),
            "primitive declaration mutation {mutation}"
        );
    }
}

#[test]
fn independent_replay_rejects_a_primitive_instance_with_a_pure_capability_bound() {
    let source = "fn example(){let append:fn(mut []int,int)->() &{}=Array::push}";
    let snapshot = Session::new(source.as_bytes().to_vec()).analyze();
    assert!(
        snapshot
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "E0534")
    );
    assert!(ril_compiler::sema::validate::solved_facts(snapshot.facts().unwrap()).is_err());
}

#[test]
fn generic_primitive_sources_reach_core_on_both_pointer_layouts() {
    for target in ["pointer32", "pointer64"] {
        for case in [
            "tests/regressions/generic-builtins.ril::distinct-source-instances",
            "tests/regressions/generic-builtins.ril::raw-dispatch",
            "tests/regressions/generic-builtins.ril::truncate",
            "tests/conformance/storage.ril::fresh-factory-results",
        ] {
            let source = ril_test::case_source(case);
            let program = Session::with_options(
                source.as_bytes().to_vec(),
                ril_compiler::CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|error| panic!("{target} {case}: {error:?}"));
            ril_compiler::lower::lower_core(&program).unwrap();
        }
        for (case, code) in [
            ("hidden-element-mismatch", "E0301"),
            ("hidden-map-value-mismatch", "E0301"),
            ("fixed-receiver", "E0301"),
            ("pure-bound", "E0534"),
            ("retention-bound", "E0534"),
        ] {
            let source =
                ril_test::case_source(&format!("tests/regressions/generic-builtins.ril::{case}"));
            let result = Session::with_options(
                source.as_bytes().to_vec(),
                ril_compiler::CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .check();
            assert!(
                matches!(&result, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic|diagnostic.code==code)),
                "{target} {case}: {result:?}"
            );
        }
    }
}
