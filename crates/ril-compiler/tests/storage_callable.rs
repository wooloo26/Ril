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
fn independent_replay_rejects_a_primitive_instance_with_a_pure_capability_bound() {
    let source = "fn example(){let append:fn(mut []int,int)->() &{}=Array::push}";
    let snapshot = Session::new(source.as_bytes().to_vec()).analyze();
    assert!(
        snapshot
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "E0534")
    );
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
