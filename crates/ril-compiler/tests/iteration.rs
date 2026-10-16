use ril_compiler::{CompilationOutcome, ProjectSource, Session};

fn check(source: &str) -> CompilationOutcome {
    Session::new(source.as_bytes().to_vec()).check()
}

#[test]
fn dynamic_iterator_states_use_regular_repeated_scalar_transfers() {
    for source in [
        "use ril/iter\nfn collect_from(state:int)->[]int{Iter::collect(state,Iter::indexed([1,2]))}",
        "use ril/iter\nfn fold_from(state:int)->int{Iter::fold(state,Iter::indexed([1,2]),0,\\sum,n->sum+n)}",
        "use ril/iter\nfn filtered(state:int,limit:int)->[]int{Iter::collect(state,Iter::filter(Iter::indexed([1,2]),\\n->n>limit))}",
    ] {
        let outcome = check(source);
        assert!(
            matches!(outcome, CompilationOutcome::Accepted { .. }),
            "{source}: {outcome:?}"
        );
    }
    let items = (0..40)
        .map(|value| value.to_string())
        .collect::<Vec<_>>()
        .join(",");
    let outcome = check(&format!(
        "use ril/iter\nfn example(){{let values=Iter::collect(0,Iter::indexed([{items}]));assert(len(values)==40)}}"
    ));
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
}

#[test]
fn collection_and_fold_preserve_readonly_element_and_accumulator_origins() {
    for body in [
        "fn bad(items:[]Cell){let mut gathered=Iter::collect(0,Iter::indexed(items));gathered[0].count+=1}",
        "fn bad(initial:Cell){let mut value=Iter::fold(0,Iter::indexed([1]),initial,\\acc,n->acc);value.count+=1}",
    ] {
        let outcome = check(&format!(
            "use ril/iter\ntype Cell={{mut count:int}}\n{body}"
        ));
        assert!(
            matches!(outcome, CompilationOutcome::Rejected { ref diagnostics } if diagnostics.iter().any(|diagnostic| matches!(diagnostic.code.as_str(), "E0520"|"E0522"|"E0528"))),
            "{body}: {outcome:?}"
        );
    }
}

#[test]
fn original_explicit_iteration_sources_check_with_their_actual_transition_values() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests");
    let directory = std::env::temp_dir().join("ril-explicit-iteration-source-contract");
    let mut checked = 0;
    for case in ril_test::discover_cases(&root)
        .unwrap()
        .into_iter()
        .filter(|case| case.id.starts_with("tests/stdlib/iter.ril::"))
    {
        let outcome = Session::with_project(
            directory.join(&case.root),
            case.files
                .iter()
                .map(|file| ProjectSource {
                    path: directory.join(&file.name),
                    bytes: file.bytes.clone(),
                })
                .collect(),
            Default::default(),
        )
        .unwrap()
        .check();
        assert!(
            matches!(outcome, CompilationOutcome::Accepted { .. }),
            "{}: {outcome:?}",
            case.id
        );
        checked += 1;
    }
    assert_eq!(checked, 5);
}
