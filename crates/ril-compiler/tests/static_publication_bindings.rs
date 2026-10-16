//! Publication aliases follow lexical tokens and share sealed object identities.
use ril_compiler::sema::facts::{Permission, Publication};
use ril_compiler::{CompilationOutcome, Session};

fn core(source: &str) -> ril_compiler::sema::SemanticFacts {
    let verified = Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
    ril_compiler::lower::lower_core(&verified).expect("closed local publication reaches Core");
    verified.facts().clone()
}

#[test]
fn original_same_spelling_reference_shadow_is_legal_and_has_distinct_origins() {
    let facts = core(ril_test::case_source(
        "tests/regressions/static.ril::static-reference-shadowing",
    ));
    let values: Vec<_> = facts
        .bindings
        .iter()
        .filter(|binding| binding.name == "VALUES")
        .collect();
    assert_eq!(values.len(), 2);
    assert!(
        values[0]
            .value
            .origins
            .nodes
            .is_disjoint(&values[1].value.origins.nodes)
    );
}

#[test]
fn local_first_publication_preserves_aliases_and_equal_allocations_remain_distinct() {
    let facts = core(
        "fn example(){meta let FIRST=[1];meta let ALIAS=FIRST;meta let SECOND=[1];assert(FIRST==SECOND)}",
    );
    let value = |name| {
        &facts
            .bindings
            .iter()
            .find(|binding| binding.name == name)
            .unwrap()
            .value
    };
    assert_eq!(value("FIRST").origins, value("ALIAS").origins);
    assert!(
        value("FIRST")
            .origins
            .nodes
            .is_disjoint(&value("SECOND").origins.nodes)
    );
    assert!(
        facts
            .constant_values
            .iter()
            .all(|fact| fact.value.permission == Permission::Read
                && fact.value.publication == Publication::Immutable)
    );
}

#[test]
fn hidden_local_reference_keeps_the_same_pool_node_through_a_captured_helper() {
    let facts = core(
        r#"
fn example(){
    meta let VALUES=[1]
    meta let KEEP=\->VALUES
    {
        meta let VALUES=[2]
        meta let RECOVERED=KEEP()
        assert(VALUES[0]==2 && RECOVERED[0]==1)
    }
    meta let RESTORED=VALUES
    assert(RESTORED[0]==1)
}
"#,
    );
    let values: Vec<_> = facts
        .bindings
        .iter()
        .filter(|binding| binding.name == "VALUES")
        .collect();
    let value = |name| {
        &facts
            .bindings
            .iter()
            .find(|binding| binding.name == name)
            .unwrap()
            .value
    };
    assert_eq!(value("RECOVERED").origins, values[0].value.origins);
    assert_eq!(value("RESTORED").origins, values[0].value.origins);
    assert!(
        value("RECOVERED")
            .origins
            .nodes
            .is_disjoint(&values[1].value.origins.nodes)
    );
}

#[test]
fn branch_for_while_and_match_scopes_restore_static_visibility() {
    core(
        r#"
fn example(flag:bool){
    meta let VALUES=[1]
    if flag{meta let VALUES=[2];assert(VALUES[0]==2)}else{meta let VALUES=[3];assert(VALUES[0]==3)}
    for [1] as value{meta let VALUES=[4];assert(VALUES[0]==4 && value==1)}
    while false{meta let VALUES=[5];assert(VALUES[0]==5)}
    match flag{true->{meta let VALUES=[6];assert(VALUES[0]==6)},false->{}}
    meta let RESTORED=VALUES
    assert(RESTORED[0]==1)
}
"#,
    );
}

#[test]
fn edited_session_does_not_reuse_a_previous_same_named_publication() {
    let before = "fn example(){meta let VALUES=[1];{meta let VALUES=[2];assert(VALUES[0]==2)}}";
    let after = "fn example(){meta let VALUES=[1];{meta let VALUES=[3];meta let ALIAS=VALUES;assert(ALIAS[0]==3)}}";
    let mut session = Session::new(before.as_bytes().to_vec());
    session.verify().unwrap();
    session.update(after.as_bytes().to_vec());
    let edited = session.verify().unwrap();
    let fresh = Session::new(after.as_bytes().to_vec()).verify().unwrap();
    assert_eq!(
        format!("{:?}", edited.facts().constant_values),
        format!("{:?}", fresh.facts().constant_values)
    );
    ril_compiler::lower::lower_core(&edited).unwrap();
}

#[test]
fn local_pool_publication_cannot_seal_an_unchecked_result_or_grant_write_authority() {
    let source = "fn bad(){meta let VALUES=[1];VALUES[0]=2}";
    let result = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&result, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| matches!(diagnostic.code.as_str(), "E0520" | "E0522" | "E0528"))),
        "{result:?}"
    );
    let source = "fn bad(){meta let VALUES={let result:Result<int,str>=Ok(1);[result]}}";
    let result = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&result, CompilationOutcome::NotImplemented { reason } if reason.detail.contains("local meta Result publication")),
        "{result:?}"
    );
    let source = "meta let VALUES={let result:Result<int,str>=Ok(1);[result]}";
    let result = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&result, CompilationOutcome::NotImplemented { reason } if reason.detail.contains("pending static Result publication")),
        "{result:?}"
    );
    let source = "meta let VALUES={let result:Result<int,str>=Ok(1);[1]}";
    let result = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&result, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
        "{result:?}"
    );
    for source in [
        "type Token(int)\nfn example(){meta let VALUES=(Token(1),[2])}",
        "meta fn qualified()->([]Immut<[]int>,int){([[1]],2)}\nfn example(){meta let VALUES=qualified()}",
    ] {
        let result = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(
                result,
                CompilationOutcome::NotImplemented { .. } | CompilationOutcome::Rejected { .. }
            ),
            "{source}\n{result:?}"
        );
    }
}
