use ril_compiler::{CompilationOutcome, ProjectSource, Session};

fn project(root: &str, provider: &str) -> CompilationOutcome {
    let directory = std::env::temp_dir().join("ril-callable-return-origin-oracles");
    Session::with_project(
        directory.join("root.ril"),
        vec![
            ProjectSource {
                path: directory.join("root.ril"),
                bytes: root.as_bytes().to_vec(),
            },
            ProjectSource {
                path: directory.join("token.ril"),
                bytes: provider.as_bytes().to_vec(),
            },
        ],
        Default::default(),
    )
    .unwrap()
    .check()
}

fn has_type_error(outcome: &CompilationOutcome) -> bool {
    matches!(outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301"))
}

#[test]
fn repeated_client_ascriptions_preserve_the_producers_opaque_result() {
    let provider = "pub opaque type Value=int\npub fn make()->fn()->Value{\\->7}\npub fn reveal(value:Value)->int{value}";
    for aliases in [
        "let first:fn()->Token::Value=action;let second=first",
        "let first:fn()->Token::Value=action;let second:fn()->Token::Value=first",
    ] {
        let root = format!(
            "use token\nfn example(){{let action=Token::make();{aliases};assert(Token::reveal(second())==7)}}"
        );
        let outcome = project(&root, provider);
        assert!(
            matches!(outcome, CompilationOutcome::Accepted { .. }),
            "sequential ascriptions consume the producer's sealed result: {root}: {outcome:?}"
        );
        let root = format!(
            "use token\nfn example(){{let action=Token::make();{aliases};let raw:int=second()}}"
        );
        let outcome = project(&root, provider);
        assert!(
            has_type_error(&outcome),
            "a later client ascription cannot expose the producer's raw representation: {root}: {outcome:?}"
        );
    }
}

#[test]
fn a_raw_alias_branch_cannot_borrow_another_branchs_opaque_result_contract() {
    let provider = "pub opaque type Value=int\npub let RAW=\\->7\npub fn sealed()->(fn()->Value) &{RAW}{RAW}\npub fn reveal(value:Value)->int{value}";
    let root = "use token\nfn example() &{Token::RAW}{assert(Token::reveal(Token::sealed()())==7);assert(Token::RAW()==7)}";
    let outcome = project(root, provider);
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "the same callable descriptor supports each actual exported contract independently: {outcome:?}"
    );
    for branches in [
        "if flag{Token::sealed()}else{Token::RAW}",
        "if flag{Token::RAW}else{Token::sealed()}",
    ] {
        let root = format!(
            "use token\nfn example(flag:bool) &{{Token::RAW}}{{let selected={branches};let value=selected();assert(Token::reveal(value)==7)}}"
        );
        let outcome = project(&root, provider);
        assert!(
            matches!(outcome, CompilationOutcome::Rejected { ref diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0351")),
            "a possible raw invocation cannot use another value's opaque sealing stage: {root}: {outcome:?}"
        );
    }
}
