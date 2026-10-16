use ril_compiler::{CompilationOutcome, Session};

#[test]
fn invalid_array_length_sorts_and_scoped_modes_keep_the_specified_diagnostics() {
    for (source, code) in [
        ("fn example(){let items:[\"0\"]int=[]}", "E0323"),
        ("fn example(){let items:[.{size:1}]int=[]}", "E0323"),
        ("fn example(){let items:[[1]]int=[]}", "E0323"),
        (
            "type Guard={on_close:fn()->()}\nfn example(){var scoped item=Guard.{on_close:\\->()}}",
            "E0532",
        ),
        (
            "type Guard={on_close:fn()->()}\nfn example(){var mut scoped item=Guard.{on_close:\\->()}}",
            "E0532",
        ),
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome, CompilationOutcome::Rejected { ref diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
            "{source}: {outcome:?}"
        );
    }
}

#[test]
fn original_length_and_resource_diagnostic_corpus_cases_keep_their_expected_codes() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests");
    let mut checked = 0;
    for case in ril_test::discover_cases(&root)
        .unwrap()
        .into_iter()
        .filter(|case| {
            matches!(
                case.id.as_str(),
                "tests/conformance/collections.ril::reject-length-sort"
                    | "tests/conformance/cleanup.ril::reject-reassignable-scoped"
            )
        })
    {
        let source = case
            .files
            .iter()
            .find(|file| file.name == case.root)
            .unwrap();
        let outcome = Session::new(source.bytes.clone()).check();
        assert!(
            matches!(outcome, CompilationOutcome::Rejected { ref diagnostics } if case.errors.iter().all(|expected| diagnostics.iter().any(|diagnostic| &diagnostic.code == expected))),
            "{}: {outcome:?}",
            case.id
        );
        checked += 1;
    }
    assert_eq!(checked, 2);
}
