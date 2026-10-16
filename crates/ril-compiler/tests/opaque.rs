use ril_compiler::{CompilationOutcome, ProjectSource, Session};

fn project(root: &str, provider: &str) -> CompilationOutcome {
    let directory = std::env::temp_dir().join("ril-opaque-source-contract");
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

#[test]
fn original_opaque_module_corpus_checks_internal_equivalence_and_external_boundaries() {
    let directory = std::env::temp_dir().join("ril-opaque-original-corpus");
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests");
    let mut checked = 0;
    for case in ril_test::discover_cases(&root)
        .unwrap()
        .into_iter()
        .filter(|case| {
            matches!(
                case.id.as_str(),
                "tests/conformance/modules.ril::accept-opaque-unwrapping"
                    | "tests/conformance/modules.ril::reject-opaque-unwrapping"
                    | "tests/integration/modules.ril::opaque-exported-operations"
            )
        })
    {
        let session = Session::with_project(
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
        .unwrap();
        let outcome = session.check();
        if case.meta.mode == ril_test::Mode::CheckFail {
            assert!(
                matches!(&outcome,CompilationOutcome::Rejected {diagnostics} if case.errors.iter().all(|expected|diagnostics.iter().any(|diagnostic|&diagnostic.code==expected))),
                "{}: {outcome:?}",
                case.id
            );
        } else {
            assert!(
                matches!(outcome, CompilationOutcome::Accepted { .. }),
                "{}: {outcome:?}",
                case.id
            );
        }
        checked += 1;
    }
    assert_eq!(checked, 3);
}

#[test]
fn an_exported_opaque_operation_does_not_authorize_external_implicit_conversion() {
    let provider = "pub opaque type Value=int\npub fn make(value:int)->Value{value}\npub fn reveal(value:Value)->int{value}";
    for root in [
        "use token\nfn example(){let raw:int=Token::make(7)}",
        "use token\nfn example(){let value=Token::reveal(7)}",
        "use token\nfn example(){let value:Token::Value=7}",
    ] {
        let outcome = project(root, provider);
        assert!(
            matches!(outcome,CompilationOutcome::Rejected {ref diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
            "{root}: {outcome:?}"
        );
    }
}

#[test]
fn nested_opaque_payload_names_and_readonly_origins_survive_exported_returns() {
    let provider = "pub opaque type Cell={mut count:int}\npub opaque type Holder={child:Cell}\npub fn make()->Holder{.{child:.{count:0}}}\npub fn reveal(value:Holder)->Cell{value.child}";
    for root in [
        "use token\nfn example(){let holder=Token::make();let child=Token::reveal(holder);let raw:{mut count:int}=child}",
        "use token\nfn example(){let holder=Token::make();let child=Token::reveal(holder);let number=child.count}",
    ] {
        assert!(
            !matches!(project(root, provider), CompilationOutcome::Accepted { .. }),
            "nested opaque identity exposed its representation"
        );
    }
}

#[test]
fn opaque_integer_representations_keep_numeric_width_and_scalar_parameter_roles() {
    let provider = "pub opaque type Value=i8\npub fn make()->Value{127}\npub fn reveal(value:Value)->i8{value}";
    let outcome = project(
        "use token\nfn example(){let small:i8=Token::reveal(Token::make());assert(small==127i8)}",
        provider,
    );
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
    for (provider, code) in [
        (
            "pub opaque type Value=i8\npub fn make()->Value{128}",
            "E0326",
        ),
        (
            "pub opaque type Value=i8\npub fn make(value:int)->Value{value}",
            "E0301",
        ),
        (
            "pub opaque type Value=i8\npub fn bad(mut value:Value){}",
            "E0401",
        ),
    ] {
        let outcome = project("use token", provider);
        assert!(
            matches!(outcome,CompilationOutcome::Rejected {ref diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code==code)),
            "{code}: {outcome:?}"
        );
    }
}

#[test]
fn opaque_resources_and_callable_representations_remain_inaccessible_to_clients() {
    let provider =
        "pub opaque type Value=File::Handle\npub fn duplicate(value:Value)->Value{clone(value)}";
    let outcome = project("use token", provider);
    assert!(
        matches!(outcome,CompilationOutcome::Rejected {ref diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0530")),
        "{outcome:?}"
    );
    let provider =
        "pub opaque type Action=fn()->int\nfn action()->int{7}\npub fn make()->Action{action}";
    let outcome = project(
        "use token\nfn example(){let action=Token::make();let value=action()}",
        provider,
    );
    assert!(
        !matches!(outcome, CompilationOutcome::Accepted { .. }),
        "client invoked a hidden callable representation"
    );
}

#[test]
fn a_returned_closure_keeps_its_defining_file_and_seals_its_declared_opaque_result() {
    let provider = "pub opaque type Value=int\npub fn make()->fn()->Value{\\->7}\npub fn reveal(value:Value)->int{value}";
    let outcome = project(
        "use token\nfn example(){let action=Token::make();let value=action();assert(Token::reveal(value)==7)}",
        provider,
    );
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
    let outcome = project(
        "use token\nfn example(){let action=Token::make();let raw:int=action()}",
        provider,
    );
    assert!(
        matches!(outcome,CompilationOutcome::Rejected {ref diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
        "closure exposed its raw result: {outcome:?}"
    );
}

#[test]
fn opacity_does_not_erase_fixed_array_cardinality_or_nested_callable_modes() {
    for provider in [
        "pub opaque type Value=[2]int\npub fn make()->Value{[1]}",
        "pub opaque type Value={run:fn([]int)->()}\npub fn make()->Value{.{run:\\mut values:[]int->{values !> Array::push(1)}}}",
    ] {
        let outcome = project("use token", provider);
        assert!(
            matches!(outcome,CompilationOutcome::Rejected {ref diagnostics} if diagnostics.iter().any(|diagnostic|matches!(diagnostic.code.as_str(),"E0301"|"E0407"))),
            "{provider}: {outcome:?}"
        );
    }
}
