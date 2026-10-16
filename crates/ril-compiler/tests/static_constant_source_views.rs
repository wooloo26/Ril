use ril_compiler::{CheckOptions, CompilationOutcome, Session};

#[test]
fn shared_constant_nodes_keep_distinct_declared_source_views() {
    let source = "meta let FIXED:[2]int=[1,2]\nmeta let WEAK:[]int=FIXED\nfn example() &{FIXED,WEAK}{assert(FIXED==WEAK)}";
    for target in ["pointer32", "pointer64"] {
        let verified = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|outcome| panic!("{target}: {outcome:?}"));
        let binding = |name: &str| {
            &verified
                .facts()
                .bindings
                .iter()
                .find(|binding| binding.name == name)
                .unwrap()
                .value
        };
        let fixed = binding("FIXED");
        let weak = binding("WEAK");
        assert_eq!(
            fixed.origins, weak.origins,
            "a type view must not clone storage"
        );
        assert_ne!(fixed.source_type_witness, weak.source_type_witness);
        assert!(fixed.source_type_witness.is_some() && weak.source_type_witness.is_some());
        ril_compiler::lower::lower_core(&verified).unwrap();
    }
}

#[test]
fn an_evaluated_dynamic_alias_cannot_recover_a_fixed_source_from_shared_storage() {
    for target in ["pointer32", "pointer64"] {
        let source = "meta let FIXED:[2]int=[1,2]\nmeta let WEAK:[]int=FIXED\nfn bad() &{WEAK}{let recovered:[2]int=WEAK}";
        let outcome = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
            "{target}: {outcome:?}"
        );
    }
}

#[test]
fn empty_evaluated_graphs_keep_their_written_nested_element_dimensions() {
    for target in ["pointer32", "pointer64"] {
        let source =
            "meta let ORIGINAL:[0][3]int=[]\nfn bad() &{ORIGINAL}{let changed:[0][2]int=ORIGINAL}";
        let outcome = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
            "{target}: {outcome:?}"
        );
    }
}
