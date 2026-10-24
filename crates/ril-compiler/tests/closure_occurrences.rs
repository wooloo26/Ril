use ril_compiler::{CheckOptions, Session, sema::SemanticFacts};

fn verified(name: &str, layout: &str) -> SemanticFacts {
    let source = ril_test::case_source(&format!(
        "tests/regressions/closure-occurrences.ril::{name}"
    ));
    let program = Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: layout.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap_or_else(|error| panic!("{name} {layout}: {error:?}"));
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    for site in &program.facts().closure_sites {
        assert!(
            core.metadata
                .closure_sites
                .iter()
                .any(|lowered| lowered.id == site.id && lowered.source == site.source)
        );
    }
    program.facts().clone()
}

#[test]
fn static_sites_and_dynamic_objects_keep_their_original_hir_sources() {
    for layout in ["pointer32", "pointer64"] {
        for name in [
            "two-written",
            "repeated-default",
            "factory-with-handlers",
            "named-default-block",
            "default-capture",
            "default-capture-through-call",
        ] {
            let facts = verified(name, layout);
            for object in &facts.closures {
                let site = &facts.closure_sites[object.site.unwrap().0 as usize];
                assert_eq!(object.hir_id, Some(site.source));
            }
            if name == "repeated-default" {
                assert!(facts.closure_sites.iter().any(|site| {
                    facts
                        .closures
                        .iter()
                        .filter(|object| object.site == Some(site.id))
                        .count()
                        > 1
                }));
            }
        }
    }
}
