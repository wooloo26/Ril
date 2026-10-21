use ril_compiler::{
    CheckOptions, Session,
    sema::{SemanticFacts, validate::solved_facts},
};
use ril_compiler_core::ids::{CallableOwner, ClosureSiteId, ExprId};

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
            core.provenance
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
            solved_facts(&facts).unwrap();
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

#[test]
fn deleting_or_substituting_site_identity_never_erases_a_closure_obligation() {
    let facts = verified("two-written", "pointer64");
    assert!(facts.closure_sites.len() >= 2);
    for mutation in 0..9 {
        let mut changed = facts.clone();
        match mutation {
            0 => changed.closure_sites.clear(),
            1 => changed.closure_sites[0].source = changed.closure_sites[1].source,
            2 => changed.closure_sites[0].source = ExprId(u32::MAX),
            3 => changed.closure_sites[0].owner = CallableOwner::Lambda(ClosureSiteId(0)),
            4 => changed.closures[0].hir_id = changed.closures[1].hir_id,
            5 => changed.closures[0].site = None,
            6 => {
                changed.closure_sites.clear();
                changed.closures.clear();
                for expression in &mut changed.expressions {
                    expression.value.callables.clear();
                }
            }
            7 => changed.closure_sites[1].id = changed.closure_sites[0].id,
            8 => {
                changed.closures.clear();
                for expression in &mut changed.expressions {
                    expression.value.callables.clear();
                }
            }
            _ => unreachable!(),
        }
        assert!(
            solved_facts(&changed).is_err(),
            "closure site mutation {mutation}"
        );
    }
}
