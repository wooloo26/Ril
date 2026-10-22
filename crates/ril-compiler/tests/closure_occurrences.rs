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
fn contextual_lambda_preview_keeps_its_original_signature_and_result_check() {
    for layout in ["pointer32", "pointer64"] {
        let facts = verified("contextual-signature-preview", layout);
        assert!(facts.closure_invocations.iter().any(|call| {
            matches!(&call.entry.origin,
                ril_compiler::sema::application_effect::EntryOrigin::SignatureProbe(source)
                if source.header.hir_id == Some(source.source) && source.formals.len() == 1)
        }));
        let call = facts
            .closure_invocations
            .iter()
            .find(|call| {
                matches!(
                    call.entry.origin,
                    ril_compiler::sema::application_effect::EntryOrigin::SignatureProbe(_)
                )
            })
            .unwrap();
        let closure = &facts.closures[call.closure];
        assert!(
            closure.parameters[0].ty.is_none(),
            "context never invents a written lambda parameter"
        );
        assert!(
            closure.contract.return_type.is_none(),
            "context never invents a written lambda result"
        );
        let (binding, info) = facts
            .bindings
            .iter()
            .enumerate()
            .find(|(_, info)| {
                info.parameter
                    && Some(info.owner) == call.activation
                    && info.pattern == closure.parameters[0].pattern.hir_id
            })
            .unwrap();
        assert!(facts.source_types.binding_type(binding).is_some());
        assert_eq!(
            info.typing_environment.id(),
            closure.contract.typing_environment.id()
        );
        for mutation in 0..3 {
            let mut changed = facts.clone();
            match mutation {
                0 => changed.source_types = Default::default(),
                1 => {
                    changed.source_types = Default::default();
                    changed.bindings[binding].pattern = None;
                }
                2 => {
                    changed.bindings[binding].typing_environment =
                        info.typing_environment.thaw().freeze()
                }
                _ => unreachable!(),
            }
            assert!(
                solved_facts(&changed).is_err(),
                "inferred parameter Source mutation {mutation}"
            );
        }
        for case in [
            "contextual-signature-result-mismatch",
            "contextual-signature-closure-argument-mismatch",
        ] {
            let source = ril_test::case_source(&format!(
                "tests/regressions/closure-occurrences.ril::{case}"
            ));
            let outcome = Session::with_options(
                source.as_bytes().to_vec(),
                CheckOptions {
                    target: layout.into(),
                    ..Default::default()
                },
            )
            .check();
            assert!(
                matches!(&outcome, ril_compiler::CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
                "{case} {layout}: {outcome:?}"
            );
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
