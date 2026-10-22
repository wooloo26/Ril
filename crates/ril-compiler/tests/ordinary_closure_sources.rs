//! Lambda Source types retain their real creator, body and parameter scopes.
use ril_compiler::sema::{SemanticFacts, facts::ScopeId, validate::solved_facts};
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn step_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-observations.ril::closure-captured-step")
}

fn verified(source: &str) -> SemanticFacts {
    let mut facts = None;
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|outcome| panic!("{source}\n{outcome:?}"));
        solved_facts(program.facts()).unwrap();
        ril_compiler::lower::lower_core(&program).unwrap();
        facts = Some(program.facts().clone());
    }
    facts.unwrap()
}

#[test]
fn real_lambda_bodies_and_immutable_generic_locals_supply_complete_source() {
    for source in [
        step_fixture(),
        ril_test::case_source("tests/regressions/source-observations.ril::closure-generic-return"),
        ril_test::case_source(
            "tests/regressions/source-observations.ril::generic-immutable-empty-local",
        ),
        ril_test::case_source(
            "tests/regressions/source-observations.ril::generic-tuple-projection",
        ),
    ] {
        verified(source);
    }
}

#[test]
fn an_open_public_fn_view_does_not_recover_the_original_parameter_view() {
    let source = ril_test::case_source(
        "tests/regressions/source-observations.ril::reject-open-fn-fixed-recovery",
    );
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected {diagnostics}
        if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
        "{source}\n{outcome:?}"
    );
}

#[test]
fn closure_activation_and_formal_owner_cannot_be_deleted_or_borrowed() {
    let facts = verified(step_fixture());
    let probe = facts
        .closure_invocations
        .iter()
        .find(|call| call.probe && call.activation.is_some())
        .unwrap();
    let activation = probe.activation.unwrap();
    let parameter = facts.closures[probe.closure].parameters[0].pattern.span;
    let mut changed = facts.clone();
    changed.closure_invocations[probe.id.0 as usize].activation = None;
    assert!(solved_facts(&changed).is_err());
    let mut changed = facts.clone();
    changed
        .bindings
        .iter_mut()
        .find(|binding| {
            binding.parameter && binding.owner == activation && binding.span == parameter
        })
        .unwrap()
        .owner = ScopeId(0);
    assert!(solved_facts(&changed).is_err());
    let mut changed = facts.clone();
    changed
        .bindings
        .iter_mut()
        .find(|binding| {
            binding.parameter && binding.owner == activation && binding.span == parameter
        })
        .unwrap()
        .context
        .closure_invocation = None;
    assert!(solved_facts(&changed).is_err());
}

#[test]
fn captured_named_headers_keep_their_own_type_selection_at_each_entry() {
    for source in [
        ril_test::case_source(
            "tests/regressions/source-observations.ril::named-generic-captured-header-where",
        ),
        ril_test::case_source(
            "tests/regressions/source-observations.ril::named-generic-distinct-instances-where",
        ),
    ] {
        verified(source);
    }
}

#[test]
fn captured_named_sources_cannot_exchange_creation_environments_or_uid_selections() {
    fn returned_captures(facts: &SemanticFacts) -> std::collections::BTreeMap<usize, &String> {
        use ril_compiler::hir::lexical::{LexicalBindings, TypeNameBinding};
        let hir = facts.semantic_hir.as_deref().unwrap();
        let mut work = 4_000_000;
        let lexical = LexicalBindings::new(hir, &mut work).unwrap();
        facts
            .copy_invocations
            .iter()
            .filter_map(
                |call| match call.result.as_ref()?.value.callables.as_slice() {
                    [ril_compiler::sema::model::Callable::Named(index)] => Some(*index),
                    _ => None,
                },
            )
            .filter_map(|index| {
                let function = &facts.functions[index];
                let header = function.syntax.parameters.first()?.ty.as_ref()?.hir_id?;
                let TypeNameBinding::Generic(generic) =
                    lexical.lookup_type(header, &mut work).unwrap()
                else {
                    return None;
                };
                function
                    .typing_environment
                    .generic_sources
                    .keys()
                    .find(|identity| {
                        let Some(binder) = facts.generic_binders.get(*identity) else {
                            return false;
                        };
                        facts.functions.iter().any(|owner| {
                            owner.definition == binder.definition
                                && owner
                                    .syntax
                                    .generics
                                    .get(binder.index as usize)
                                    .is_some_and(|parameter| parameter.hir_id == Some(generic))
                        })
                    })
                    .map(|identity| (index, identity))
            })
            .collect()
    }

    let facts = verified(ril_test::case_source(
        "tests/regressions/source-observations.ril::named-generic-captured-header-where",
    ));
    let captures = returned_captures(&facts);
    let (index, function, identity) = captures
        .iter()
        .map(|(&index, &identity)| (index, &facts.functions[index], identity))
        .next()
        .unwrap_or_else(|| panic!(
            "the actual returned named function must retain a real creation selection; captures={captures:?}; functions={:?}",
            facts.functions.iter().enumerate().map(|(index, function)| (
                index, &function.syntax.name, function.typing_environment.id(),
                function.typing_environment.generic_context.keys().collect::<Vec<_>>(),
                function.typing_environment.generic_sources.keys().collect::<Vec<_>>()
            )).collect::<Vec<_>>()
        ));
    let original = &facts.generic_binders[identity];
    let unrelated = facts
        .generic_binders
        .iter()
        .find(|(candidate, binder)| {
            *candidate != identity
                && binder.name == original.name
                && binder.definition != original.definition
        })
        .map(|(identity, _)| identity)
        .expect("the corpus contains distinct make<T> and consume<T> declaration UIDs");
    let mut changed = facts.clone();
    let mut environment = function.typing_environment.thaw();
    let selection = environment.generic_sources.remove(identity).unwrap();
    assert!(
        environment
            .generic_sources
            .insert(unrelated.clone(), selection)
            .is_none()
    );
    changed.functions[index].typing_environment = environment.freeze();
    assert!(
        solved_facts(&changed).is_err(),
        "a same-spelled caller UID cannot replace the nested declaration's captured Source coordinate"
    );

    let facts = verified(ril_test::case_source(
        "tests/regressions/source-observations.ril::named-generic-distinct-instances-where",
    ));
    let captures = returned_captures(&facts);
    let (actual, sibling) = captures
        .iter()
        .find_map(|(&actual, &identity)| {
            let function = &facts.functions[actual];
            captures.iter().find_map(|(&sibling, &other_identity)| {
                let other = &facts.functions[sibling];
                (actual != sibling
                    && function.definition == other.definition
                    && identity == other_identity
                    && function.typing_environment.id() != other.typing_environment.id()
                    && function.typing_environment.generic_sources[identity]
                        != other.typing_environment.generic_sources[identity])
                    .then_some((actual, sibling))
            })
        })
        .expect("two actual entries must create the same named declaration with different Sources");
    for (actual, sibling) in [(actual, sibling), (sibling, actual)] {
        let mut changed = facts.clone();
        changed.functions[actual].typing_environment =
            facts.functions[sibling].typing_environment.clone();
        assert!(
            solved_facts(&changed).is_err(),
            "a returned named callable cannot borrow a different entry's frozen Source interpretation"
        );
    }
}

#[test]
fn open_callable_rows_survive_real_product_operands() {
    for source in [
        ril_test::case_source(
            "tests/regressions/source-observations.ril::callable-product-open-row",
        ),
        ril_test::case_source("tests/regressions/record-bounds.ril::scoped-callable-mut"),
    ] {
        verified(source);
    }
}

#[test]
fn a_creation_probe_cannot_be_relabelled_as_an_unrecorded_runtime_call() {
    let facts = verified(step_fixture());
    let probe = facts
        .closure_invocations
        .iter()
        .find(|invocation| {
            invocation.probe
                && facts.closures[invocation.closure]
                    .parameters
                    .iter()
                    .all(|parameter| parameter.ty.is_some())
        })
        .unwrap();
    let mut changed = facts.clone();
    changed.closure_invocations[probe.id.0 as usize].probe = false;
    assert!(solved_facts(&changed).is_err());
}
