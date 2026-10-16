//! Source-index differential, adversarial and actual Session checks.
use super::*;
use crate::Session;
use crate::sema::copy_templates::InstanceId;
use ril_compiler_core::ids::DefinitionId;

fn facts(source: &str) -> SemanticFacts {
    Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"))
        .facts()
        .clone()
}

fn flags(bounds: Bounds) -> (bool, bool, bool) {
    (bounds.once, bounds.entered, bounds.repeated)
}

fn sole_call(function: &Function) -> &Expr {
    let StmtKind::Expr { expression, .. } = &function.body.as_ref().unwrap().statements[0].kind
    else {
        panic!("expected direct call body")
    };
    assert!(matches!(expression.kind, ExprKind::Call { .. }));
    expression
}

fn sole_call_mut(function: &mut Function) -> &mut Expr {
    let StmtKind::Expr { expression, .. } = &mut function.body.as_mut().unwrap().statements[0].kind
    else {
        panic!("expected direct call body")
    };
    expression
}

#[test]
fn indexed_real_calls_match_the_original_walker_and_keep_loop_bounds() {
    let source = "fn leaf(value:int)->int{value}\nfn example(seed:int=leaf(0)){let callback=\\->{leaf(1)};for [1,2] as value{let mapped=leaf(value)};let _=callback()}";
    let facts = facts(source);
    let mut index = Index::new(&facts);
    let mut reference = super::super::Analysis::new(&facts);
    let mut work = 65_536;
    let mut repeated = false;
    let mut singleton = false;
    for call in &facts.copy_call_events {
        let Some(owner) = call.owner else { continue };
        for (role, call_only) in [(Role::Call, true), (Role::Expression, false)] {
            let expected = reference
                .syntax_walk(Some(owner), call.span, call_only)
                .unwrap();
            let observed = index
                .lookup(Some(owner), call.span, role, &mut work)
                .unwrap();
            assert!(std::ptr::eq(expected.0, observed.0));
            assert_eq!(flags(expected.1), flags(observed.1));
            repeated |= !observed.1.once && observed.1.entered && observed.1.repeated;
            singleton |= observed.1.once && observed.1.entered && !observed.1.repeated;
        }
    }
    assert!(repeated && singleton);
    let closure = facts
        .closures
        .iter()
        .find(|closure| closure.site.is_some())
        .unwrap();
    let lambda = CallableOwner::Lambda(closure.site.unwrap());
    let expected = reference
        .syntax_walk(Some(lambda), closure.body.span, false)
        .unwrap();
    let observed = index
        .lookup(Some(lambda), closure.body.span, Role::Expression, &mut work)
        .unwrap();
    assert!(std::ptr::eq(expected.0, observed.0));
    assert_eq!(flags(expected.1), flags(observed.1));
}

#[test]
fn owner_and_query_role_do_not_borrow_equal_spans() {
    let mut facts = facts(
        "fn leaf(value:int)->int{value}\nfn first()->int{leaf(1)}\nfn second()->int{leaf(2)}",
    );
    let first = facts
        .functions
        .iter()
        .position(|function| function.syntax.name == "first")
        .unwrap();
    let second = facts
        .functions
        .iter()
        .position(|function| function.syntax.name == "second")
        .unwrap();
    let span = sole_call(&facts.functions[first].syntax).span;
    sole_call_mut(&mut facts.functions[second].syntax).span = span;
    let mut index = Index::new(&facts);
    let mut work = 65_536;
    let left = index
        .lookup(
            Some(CallableOwner::Function(facts.functions[first].definition)),
            span,
            Role::Call,
            &mut work,
        )
        .unwrap();
    let right = index
        .lookup(
            Some(CallableOwner::Function(facts.functions[second].definition)),
            span,
            Role::Call,
            &mut work,
        )
        .unwrap();
    assert!(!std::ptr::eq(left.0, right.0));
    assert_ne!(left.0.kind, right.0.kind);

    let ExprKind::Call { callee, .. } = &left.0.kind else {
        unreachable!()
    };
    let owner = Some(CallableOwner::Function(facts.functions[first].definition));
    assert!(
        index
            .lookup(owner, callee.span, Role::Expression, &mut work)
            .is_ok()
    );
    assert!(
        index
            .lookup(owner, callee.span, Role::Call, &mut work)
            .is_err()
    );
    assert!(index.lookup(None, span, Role::Call, &mut work).is_err());
    assert!(
        index
            .lookup(Some(CallableOwner::Global), span, Role::Call, &mut work)
            .is_err()
    );
    assert!(
        index
            .lookup(
                Some(CallableOwner::Function(DefinitionId(u32::MAX))),
                span,
                Role::Call,
                &mut work
            )
            .is_err()
    );
    let mut other_file = span;
    other_file.file.0 += 1;
    assert!(
        index
            .lookup(owner, other_file, Role::Call, &mut work)
            .is_err()
    );
}

#[test]
fn ambiguous_expressions_remain_ambiguous_without_hiding_a_unique_call_role() {
    let mut facts = facts("fn leaf(value:int)->int{value}\nfn caller()->int{leaf(1)}");
    let caller = facts
        .functions
        .iter_mut()
        .find(|function| function.syntax.name == "caller")
        .unwrap();
    let owner = Some(CallableOwner::Function(caller.definition));
    let call = sole_call_mut(&mut caller.syntax);
    let span = call.span;
    let ExprKind::Call { callee, .. } = &mut call.kind else {
        unreachable!()
    };
    callee.span = span;
    let mut index = Index::new(&facts);
    let mut work = 65_536;
    assert!(
        index
            .lookup(owner, span, Role::Expression, &mut work)
            .err()
            .unwrap()
            .contains("ambiguous")
    );
    assert!(index.lookup(owner, span, Role::Call, &mut work).is_ok());

    let mut duplicate = facts.clone();
    let body = duplicate
        .functions
        .iter_mut()
        .find(|function| function.syntax.name == "caller")
        .unwrap()
        .syntax
        .body
        .as_mut()
        .unwrap();
    body.statements.push(body.statements[0].clone());
    let mut index = Index::new(&duplicate);
    assert!(
        index
            .lookup(owner, span, Role::Call, &mut work)
            .err()
            .unwrap()
            .contains("ambiguous")
    );
}

#[test]
fn duplicate_definition_headers_or_bodies_cannot_replace_the_canonical_source() {
    let original = facts("fn leaf(value:int)->int{value}\nfn caller()->int{leaf(1)}");
    let caller = original
        .functions
        .iter()
        .find(|function| function.syntax.name == "caller")
        .unwrap();
    let owner = Some(CallableOwner::Function(caller.definition));
    let span = sole_call(&caller.syntax).span;
    for change_body in [false, true] {
        let mut changed = original.clone();
        let mut duplicate = caller.clone();
        if change_body {
            duplicate.syntax.body.as_mut().unwrap().statements.clear();
        } else {
            duplicate.syntax.name.push_str("_unrelated");
        }
        changed.functions.push(duplicate);
        let mut index = Index::new(&changed);
        let mut work = 65_536;
        assert!(
            index
                .lookup(owner, span, Role::Call, &mut work)
                .err()
                .unwrap()
                .contains("inconsistent duplicate function")
        );
    }
    let mut congruent = original.clone();
    congruent.functions.push(caller.clone());
    let mut index = Index::new(&congruent);
    assert!(index.lookup(owner, span, Role::Call, &mut 65_536).is_ok());
}

#[test]
fn nested_lambda_bodies_and_inconsistent_site_instances_are_not_parent_syntax() {
    let original = facts(
        "fn leaf(value:int)->int{value}\nfn outer(){let callback=\\->{leaf(1)};let _=callback()}",
    );
    let outer = original
        .functions
        .iter()
        .find(|function| function.syntax.name == "outer")
        .unwrap();
    let closure = original
        .closures
        .iter()
        .find(|closure| closure.site.is_some())
        .unwrap();
    let lambda = Some(CallableOwner::Lambda(closure.site.unwrap()));
    let mut index = Index::new(&original);
    let mut work = 65_536;
    assert!(
        index
            .lookup(lambda, closure.body.span, Role::Expression, &mut work)
            .is_ok()
    );
    assert!(
        index
            .lookup(
                Some(CallableOwner::Function(outer.definition)),
                closure.body.span,
                Role::Expression,
                &mut work
            )
            .is_err()
    );
    for change_body in [false, true] {
        let mut changed = original.clone();
        let mut duplicate = closure.clone();
        if change_body {
            duplicate.body.span.end += 1;
        } else {
            duplicate
                .parameters
                .push(original.functions[0].syntax.parameters[0].clone());
        }
        changed.closures.push(duplicate);
        let mut index = Index::new(&changed);
        assert!(
            index
                .lookup(lambda, closure.body.span, Role::Expression, &mut work)
                .err()
                .unwrap()
                .contains("inconsistent duplicate closure")
        );
    }
}

#[test]
fn nested_named_function_body_is_indexed_only_under_its_real_definition() {
    let facts = facts(
        "fn leaf(value:int)->int{value}\nfn outer(){let _=nested() where fn nested()->int{leaf(2)}}",
    );
    let outer = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "outer")
        .unwrap();
    // Static elaboration gives this where declaration a lexical name. Locate
    // its registered definition from the actual enclosing source declaration.
    let StmtKind::Function(declaration) = &outer.syntax.body.as_ref().unwrap().where_items[0].kind
    else {
        panic!("expected a nested where function");
    };
    let nested = facts
        .functions
        .iter()
        .find(|function| {
            function.lexical_owner == Some(CallableOwner::Function(outer.definition))
                && function.syntax == *declaration
        })
        .unwrap();
    assert_ne!(nested.definition, outer.definition);
    let span = sole_call(&nested.syntax).span;
    let mut index = Index::new(&facts);
    let mut work = 65_536;
    assert!(
        index
            .lookup(
                Some(CallableOwner::Function(nested.definition)),
                span,
                Role::Call,
                &mut work,
            )
            .is_ok()
    );
    assert!(
        index
            .lookup(
                Some(CallableOwner::Function(outer.definition)),
                span,
                Role::Call,
                &mut work,
            )
            .is_err()
    );
}

#[test]
fn caller_row_index_preserves_every_actual_id_row_and_its_context() {
    let mut facts = facts("fn leaf(value:int)->int{value}\nfn caller()->int{leaf(1)}");
    let actual = facts
        .invocation_calls
        .iter()
        .find(|row| row.caller_owner.is_some())
        .unwrap()
        .clone();
    let mut altered = actual.clone();
    altered.default_use = None;
    altered.caller_closure = Some(999);
    facts.invocation_calls.push(altered);
    let mut index = Index::new(&facts);
    let mut work = 65_536;
    let indexed = index.caller_links(actual.invocation, &mut work).unwrap();
    let expected = facts
        .invocation_calls
        .iter()
        .filter(|row| row.invocation == actual.invocation)
        .collect::<Vec<_>>();
    assert_eq!(indexed.len(), expected.len());
    assert!(
        indexed
            .iter()
            .zip(expected)
            .all(|(left, right)| std::ptr::eq(*left, right))
    );
    assert!(indexed.iter().any(|row| row.caller_closure == Some(999)));
    assert!(
        index
            .caller_links(InstanceId(u32::MAX), &mut work)
            .unwrap()
            .is_empty()
    );
}

#[test]
fn application_index_never_recovers_an_actual_id_from_its_equal_span() {
    let original = facts("fn leaf(value:int)->int{value}\nfn caller()->int{leaf(1)}");
    let event = original.copy_call_events.first().unwrap();
    let mut work = 65_536;
    let index = Index::new(&original);
    assert!(std::ptr::eq(
        index.application(event.id, &mut work).unwrap(),
        event
    ));
    let mut changed = original.clone();
    changed.copy_call_events[event.id.0 as usize].id = CopyCallEventId(u32::MAX);
    let index = Index::new(&changed);
    assert!(index.application(event.id, &mut work).is_err());
    assert!(
        index
            .application(CopyCallEventId(u32::MAX), &mut work)
            .is_err()
    );
}

#[test]
fn successful_index_reuses_structure_but_every_lookup_still_spends_work() {
    let facts = facts("fn leaf(value:int)->int{value}\nfn caller()->int{leaf(1)}");
    let caller = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "caller")
        .unwrap();
    let owner = Some(CallableOwner::Function(caller.definition));
    let span = sole_call(&caller.syntax).span;
    let mut index = Index::new(&facts);
    let mut work = 65_536;
    let mut reference = super::super::Analysis::new(&facts);
    for _ in 0..100 {
        let observed = index.lookup(owner, span, Role::Call, &mut work).unwrap();
        let expected = reference.syntax_walk(owner, span, true).unwrap();
        assert!(std::ptr::eq(observed.0, expected.0));
    }
    assert!(work > reference.work);
    let before = work;
    index.lookup(owner, span, Role::Call, &mut work).unwrap();
    assert!(work < before);
    assert!(index.lookup(owner, span, Role::Call, &mut 0).is_err());
    let mut incomplete = Index::new(&facts);
    assert!(incomplete.lookup(owner, span, Role::Call, &mut 1).is_err());
    assert!(incomplete.owners.is_empty());
}

#[test]
fn repeated_pure_source_scans_no_longer_reject_the_preserved_split_composition() {
    let source = include_str!(
        "../../tests/fixtures/channel_message_optional_callback_source_index_checked.ril"
    );
    let verified = Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|error| panic!("{error:?}"));
    crate::lower::lower_core(&verified).unwrap();
}

#[test]
fn structural_guard_laws_do_not_authorize_the_preserved_replay_state_gap() {
    let source =
        include_str!("../../tests/fixtures/channel_message_optional_callback_scope_budget.ril");
    match Session::new(source.as_bytes().to_vec()).check() {
        crate::CompilationOutcome::NotImplemented { reason } => {
            assert_eq!(reason.stage, ril_compiler_core::phase::Stage::Provenance);
            assert!(
                // Added complete-evaluation records shift the physical sequence.
                // Keep the same refusal stage and case-bound obligation; do not
                // reinterpret a successful NI regression as language support.
                reason
                    .detail
                    .contains("independent channel replay exceeds its case bound"),
                "{reason:?}"
            );
        }
        other => panic!("original nine-scope program must remain unauthorized: {other:?}"),
    }
}
