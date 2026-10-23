//! Small identity models exercise corruption independently of language checks.
use super::*;
use crate::sema::{
    WindowInfo,
    copy_contract::{CopyHeapSnapshot, CopyNode},
    evaluated::EvaluatedValue,
    facts::Permission,
    model::{Origins, Ty, Value},
};
use ril_compiler_core::source::{FileId, Span};
use std::sync::Arc;

fn allocate(facts: &mut SemanticFacts, site: SiteId, owner: ScopeId) -> AllocationEventId {
    let cause = facts
        .explanations
        .add(CauseKind::Allocation, None, "actual allocation", []);
    let epoch_before = facts.allocation_history.len();
    let (recent, remap) = facts
        .heap
        .fresh_in_scopes(site, owner, cause, &facts.scopes);
    let id = AllocationEventId(facts.allocation_events.len() as u32);
    facts.allocation_events.push(AllocationEvent {
        id,
        site,
        recent,
        remap,
        epoch_before,
        cause,
        owner,
        anchor: None,
        position: 0,
    });
    if let Some(remap) = remap {
        facts.allocation_history.push(remap);
    }
    id
}

fn creation(
    facts: &mut SemanticFacts,
    allocation: AllocationEventId,
    root: PatternId,
    rest: PatternId,
) {
    let event = &facts.allocation_events[allocation.0 as usize];
    let epoch = event.epoch_after();
    let cause = facts.explanations.add(
        CauseKind::Projection,
        None,
        "window selection",
        [event.cause],
    );
    let mut value = Value::reference(
        Ty::Array(Box::new(Ty::Int("int".into()))),
        event.recent,
        cause,
    );
    value.permission = Permission::Read;
    value.construction = false;
    let input = Value::scalar(Ty::Unit, None, event.cause);
    facts.pattern_windows.push(PatternWindowCreation {
        allocation,
        root,
        rest,
        anchor: None,
        context: crate::sema::effect_identity::InvocationContext {
            invocation: None,
            owner: None,
            closure: None,
            closure_invocation: None,
            budget_validation: false,
            default_use: None,
        },
        owner: event.owner,
        input: Arc::new(EvaluatedValue::new(input, epoch)),
        heap: Arc::new(CopyHeapSnapshot {
            allocation_epoch: epoch,
            nodes: vec![],
            relations: vec![],
        }),
        parents: vec![],
        prefix: 0,
        suffix: 0,
        output: Arc::new(EvaluatedValue::new(value, epoch)),
        output_node: CopyNode {
            origin: event.recent,
            fact: facts.heap.nodes[event.recent.0 as usize].clone(),
            fields: vec![],
            length: Some(Some(0)),
            fixed: false,
        },
        info: WindowInfo {
            pattern: Some(rest),
            constant: None,
            backing: Origins::default(),
            lower: Some(0),
            length: Some(0),
            span: Span {
                file: FileId(0),
                start: 0,
                end: 0,
            },
            cause,
        },
    });
}

fn fixture() -> SemanticFacts {
    let mut parsed = ril_syntax::parse(ril_test::case_source(
        "tests/conformance/rest-patterns.ril::array-rest-lengths-pointer64",
    ));
    assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
    let hir = crate::hir::HirProgram::lower_identified(
        &mut parsed.program,
        crate::hir::nodes::InputOrigin::Source,
    )
    .unwrap();
    let mut selected = None;
    hir.walk(1_000_000, |node, _| {
        if let crate::hir::nodes::NodeId::Pattern(root) = node
            && let crate::hir::nodes::PatternKind::Array(items) = &hir.pattern(root).unwrap().kind
            && let Some(rest) = items.iter().find(|rest| {
                matches!(
                    hir.pattern(**rest).map(|node| &node.kind),
                    Some(crate::hir::nodes::PatternKind::Rest(Some(_)))
                )
            })
        {
            selected.get_or_insert((root, *rest));
        }
    })
    .unwrap();
    let (root, rest) = selected.expect("corpus includes an original named array rest");
    let mut facts = SemanticFacts {
        semantic_hir: Some(Arc::new(hir)),
        ..Default::default()
    };
    facts.scopes.insert(ScopeId(0));
    allocate(&mut facts, SiteId(9), ScopeId(0));
    let first = allocate(&mut facts, SiteId(4), ScopeId(0));
    creation(&mut facts, first, root, rest);
    let second = allocate(&mut facts, SiteId(4), ScopeId(0));
    creation(&mut facts, second, root, rest);
    facts.pattern_window_sites.push(PatternWindowSite {
        rest,
        loop_owner: ScopeId(0),
        site: SiteId(4),
    });
    facts
}

#[test]
fn reused_recent_identity_keeps_each_historical_birth_cause() {
    let facts = fixture();
    validate(&facts, &mut 1_000_000).unwrap();
    let first = &facts.pattern_windows[0];
    let recent = first.output_node.origin;
    assert_ne!(
        first.output_node.fact.cause,
        facts.heap.nodes[recent.0 as usize].cause
    );

    let mut changed = facts.clone();
    // This is a real, earlier, parentless Allocation cause. The previous
    // final-node check could not authenticate it after raw recent reuse.
    changed.pattern_windows[0].output_node.fact.cause = facts.allocation_events[0].cause;
    assert!(
        validate(&changed, &mut 1_000_000)
            .unwrap_err()
            .contains("another allocation birth")
    );

    let mut later_storage = facts.clone();
    later_storage.heap.nodes[recent.0 as usize].fields.clear();
    validate(&later_storage, &mut 1_000_000).unwrap();
}

#[test]
fn allocation_ledger_rejects_missing_reordered_and_reassigned_births() {
    let facts = fixture();
    for mutation in 0..7 {
        let mut changed = facts.clone();
        match mutation {
            0 => {
                changed.allocation_events.remove(1);
            }
            1 => {
                changed.allocation_events.swap(1, 2);
                for (id, event) in changed.allocation_events.iter_mut().enumerate() {
                    event.id = AllocationEventId(id as u32);
                }
            }
            2 => changed.allocation_events[2].cause = changed.allocation_events[0].cause,
            3 => changed.allocation_events[2].remap = None,
            4 => {
                changed.allocation_history.clear();
            }
            5 => changed.heap.nodes[0].kind = OriginKind::Fresh(SiteId(999)),
            _ => changed.allocation_poisoned = true,
        }
        assert!(
            validate(&changed, &mut 1_000_000).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn window_allocation_roles_and_receipts_are_unique_original_edges() {
    let facts = fixture();
    for mutation in 0..6 {
        let mut changed = facts.clone();
        match mutation {
            0 => changed.pattern_window_sites[0].rest = changed.pattern_windows[0].root,
            1 => {
                changed.pattern_window_sites.clear();
            }
            2 => changed
                .pattern_window_sites
                .push(changed.pattern_window_sites[0]),
            3 => changed.pattern_window_sites[0].site = SiteId(9),
            4 => changed
                .pattern_windows
                .push(changed.pattern_windows[0].clone()),
            _ => {
                changed.pattern_windows.remove(0);
            }
        }
        assert!(
            validate(&changed, &mut 1_000_000).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn allocation_replay_charges_before_growing_or_walking_its_domain() {
    let facts = fixture();
    let mut remaining = 1_000_000;
    validate(&facts, &mut remaining).unwrap();
    let exact = 1_000_000 - remaining;
    validate(&facts, &mut { exact }).unwrap();
    let mut short = exact - 1;
    assert!(validate(&facts, &mut short).is_err());
    assert_eq!(short, 0);
    assert!(window_event(&facts, &facts.pattern_windows[0], &mut 0).is_err());
}

#[test]
fn unrelated_scope_roots_merge_to_the_same_module_owner_as_the_heap() {
    let mut facts = SemanticFacts::default();
    for id in [0, 10, 11] {
        facts.scopes.insert(ScopeId(id));
    }
    allocate(&mut facts, SiteId(0), ScopeId(10));
    allocate(&mut facts, SiteId(0), ScopeId(11));
    allocate(&mut facts, SiteId(0), ScopeId(11));
    let older = facts.allocation_history[0].1;
    assert_eq!(facts.heap.nodes[older.0 as usize].owner, ScopeId(0));
    validate(&facts, &mut 1_000_000).unwrap();
    let mut changed = facts.clone();
    changed.heap.nodes[older.0 as usize].owner = ScopeId(10);
    assert!(validate(&changed, &mut 1_000_000).is_err());
}

fn local_activation(facts: &mut SemanticFacts) -> ActivationEpochId {
    use crate::sema::application_effect::{ActivationKind, EvaluationActivation};
    let id = ActivationEpochId(facts.activations.len() as u32);
    facts.scopes.insert(ScopeId(10));
    let context = crate::sema::effect_identity::InvocationContext {
        invocation: None,
        owner: None,
        closure: None,
        closure_invocation: None,
        budget_validation: false,
        default_use: None,
    };
    facts.activations.push(EvaluationActivation {
        id,
        parent: None,
        kind: ActivationKind::Emission,
        source: None,
        scope: ScopeId(10),
        context,
        start_expression: 0,
        end_expression: Some(1),
        result: Some(ril_compiler_core::ids::EvaluationOccurrenceId(0)),
    });
    facts.expressions.push(crate::sema::ExpressionFact {
        source_id: None,
        allocation_epoch: 0,
        span: Span {
            file: FileId(0),
            start: 0,
            end: 0,
        },
        value: crate::sema::PhysicalValue::unobserved_fixture(
            Value::scalar(Ty::Unit, None, facts.allocation_events[0].cause),
            0,
        ),
    });
    id
}

#[test]
fn module_owned_allocations_keep_their_real_local_execution_activation() {
    let mut facts = SemanticFacts::default();
    facts.scopes.insert(ScopeId(0));
    allocate(&mut facts, SiteId(0), ScopeId(0));
    let anchor = local_activation(&mut facts);
    facts.allocation_events[0].anchor = Some(anchor);
    assert!(!within(&facts, ScopeId(0), ScopeId(10), &mut 1_000).unwrap());
    validate(&facts, &mut 1_000_000).unwrap();
    let mut changed = facts.clone();
    changed.activations[0].scope = ScopeId(u32::MAX);
    assert!(validate(&changed, &mut 1_000_000).is_err());
    let mut changed = facts.clone();
    changed.allocation_events[0].position = 1;
    assert!(validate(&changed, &mut 1_000_000).is_err());

    // A window has a stronger receiving-frame obligation than the generic
    // allocation ledger. Admitting module catalog allocations cannot relax it.
    let mut windows = fixture();
    let anchor = local_activation(&mut windows);
    windows.allocation_events[1].anchor = Some(anchor);
    windows.pattern_windows[0].anchor = Some(anchor);
    assert!(
        validate(&windows, &mut 1_000_000)
            .unwrap_err()
            .contains("receiving frame")
    );
}
