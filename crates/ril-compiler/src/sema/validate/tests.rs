use super::*;
use crate::Session;

const PARALLEL: &str = "use ril/parallel\ntype Cell={mut value:int,mut other:int}\nfn cell()->Cell{Cell.{value:0,other:0}}\nfn example(){for [0,1] as index{let mut shared=cell();let _=Parallel::join(\\->{shared.value+=1},\\->{let unused=cell();shared.other+=1})}}";

fn facts(source: &str) -> SemanticFacts {
    Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap()
        .facts()
        .clone()
}
fn access(facts: &mut SemanticFacts) -> &mut AccessFact {
    facts
        .parallel_boundaries
        .iter_mut()
        .flat_map(|boundary| &mut boundary.callbacks)
        .flat_map(|callback| &mut callback.accesses)
        .find(|access| !access.origins.nodes.is_empty())
        .unwrap()
}
fn fails(facts: &SemanticFacts, expected: impl Fn(&ValidationIssueKind) -> bool) {
    let errors = solved_facts(facts).expect_err("damaged structure was accepted");
    assert!(
        errors.iter().any(|issue| expected(&issue.kind)),
        "{errors:#?}"
    );
}

#[test]
fn ordinary_verified_sources_calibrate_the_independent_structure_checker() {
    for source in [
        "fn example(){assert(1==1)}",
        "type Cell={mut value:int}\nfn example(){let mut cell=Cell.{value:0};cell.value+=1;assert(cell.value==1)}",
        "fn read()->Result<int,str>{Ok(1)}\nfn example(){let result=read();assert(result is Ok(1))}",
        "fn example(flag:bool){let first=[1];let second=[2];let pair=if flag{(first,second)}else{(second,first)};assert(pair.0[0]>0)}",
        PARALLEL,
        "use ril/parallel\neff Read{get()->int}\nfn example(){let callback={with Read::get()->resume 7;\\n:int->Read::get()+n};assert(Parallel::map([1,2],callback)==[8,9])}",
        "use ril/concurrent\nfn example()->Result<int,Concurrent::TaskFault> @Concurrent{Concurrent::scope \\mut scope->{let task=scope.fork(\\->7);task.join()}}",
    ] {
        let facts = facts(source);
        assert!(
            solved_facts(&facts).is_ok(),
            "{source}\n{:#?}",
            solved_facts(&facts)
        );
    }
}

#[test]
fn access_epoch_origin_coverage_and_owner_material_are_not_optional() {
    let original = facts(PARALLEL);
    assert!(
        solved_facts(&original).is_ok(),
        "{:#?}",
        solved_facts(&original)
    );
    assert!(!original.allocation_history.is_empty());
    let mut damaged = original.clone();
    access(&mut damaged).recency = 0;
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::AccessEpoch { .. })
    });
    let mut damaged = original.clone();
    access(&mut damaged).observed_recency = usize::MAX;
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::AccessEpoch { .. })
    });
    let mut damaged = original.clone();
    access(&mut damaged).origin_owners.clear();
    fails(&damaged, |kind| {
        *kind == ValidationIssueKind::OwnershipCoverage
    });
    let mut damaged = original.clone();
    *access(&mut damaged)
        .origin_owners
        .values_mut()
        .next()
        .unwrap() = AccessOwners::Known(BTreeSet::new());
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::EmptyKnownOwnership(_))
    });
    let mut damaged = original.clone();
    *access(&mut damaged)
        .origin_owners
        .values_mut()
        .next()
        .unwrap() = AccessOwners::Known([ScopeId(999_999)].into());
    fails(&damaged, |kind| {
        *kind == ValidationIssueKind::InvalidScope(ScopeId(999_999))
    });
    let mut damaged = original.clone();
    access(&mut damaged)
        .origins
        .choices
        .insert(0, vec![BTreeSet::new(), BTreeSet::new()]);
    fails(&damaged, |kind| {
        *kind == ValidationIssueKind::OriginCoverage
    });
    let mut explicit_unknown = original;
    *access(&mut explicit_unknown)
        .origin_owners
        .values_mut()
        .next()
        .unwrap() = AccessOwners::Unknown;
    assert!(
        solved_facts(&explicit_unknown).is_ok(),
        "Unknown is explicit structure, never a locality proof"
    );
}

#[test]
fn damaged_graph_roots_loans_causes_and_history_are_rejected_without_panics() {
    let original = facts(PARALLEL);
    let mut damaged = original.clone();
    let node = access(&mut damaged).origins.nodes.first().copied().unwrap();
    damaged.heap.nodes[node.0 as usize]
        .writable_roots
        .insert(super::super::facts::RootId(u32::MAX));
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::InvalidRoot(_))
    });
    let mut damaged = original.clone();
    access(&mut damaged)
        .participants
        .insert(Participant::Loan(super::super::facts::LoanId(u32::MAX)));
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::InvalidLoan(_))
    });
    let mut damaged = original.clone();
    damaged.bindings[0].root = super::super::facts::RootId(1);
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::InvalidRoot(_))
    });
    let mut damaged = original.clone();
    access(&mut damaged).cause = CauseId(u32::MAX);
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::InvalidCause(_))
    });
    let mut damaged = original.clone();
    damaged.allocation_history[0].1 = damaged.allocation_history[0].0;
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::InvalidAllocationMove(_))
    });
    let mut damaged = original.clone();
    let key = damaged.fields.keys().next().unwrap().clone();
    damaged.heap.nodes[key.0.0 as usize].fields.remove(&key.1);
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::FieldGraphMismatch(..))
    });
    let mut damaged = original;
    access(&mut damaged).origins.nodes.insert(NodeId(u32::MAX));
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::InvalidOrigin(_))
    });
}

#[test]
fn boundary_and_scope_references_are_checked_against_independent_registries() {
    let original = facts(PARALLEL);
    let mut damaged = original.clone();
    damaged.allocated_scopes.remove(&ScopeId(0));
    fails(&damaged, |kind| {
        *kind == ValidationIssueKind::MissingGlobalScope
    });
    let mut damaged = original.clone();
    damaged.scope_parents.insert(ScopeId(1), ScopeId(1));
    fails(&damaged, |kind| {
        *kind == ValidationIssueKind::ScopeCycle(ScopeId(1))
    });
    let mut damaged = original.clone();
    damaged.parallel_boundaries[0].callbacks[0]
        .selected_handlers
        .insert(usize::MAX);
    fails(&damaged, |kind| {
        *kind == ValidationIssueKind::InvalidHandler(usize::MAX)
    });
    let mut damaged = original.clone();
    damaged.parallel_boundaries[0].callbacks[0]
        .termination
        .unresolved = true;
    fails(&damaged, |kind| {
        *kind == ValidationIssueKind::IncompleteParallelTermination
    });
    let mut damaged = original.clone();
    damaged.parallel_boundaries[0].callbacks.clear();
    fails(&damaged, |kind| {
        *kind == ValidationIssueKind::MissingBoundaryEvidence
    });
    let mut damaged = original.clone();
    let cause = damaged.parallel_boundaries[0].cause;
    damaged.explanations.causes[cause.0 as usize]
        .parents
        .clear();
    fails(&damaged, |kind| {
        *kind == ValidationIssueKind::BoundaryCauseMismatch
    });
    let mut damaged = original;
    let span = damaged.parallel_boundaries[0].span;
    damaged
        .concurrent_boundaries
        .push(super::super::ConcurrentBoundary {
            span,
            scope: NodeId(u32::MAX),
            task: Some(NodeId(u32::MAX - 1)),
            kind: super::super::ConcurrentBoundaryKind::Fork,
            cause: CauseId(0),
        });
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::InvalidOrigin(_))
    });
}

#[test]
fn formal_scope_sentinels_and_relation_material_cannot_bypass_the_structure_checks() {
    let original = facts(PARALLEL);
    let mut damaged = original.clone();
    let node = damaged
        .heap
        .nodes
        .iter()
        .position(|node| matches!(node.kind, OriginKind::Fresh(_)))
        .unwrap();
    damaged.heap.nodes[node].owner = ScopeId(u32::MAX);
    fails(&damaged, |kind| {
        *kind == ValidationIssueKind::InvalidScope(ScopeId(u32::MAX))
    });
    let mut damaged = original.clone();
    damaged.allocated_scopes.insert(ScopeId(u32::MAX));
    fails(&damaged, |kind| {
        *kind == ValidationIssueKind::InvalidScope(ScopeId(u32::MAX))
    });
    let mut damaged = original.clone();
    damaged.heap.set_relation(
        NodeId(0),
        NodeId(1),
        super::super::relations::Relation {
            equal: Condition::TRUE,
            disjoint: Condition::TRUE,
        },
    );
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::ContradictoryRelation(..))
    });
    let mut damaged = original.clone();
    damaged.heap.set_relation(
        NodeId(0),
        NodeId(1),
        super::super::relations::Relation {
            equal: Condition(u32::MAX),
            disjoint: Condition::FALSE,
        },
    );
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::InvalidCondition(_))
    });
    let mut damaged = original.clone();
    damaged.heap.conditions.atom(Atom::equal(
        super::super::relations::Pivot(u32::MAX),
        super::super::relations::Pivot(u32::MAX - 1),
    ));
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::InvalidPivot(_))
    });
    let mut damaged = original;
    let loan = *damaged.loan_parents.keys().next().unwrap();
    damaged
        .loan_parents
        .insert(loan, [Participant::Loan(loan)].into());
    fails(&damaged, |kind| {
        *kind == ValidationIssueKind::LoanCycle(loan.0)
    });
}

#[test]
fn existing_resource_result_and_collection_programs_keep_valid_structure() {
    for source in [
        ril_test::case_source("tests/regressions/channels.ril::nested-result-channel"),
        ril_test::case_source("tests/regressions/copy.ril::private-helpers"),
        "type Node={mut value:int,mut following:?Node}\nfn example(){let mut original=Node.{value:1,following:None};original.following=Some(^mut original);let mut copied=^mut clone(original);copied.value+=1;assert(original.value==1)}",
        "fn repeat(values:[]int)->[][]int{var current=[[1],[2]];for values as index{current=clone(current)};current}\nfn example(){assert(repeat([1,2])==[[1],[2]])}",
    ] {
        let facts = facts(source);
        assert!(
            solved_facts(&facts).is_ok(),
            "{source}\n{:#?}",
            solved_facts(&facts)
        );
    }
}

#[test]
fn result_producer_identity_and_creation_scope_survive_current_owner_transfer() {
    let original = facts(
        "fn make()->Result<int,str>{Ok(1)}\nfn example(){let result=make();assert(result is Ok(1))}",
    );
    let selected = original
        .result_duties
        .iter()
        .position(|duty| duty.creation_owner != duty.owner)
        .unwrap();
    assert!(solved_facts(&original).is_ok());
    let mut damaged = original.clone();
    damaged.result_duties[selected].creation_owner = ScopeId(999_999);
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::InvalidScope(ScopeId(999_999)))
    });
    let mut damaged = original.clone();
    damaged.result_duties[selected].id = u32::MAX;
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::InvalidResultProducer(u32::MAX))
    });
    let mut damaged = original;
    damaged.result_duties.clear();
    fails(&damaged, |kind| {
        matches!(kind, ValidationIssueKind::InvalidResultProducer(_))
    });
}
