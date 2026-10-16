use super::*;
#[test]
fn finite_event_oracle_checks_last_unit_and_the_outermost_exhausted_owner() {
    for outer in 1..5 {
        for inner in 1..5 {
            let mut state = Allowances::default();
            let parent = state.begin(outer, Handle(11)).unwrap();
            assert_eq!(state.charge(BudgetEvent::BudgetEntry), Decision::Execute);
            let child = state.begin(inner, Handle(22)).unwrap();
            let allowed = (outer - 1).min(inner);
            for _ in 0..allowed {
                assert_eq!(state.charge(BudgetEvent::FunctionEntry), Decision::Execute);
            }
            let Decision::Exhaust(exhaustion) = state.charge(BudgetEvent::Resume) else {
                panic!("finite event trace must exhaust");
            };
            if outer - 1 <= inner {
                assert_eq!(exhaustion.owner, parent);
                assert_eq!(exhaustion.boundary, Handle(11));
                assert_eq!(exhaustion.abandoned.len(), 2);
            } else {
                assert_eq!(exhaustion.owner, child);
                assert_eq!(exhaustion.boundary, Handle(22));
                assert_eq!(exhaustion.abandoned.len(), 1);
                state.finish(parent).unwrap();
            }
        }
    }
}
#[test]
fn cleanup_suspends_existing_owners_but_new_boundaries_still_charge() {
    let mut state = Allowances::default();
    let parent = state.begin(0, Handle(1)).unwrap();
    let mask = state.suspend_for_cleanup();
    assert!(!state.is_active());
    for _ in 0..10 {
        assert_eq!(state.charge(BudgetEvent::LoopIteration), Decision::Execute);
    }
    let child = state.begin(1, Handle(2)).unwrap();
    assert_eq!(state.charge(BudgetEvent::FunctionEntry), Decision::Execute);
    let nested = state.suspend_for_cleanup();
    assert_eq!(state.charge(BudgetEvent::HandlerEntry), Decision::Execute);
    state.restore_after_cleanup(nested);
    let Decision::Exhaust(exhaustion) = state.charge(BudgetEvent::LoopIteration) else {
        panic!("cleanup-local boundary is active");
    };
    assert_eq!(exhaustion.owner, child);
    state.restore_after_cleanup(mask);
    let Decision::Exhaust(exhaustion) = state.charge(BudgetEvent::HandlerEntry) else {
        panic!("outer boundary resumes");
    };
    assert_eq!(exhaustion.owner, parent);
}
#[test]
fn zero_inner_exhaustion_does_not_spend_or_replenish_a_surviving_outer_allowance() {
    let mut state = Allowances::default();
    let parent = state.begin(1, Handle(1)).unwrap();
    assert_eq!(state.charge(BudgetEvent::BudgetEntry), Decision::Execute);
    let child = state.begin(0, Handle(2)).unwrap();
    let exhausted = state.exhaust_zero(child).unwrap();
    assert_eq!(exhausted.owner, child);
    let Decision::Exhaust(exhaustion) = state.charge(BudgetEvent::HandlerEntry) else {
        panic!("outer last unit was already consumed");
    };
    assert_eq!(exhaustion.owner, parent);
}
