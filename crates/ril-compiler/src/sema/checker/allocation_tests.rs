use super::*;

#[test]
fn exhausted_allocation_recording_cannot_authenticate_the_infallible_analysis_result() {
    let mut checker = Checker::new(FileId(0));
    let span = Span {
        file: FileId(0),
        start: 0,
        end: 0,
    };
    let first = checker.allocate_site(span, SiteId(0), ScopeId(0));
    assert!(checker.last_allocation_event(first).is_some());
    assert!(!checker.application_effect.admit(usize::MAX));
    let unproved = checker.allocate_site(span, SiteId(0), ScopeId(0));
    assert_eq!(unproved, first);
    assert!(checker.allocation_poisoned);
    assert_eq!(checker.allocation_events.len(), 1);
    assert!(checker.last_allocation_event(unproved).is_none());
    assert!(
        checker
            .unsupported
            .iter()
            .any(|failure| failure.description.contains("allocation event recording"))
    );
}
