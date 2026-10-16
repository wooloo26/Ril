use ril_compiler::{AnalysisStatus, CompilationOutcome, Session};

fn source(name: &str) -> &'static [u8] {
    ril_test::case_bytes(&format!("tests/regressions/analysis.ril::{name}"))
}

#[test]
fn successful_analysis_and_verification_share_the_same_immutable_facts_and_hir() {
    let snapshot = Session::new(source("constant-answer").to_vec()).analyze();
    assert_eq!(
        snapshot.status(),
        AnalysisStatus::Verified,
        "{:?}",
        snapshot.outcome()
    );
    let facts = std::ptr::from_ref(snapshot.facts().unwrap());
    let hir = std::ptr::from_ref(snapshot.checked_hir().unwrap());
    let verified = snapshot.into_verified().unwrap();
    assert_eq!(facts, std::ptr::from_ref(verified.facts()));
    assert_eq!(hir, std::ptr::from_ref(verified.semantic_hir()));
    ril_compiler::lower::lower_core(&verified).unwrap();
}

#[test]
fn semantic_errors_keep_observations_without_issuing_verification() {
    let snapshot = Session::new(source("readonly-reassignment").to_vec()).analyze();
    assert_eq!(snapshot.status(), AnalysisStatus::Rejected);
    assert!(
        snapshot
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "E0501")
    );
    assert!(!snapshot.facts().unwrap().expressions.is_empty());
    assert!(snapshot.hir().unwrap().node_count() > 0);
    assert!(matches!(
        snapshot.into_verified(),
        Err(CompilationOutcome::Rejected { .. })
    ));
}

#[test]
fn recovery_syntax_and_invalid_encoding_do_not_fabricate_semantic_facts() {
    let snapshot = Session::new(source("reserved-keyword-recovery").to_vec()).analyze();
    assert_eq!(snapshot.status(), AnalysisStatus::Rejected);
    assert!(snapshot.source().is_some());
    assert!(snapshot.hir().is_some());
    assert!(snapshot.facts().is_none());
    let invalid = Session::new(vec![0xff]).analyze();
    assert_eq!(invalid.status(), AnalysisStatus::Rejected);
    assert!(invalid.facts().is_none() && invalid.source().is_none());
    assert_eq!(invalid.diagnostics()[0].code, "E0104");
}

#[test]
fn incomplete_analysis_keeps_its_unpaid_obligations() {
    let snapshot = Session::new(source("fixed-input-pipeline").to_vec()).analyze();
    assert!(snapshot.hir().is_some() && snapshot.facts().is_some());
    match snapshot.status() {
        AnalysisStatus::Incomplete => {
            assert!(!snapshot.unresolved().is_empty());
            assert!(matches!(
                snapshot.into_verified(),
                Err(CompilationOutcome::NotImplemented { .. })
            ));
        }
        AnalysisStatus::Verified => {
            // A later implementation may solve the genuine pipeline obligation.
            // The accepted source still has to cross the ordinary lowering gate.
            ril_compiler::lower::lower_core(&snapshot.into_verified().unwrap()).unwrap();
        }
        status => panic!("unexpected {status:?}: {:?}", snapshot.outcome()),
    }
}

#[test]
fn old_snapshots_survive_edits_and_match_fresh_analysis() {
    let mut session = Session::new(source("constant-answer").to_vec());
    let before = session.analyze();
    let count = before.hir().unwrap().node_count();
    session.update(source("readonly-reassignment").to_vec());
    let after = session.analyze();
    let fresh = Session::new(source("readonly-reassignment").to_vec()).analyze();
    assert_eq!(before.status(), AnalysisStatus::Verified);
    assert_eq!(before.hir().unwrap().node_count(), count);
    assert_eq!(after.status(), fresh.status());
    assert_eq!(
        after
            .diagnostics()
            .iter()
            .map(|diagnostic| &diagnostic.code)
            .collect::<Vec<_>>(),
        fresh
            .diagnostics()
            .iter()
            .map(|diagnostic| &diagnostic.code)
            .collect::<Vec<_>>()
    );
    assert_eq!(
        after.hir().unwrap().node_count(),
        fresh.hir().unwrap().node_count()
    );
}
