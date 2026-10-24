use ril_compiler::{CheckOptions, CompilationOutcome, Session};

#[test]
fn ordered_spreads_and_static_materialization_share_the_record_shape() {
    for case in [
        "tests/conformance/records.ril::accept-conflicting-spreads",
        "tests/conformance/records.ril::ordered-record-members-pointer64",
        "tests/conformance/records.ril::abrupt-record-members-pointer64",
        "tests/conformance/records.ril::static-record-members-pointer64",
    ] {
        for layout in ["pointer32", "pointer64"] {
            let program = Session::with_options(
                ril_test::case_bytes(case).to_vec(),
                CheckOptions {
                    target: layout.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|outcome| panic!("{case} {layout}: {outcome:?}"));
            ril_compiler::lower::lower_core(&program).unwrap();
        }
    }
}

#[test]
fn static_record_members_consume_exactly_their_actual_function_entries() {
    let case = "tests/conformance/records.ril::static-record-members-pointer64";
    for layout in ["pointer32", "pointer64"] {
        for (limit, accepted) in [(7, true), (6, false)] {
            let outcome = Session::with_options(
                ril_test::case_bytes(case).to_vec(),
                CheckOptions {
                    target: layout.into(),
                    static_budget: std::num::NonZeroU64::new(limit).unwrap(),
                    ..Default::default()
                },
            )
            .check();
            if accepted {
                assert!(
                    matches!(outcome, CompilationOutcome::Accepted { .. }),
                    "{layout} {limit}: {outcome:?}"
                );
            } else {
                assert!(
                    matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                    if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0811")),
                    "{layout} {limit}: {outcome:?}"
                );
            }
        }
    }
}

#[test]
fn canonical_records_still_reject_unresolved_spread_conflicts() {
    let case = "tests/conformance/records.ril::reject-conflicting-spreads";
    for layout in ["pointer32", "pointer64"] {
        let outcome = Session::with_options(
            ril_test::case_bytes(case).to_vec(),
            CheckOptions {
                target: layout.into(),
                ..Default::default()
            },
        )
        .check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0211")),
            "{layout}: {outcome:?}"
        );
    }
}
