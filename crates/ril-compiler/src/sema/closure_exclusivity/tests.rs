use super::*;
use crate::sema::{
    facts::{LoanId, RootId, ScopeId, Slot},
    model::AccessOwners,
};
use ril_compiler_core::{diagnostic::CauseId, source::FileId};

fn access(node: u32, participant: Participant, write: bool, field: &str) -> AccessFact {
    AccessFact {
        observed_recency: 0,
        recency: 0,
        origin_owners: [(NodeId(node), AccessOwners::Known([ScopeId(0)].into()))].into(),
        origins: Origins::one(NodeId(node)),
        slot: Some(Slot::Field(field.into())),
        mode: if write { Mode::Write } else { Mode::Read },
        participants: [participant].into(),
        cause: CauseId(node),
        span: Span {
            file: FileId(0),
            start: node,
            end: node + 1,
        },
    }
}

#[test]
fn conditional_requirements_match_independent_concrete_storage_conflicts() {
    for partition in 0..27usize {
        let identity = [partition % 3, (partition / 3) % 3, (partition / 9) % 3];
        for fields in 0..8usize {
            let slot = |index| {
                if fields & (1usize << index) == 0 {
                    "value"
                } else {
                    "other"
                }
            };
            let accesses = [
                access(0, Participant::Root(RootId(0)), false, slot(0)),
                access(1, Participant::Loan(LoanId(0)), true, slot(1)),
                access(2, Participant::Loan(LoanId(1)), true, slot(2)),
            ];
            let actual: BTreeSet<_> = requirements(&accesses, |a, b| {
                a.nodes.iter().all(|a| {
                    b.nodes
                        .iter()
                        .all(|b| identity[a.0 as usize] != identity[b.0 as usize])
                })
            })
            .into_iter()
            .map(|requirement| (requirement.left, requirement.right))
            .collect();
            let mut expected = BTreeSet::new();
            for a in 0..3 {
                for b in a + 1..3 {
                    if (identity[a], slot(a)) == (identity[b], slot(b)) {
                        expected.insert((a, b));
                    }
                }
            }
            assert_eq!(actual, expected, "{identity:?}/{fields}");
        }
    }
}

#[test]
fn forwarded_single_loan_is_distinct_from_unproved_independent_participants() {
    let one = Participant::Loan(LoanId(0));
    let shared = [
        access(0, one, true, "value"),
        access(0, one, false, "value"),
    ];
    assert!(requirements(&shared, |_, _| false).is_empty());
    let separate = [
        access(0, one, true, "value"),
        access(1, Participant::Loan(LoanId(1)), false, "value"),
    ];
    assert_eq!(
        requirements(&separate, |_, _| false).len(),
        1,
        "unknown relation is an obligation, never a proof"
    );
}
