use super::*;
use ril_compiler_core::ids::OptionalTagId;

#[test]
fn structural_equality_keeps_each_sort_and_every_physical_field() {
    let atoms = [
        GuardLiteral::Boolean {
            evaluation: ConditionEvaluationId(0),
            truth: false,
        },
        GuardLiteral::Boolean {
            evaluation: ConditionEvaluationId(1),
            truth: false,
        },
        GuardLiteral::Boolean {
            evaluation: ConditionEvaluationId(0),
            truth: true,
        },
        GuardLiteral::Optional {
            identity: OptionalTagId(0),
            present: false,
        },
        GuardLiteral::Optional {
            identity: OptionalTagId(1),
            present: false,
        },
        GuardLiteral::Optional {
            identity: OptionalTagId(0),
            present: true,
        },
        GuardLiteral::Result {
            producer: 0,
            version: 0,
            success: false,
        },
        GuardLiteral::Result {
            producer: 1,
            version: 0,
            success: false,
        },
        GuardLiteral::Result {
            producer: 0,
            version: 1,
            success: false,
        },
        GuardLiteral::Result {
            producer: 0,
            version: 0,
            success: true,
        },
        GuardLiteral::Transport {
            event: ChannelMessageId(0),
            producer: 0,
            version: 0,
            success: false,
        },
        GuardLiteral::Transport {
            event: ChannelMessageId(1),
            producer: 0,
            version: 0,
            success: false,
        },
        GuardLiteral::Transport {
            event: ChannelMessageId(0),
            producer: 1,
            version: 0,
            success: false,
        },
        GuardLiteral::Transport {
            event: ChannelMessageId(0),
            producer: 0,
            version: 1,
            success: false,
        },
        GuardLiteral::Transport {
            event: ChannelMessageId(0),
            producer: 0,
            version: 0,
            success: true,
        },
    ];
    for (left_index, left) in atoms.into_iter().enumerate() {
        let left = ChannelGuard::literal(left);
        for (right_index, right) in atoms.into_iter().enumerate() {
            let right = ChannelGuard::literal(right);
            let mut work = 0;
            assert_eq!(
                left.same_structure(&right, &mut work),
                Some(left_index == right_index)
            );
            assert_eq!(work, 3);
        }
    }
    let mut unavailable = ChannelGuard::always();
    unavailable.incomplete = true;
    assert_eq!(
        ChannelGuard::always().same_structure(&unavailable, &mut 0),
        Some(false)
    );
}

#[test]
fn largest_bounded_structure_comparison_is_linear_and_cannot_reset_work() {
    let guard = ChannelGuard {
        terms: (0..MAX_GUARD_TERMS)
            .map(|clause| {
                (0..MAX_GUARD_LITERALS)
                    .map(|literal| GuardLiteral::Boolean {
                        evaluation: ConditionEvaluationId(
                            (clause * MAX_GUARD_LITERALS + literal) as u32,
                        ),
                        truth: true,
                    })
                    .collect()
            })
            .collect(),
        incomplete: false,
    };
    assert!(guard.bounded());
    let cost = 1 + MAX_GUARD_TERMS + MAX_GUARD_TERMS * MAX_GUARD_LITERALS;
    assert_eq!(cost, 33_025);
    let mut work = 0;
    assert_eq!(guard.same_structure(&guard, &mut work), Some(true));
    assert_eq!(work, cost);
    let mut exact_remaining = MAX_GUARD_WORK - cost;
    assert_eq!(
        guard.same_structure(&guard, &mut exact_remaining),
        Some(true)
    );
    assert_eq!(exact_remaining, MAX_GUARD_WORK);
    let mut insufficient = MAX_GUARD_WORK - cost + 1;
    assert_eq!(guard.same_structure(&guard, &mut insufficient), None);
    assert!(insufficient > MAX_GUARD_WORK);
}

#[test]
fn raw_subset_comparison_requires_the_complete_physical_clause() {
    let original = GuardLiteral::Transport {
        event: ChannelMessageId(17),
        producer: 17,
        version: 0,
        success: false,
    };
    for changed in [
        GuardLiteral::Transport {
            event: ChannelMessageId(17),
            producer: 18,
            version: 0,
            success: false,
        },
        GuardLiteral::Transport {
            event: ChannelMessageId(17),
            producer: 17,
            version: 1,
            success: false,
        },
        GuardLiteral::Transport {
            event: ChannelMessageId(18),
            producer: 17,
            version: 0,
            success: false,
        },
        GuardLiteral::Result {
            producer: 17,
            version: 0,
            success: false,
        },
        GuardLiteral::Optional {
            identity: OptionalTagId(17),
            present: false,
        },
        GuardLiteral::Boolean {
            evaluation: ConditionEvaluationId(17),
            truth: false,
        },
    ] {
        let smaller = ChannelGuard::literal(original);
        let larger = ChannelGuard {
            terms: [
                [changed].into(),
                [GuardLiteral::Boolean {
                    evaluation: ConditionEvaluationId(999),
                    truth: true,
                }]
                .into(),
            ]
            .into(),
            incomplete: false,
        };
        assert_eq!(
            smaller.raw_clauses_contained_in(&larger, &mut 0),
            Some(false)
        );
    }
}

#[test]
fn ordered_raw_subset_lookup_debits_the_existing_counter() {
    let literal = |evaluation| GuardLiteral::Boolean {
        evaluation: ConditionEvaluationId(evaluation),
        truth: false,
    };
    let smaller = ChannelGuard::literal(literal(1));
    let larger = ChannelGuard {
        terms: [[literal(0)].into(), [literal(1)].into()].into(),
        incomplete: false,
    };
    let mut work = 0;
    assert_eq!(
        smaller.raw_clauses_contained_in(&larger, &mut work),
        Some(true)
    );
    assert_eq!(work, 7);
    let mut exact = MAX_GUARD_WORK - 7;
    assert_eq!(
        smaller.raw_clauses_contained_in(&larger, &mut exact),
        Some(true)
    );
    assert_eq!(exact, MAX_GUARD_WORK);
    let mut insufficient = MAX_GUARD_WORK - 6;
    assert_eq!(
        smaller.raw_clauses_contained_in(&larger, &mut insufficient),
        None
    );
    assert!(insufficient > MAX_GUARD_WORK);
}

#[test]
fn term_subsumption_requires_the_same_physical_literal_and_complete_inputs() {
    let original = GuardLiteral::Transport {
        event: ChannelMessageId(17),
        producer: 17,
        version: 0,
        success: false,
    };
    let extra = GuardLiteral::Boolean {
        evaluation: ConditionEvaluationId(999),
        truth: true,
    };
    let selected = ChannelGuard {
        terms: [[original, extra].into()].into(),
        incomplete: false,
    };
    assert_eq!(
        selected.terms_physically_imply(&ChannelGuard::literal(original), &mut 0),
        Some(true)
    );
    for changed in [
        GuardLiteral::Transport {
            event: ChannelMessageId(17),
            producer: 18,
            version: 0,
            success: false,
        },
        GuardLiteral::Transport {
            event: ChannelMessageId(17),
            producer: 17,
            version: 1,
            success: false,
        },
        GuardLiteral::Result {
            producer: 17,
            version: 0,
            success: false,
        },
        GuardLiteral::Optional {
            identity: OptionalTagId(17),
            present: false,
        },
        GuardLiteral::Boolean {
            evaluation: ConditionEvaluationId(17),
            truth: false,
        },
    ] {
        assert_eq!(
            selected.terms_physically_imply(&ChannelGuard::literal(changed), &mut 0),
            Some(false)
        );
    }
    assert_eq!(
        selected.terms_physically_imply(&ChannelGuard::unavailable(), &mut 0),
        Some(false)
    );
}

#[test]
fn every_term_and_witness_visit_uses_the_existing_remaining_budget() {
    let original = GuardLiteral::Result {
        producer: 17,
        version: 0,
        success: false,
    };
    let extra = GuardLiteral::Boolean {
        evaluation: ConditionEvaluationId(999),
        truth: true,
    };
    let selected = ChannelGuard {
        terms: [[original, extra].into()].into(),
        incomplete: false,
    };
    let witness = ChannelGuard::literal(original);
    let mut work = 0;
    assert_eq!(
        selected.terms_physically_imply(&witness, &mut work),
        Some(true)
    );
    assert_eq!(work, 6); // header + term + witness + both literal counts.
    let mut exact = MAX_GUARD_WORK - 6;
    assert_eq!(
        selected.terms_physically_imply(&witness, &mut exact),
        Some(true)
    );
    assert_eq!(exact, MAX_GUARD_WORK);
    let mut insufficient = MAX_GUARD_WORK - 5;
    assert_eq!(
        selected.terms_physically_imply(&witness, &mut insufficient),
        None
    );
    assert!(insufficient > MAX_GUARD_WORK);
}
