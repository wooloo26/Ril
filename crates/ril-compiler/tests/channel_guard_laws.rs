//! Truth-table oracle for guard algebra, independent of message transfer rules.
use ril_compiler::sema::{
    channel_messages::{
        ChannelGuard, ChannelMessageId, GuardLiteral, MAX_GUARD_LITERALS, MAX_GUARD_TERMS,
    },
    result_conditions::ConditionEvaluationId,
};
use std::collections::BTreeSet;

fn sampled_inactive_guard() -> ChannelGuard {
    // Exact physical literals from the frozen v15 observation, not new IDs
    // chosen to stand in for the original Source's event or producer facts.
    let transport = [
        (260, 40),
        (265, 41),
        (300, 46),
        (305, 47),
        (342, 52),
        (384, 58),
        (389, 59),
        (425, 64),
        (430, 65),
        (466, 70),
    ];
    let booleans = [
        28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52,
        53, 55, 57,
    ];
    ChannelGuard {
        terms: transport
            .into_iter()
            .map(|(event, producer)| GuardLiteral::Transport {
                event: ChannelMessageId(event),
                producer,
                version: 0,
                success: false,
            })
            .chain(
                booleans
                    .into_iter()
                    .map(|evaluation| GuardLiteral::Boolean {
                        evaluation: ConditionEvaluationId(evaluation),
                        truth: false,
                    }),
            )
            .map(|literal| [literal].into())
            .collect(),
        incomplete: false,
    }
}

#[test]
fn the_actual_record657_inactive_guard_is_preserved_by_exact_idempotence() {
    let original = sampled_inactive_guard();
    assert_eq!(original.terms.len(), 36);
    assert_eq!(original.and(&original), Some(original.clone()));
    let event_guard = original.not().unwrap();
    assert_eq!(event_guard.terms.len(), 1);
    let complement = event_guard.not().unwrap();
    assert_eq!(complement, original);
    let inactive = original.and(&complement).unwrap();
    assert_eq!(inactive, original);
    assert!(!inactive.is_never());
    assert_eq!(
        inactive
            .terms
            .iter()
            .flatten()
            .filter(|literal| matches!(literal, GuardLiteral::Transport { success: false, .. }))
            .count(),
        10
    );
    // No executed membership or custody fact is supplied by this algebra law.
}

#[test]
fn the_actual_record661_raw_clause_subset_preserves_the_whole_inactive_case() {
    let original = sampled_inactive_guard();
    let mut complement = original.clone();
    complement.terms.insert(
        [GuardLiteral::Result {
            producer: 74,
            version: 0,
            success: true,
        }]
        .into(),
    );
    assert_eq!(complement.terms.len(), 37);
    assert_eq!(original.and(&complement), Some(original.clone()));
    assert_eq!(complement.and(&original), Some(original.clone()));
    assert!(!original.is_never());
    // The extra Result tag is not an inspection and cannot turn the original
    // negative unexecuted transport alternatives into an empty continuation.
}

#[test]
fn raw_clause_subset_absorption_preserves_all_four_physical_sorts() {
    use ril_compiler_core::ids::OptionalTagId;
    let atoms = [
        GuardLiteral::Optional {
            identity: OptionalTagId(17),
            present: false,
        },
        GuardLiteral::Result {
            producer: 17,
            version: 0,
            success: false,
        },
        GuardLiteral::Transport {
            event: ChannelMessageId(17),
            producer: 17,
            version: 0,
            success: false,
        },
        GuardLiteral::Boolean {
            evaluation: ConditionEvaluationId(17),
            truth: false,
        },
    ];
    let original = ChannelGuard {
        terms: atoms.into_iter().map(|atom| [atom].into()).collect(),
        incomplete: false,
    };
    let mut larger = original.clone();
    larger.terms.insert(
        [GuardLiteral::Result {
            producer: 17,
            version: 1,
            success: true,
        }]
        .into(),
    );
    assert_eq!(original.and(&larger), Some(original.clone()));
    assert_eq!(larger.and(&original), Some(original));
}

#[test]
fn raw_clause_subset_still_normalizes_and_refuses_exhausted_or_incomplete_inputs() {
    let boolean = |evaluation, truth| GuardLiteral::Boolean {
        evaluation: ConditionEvaluationId(evaluation),
        truth,
    };
    let x = boolean(0, true);
    let smaller = ChannelGuard {
        terms: [
            [x].into(),
            [x, boolean(1, true)].into(),
            [boolean(2, true), boolean(2, false)].into(),
        ]
        .into(),
        incomplete: false,
    };
    let mut larger = smaller.clone();
    larger.terms.insert([boolean(3, true)].into());
    assert_eq!(smaller.and(&larger), Some(ChannelGuard::literal(x)));
    larger.incomplete = true;
    assert!(smaller.and(&larger).is_none());

    let expensive = ChannelGuard {
        terms: (0..200)
            .map(|evaluation| [boolean(evaluation, true)].into())
            .collect(),
        incomplete: false,
    };
    let mut larger = expensive.clone();
    larger.terms.insert([boolean(200, true)].into());
    assert!(expensive.and(&larger).is_none());
    assert!(larger.and(&expensive).is_none());
}

#[test]
fn same_logical_transport_key_cannot_fake_a_raw_clause_subset() {
    let original = GuardLiteral::Transport {
        event: ChannelMessageId(17),
        producer: 17,
        version: 0,
        success: false,
    };
    let changed = GuardLiteral::Transport {
        event: ChannelMessageId(17),
        producer: 18,
        version: 0,
        success: false,
    };
    let unrelated = GuardLiteral::Boolean {
        evaluation: ConditionEvaluationId(999),
        truth: true,
    };
    let larger = ChannelGuard {
        terms: [[changed].into(), [unrelated].into()].into(),
        incomplete: false,
    };
    let result = ChannelGuard::literal(original).and(&larger).unwrap();
    assert_eq!(
        result.terms,
        [[original, changed].into(), [original, unrelated].into()].into()
    );
}

#[test]
fn the_actual_record858_term_witnesses_preserve_all_original_physical_clauses() {
    use ril_compiler_core::ids::OptionalTagId;
    let mut common = sampled_inactive_guard()
        .not()
        .unwrap()
        .terms
        .into_iter()
        .next()
        .unwrap();
    for identity in [16, 22] {
        common.insert(GuardLiteral::Optional {
            identity: OptionalTagId(identity),
            present: true,
        });
    }
    let mut original = ChannelGuard::never();
    for first in [false, true] {
        for second in [false, true] {
            for evaluation in [63, 64] {
                let mut term = common.clone();
                term.insert(GuardLiteral::Transport {
                    event: ChannelMessageId(347),
                    producer: 53,
                    version: 0,
                    success: first,
                });
                term.insert(GuardLiteral::Transport {
                    event: ChannelMessageId(471),
                    producer: 71,
                    version: 0,
                    success: second,
                });
                term.insert(GuardLiteral::Boolean {
                    evaluation: ConditionEvaluationId(evaluation),
                    truth: false,
                });
                if first {
                    term.insert(GuardLiteral::Optional {
                        identity: OptionalTagId(17),
                        present: false,
                    });
                }
                if second {
                    term.insert(GuardLiteral::Optional {
                        identity: OptionalTagId(23),
                        present: false,
                    });
                }
                original.terms.insert(term);
            }
        }
    }
    let mut complement = sampled_inactive_guard();
    for (event, producer) in [(548, 82), (553, 83), (630, 94), (635, 95)] {
        complement.terms.insert(
            [GuardLiteral::Transport {
                event: ChannelMessageId(event),
                producer,
                version: 0,
                success: false,
            }]
            .into(),
        );
    }
    for evaluation in [63, 64, 65, 66, 67, 73, 74, 75] {
        complement.terms.insert(
            [GuardLiteral::Boolean {
                evaluation: ConditionEvaluationId(evaluation),
                truth: false,
            }]
            .into(),
        );
    }
    assert_eq!(original.terms.len(), 8);
    assert_eq!(
        original.terms.iter().map(|term| term.len()).sum::<usize>(),
        336
    );
    assert_eq!(complement.terms.len(), 48);
    assert!(original.terms.is_disjoint(&complement.terms));
    assert_eq!(original.normalized(), Some(original.clone()));
    assert_eq!(original.and(&complement), Some(original.clone()));
    assert_eq!(complement.and(&original), Some(original));
}

#[test]
fn physical_term_subsumption_is_symmetric_and_keeps_every_atom_sort() {
    use ril_compiler_core::ids::OptionalTagId;
    let atoms = [
        GuardLiteral::Optional {
            identity: OptionalTagId(17),
            present: false,
        },
        GuardLiteral::Result {
            producer: 17,
            version: 0,
            success: false,
        },
        GuardLiteral::Transport {
            event: ChannelMessageId(17),
            producer: 17,
            version: 0,
            success: false,
        },
        GuardLiteral::Boolean {
            evaluation: ConditionEvaluationId(17),
            truth: false,
        },
    ];
    for atom in atoms {
        let selected = ChannelGuard {
            terms: [
                [
                    atom,
                    GuardLiteral::Boolean {
                        evaluation: ConditionEvaluationId(999),
                        truth: false,
                    },
                ]
                .into(),
                [
                    atom,
                    GuardLiteral::Boolean {
                        evaluation: ConditionEvaluationId(1000),
                        truth: true,
                    },
                ]
                .into(),
            ]
            .into(),
            incomplete: false,
        };
        let weaker = ChannelGuard::literal(atom);
        assert_eq!(selected.and(&weaker), selected.normalized());
        assert_eq!(weaker.and(&selected), selected.normalized());
    }
}

#[test]
fn witnessed_terms_cannot_skip_normalization_work_or_unknown_inputs() {
    let common = GuardLiteral::Optional {
        identity: ril_compiler_core::ids::OptionalTagId(17),
        present: true,
    };
    let selected = ChannelGuard {
        terms: (0..200)
            .map(|evaluation| {
                [
                    common,
                    GuardLiteral::Boolean {
                        evaluation: ConditionEvaluationId(evaluation),
                        truth: true,
                    },
                ]
                .into()
            })
            .collect(),
        incomplete: false,
    };
    let weaker = ChannelGuard::literal(common);
    assert!(selected.normalized().is_none());
    assert!(selected.and(&weaker).is_none());
    assert!(weaker.and(&selected).is_none());
    assert!(selected.and(&ChannelGuard::unavailable()).is_none());
}

#[test]
fn equal_raw_guards_cannot_skip_normalization_or_its_work_limit() {
    let x = GuardLiteral::Boolean {
        evaluation: ConditionEvaluationId(0),
        truth: true,
    };
    let y = GuardLiteral::Boolean {
        evaluation: ConditionEvaluationId(1),
        truth: true,
    };
    let opposite = GuardLiteral::Boolean {
        evaluation: ConditionEvaluationId(1),
        truth: false,
    };
    let raw = ChannelGuard {
        terms: [[x].into(), [x, y].into(), [y, opposite].into()].into(),
        incomplete: false,
    };
    assert_eq!(raw.and(&raw), Some(ChannelGuard::literal(x)));

    let expensive = ChannelGuard {
        terms: (0..200)
            .map(|evaluation| {
                [GuardLiteral::Boolean {
                    evaluation: ConditionEvaluationId(evaluation),
                    truth: true,
                }]
                .into()
            })
            .collect(),
        incomplete: false,
    };
    assert!(expensive.normalized().is_none());
    assert!(expensive.and(&expensive).is_none());
}

#[test]
fn idempotence_never_bypasses_incomplete_or_shape_bounds() {
    let unavailable = ChannelGuard::unavailable();
    assert!(unavailable.and(&unavailable).is_none());
    assert!(ChannelGuard::never().and(&unavailable).is_none());
    let too_many_terms = ChannelGuard {
        terms: (0..=MAX_GUARD_TERMS)
            .map(|evaluation| {
                [GuardLiteral::Boolean {
                    evaluation: ConditionEvaluationId(evaluation as u32),
                    truth: true,
                }]
                .into()
            })
            .collect(),
        incomplete: false,
    };
    assert!(too_many_terms.and(&too_many_terms).is_none());
    let too_many_literals = ChannelGuard {
        terms: [(0..=MAX_GUARD_LITERALS)
            .map(|evaluation| GuardLiteral::Boolean {
                evaluation: ConditionEvaluationId(evaluation as u32),
                truth: true,
            })
            .collect()]
        .into(),
        incomplete: false,
    };
    assert!(too_many_literals.and(&too_many_literals).is_none());
}

#[test]
fn different_physical_fields_are_not_structural_idempotence() {
    use ril_compiler_core::ids::OptionalTagId;
    let transport = |producer, version| GuardLiteral::Transport {
        event: ChannelMessageId(17),
        producer,
        version,
        success: true,
    };
    // The algebra must retain conflicting transport metadata so that the
    // independent metadata validator can reject it, rather than erase it as
    // though a matching logical event key meant equal physical evidence.
    for (left, right) in [
        (transport(17, 0), transport(18, 0)),
        (transport(17, 0), transport(17, 1)),
        (
            GuardLiteral::Result {
                producer: 17,
                version: 0,
                success: true,
            },
            GuardLiteral::Result {
                producer: 17,
                version: 1,
                success: true,
            },
        ),
        (
            GuardLiteral::Optional {
                identity: OptionalTagId(17),
                present: true,
            },
            GuardLiteral::Optional {
                identity: OptionalTagId(18),
                present: true,
            },
        ),
        (
            GuardLiteral::Boolean {
                evaluation: ConditionEvaluationId(17),
                truth: true,
            },
            GuardLiteral::Boolean {
                evaluation: ConditionEvaluationId(18),
                truth: true,
            },
        ),
        (
            transport(17, 0),
            GuardLiteral::Result {
                producer: 17,
                version: 0,
                success: true,
            },
        ),
    ] {
        let conjunction = ChannelGuard::literal(left)
            .and(&ChannelGuard::literal(right))
            .unwrap();
        assert_eq!(conjunction.terms, [[left, right].into()].into());
    }
}

fn literal(variable: u32, truth: bool) -> GuardLiteral {
    if variable == 2 {
        GuardLiteral::Boolean {
            evaluation: ConditionEvaluationId(0),
            truth,
        }
    } else {
        GuardLiteral::Transport {
            event: ChannelMessageId(variable),
            producer: variable + 10,
            version: 3,
            success: truth,
        }
    }
}

fn formula(mask: u8) -> ChannelGuard {
    ChannelGuard {
        terms: (0..8_u8)
            .filter(|assignment| mask & (1 << assignment) != 0)
            .map(|assignment| {
                (0..3)
                    .map(|variable| literal(variable, assignment & (1 << variable) != 0))
                    .collect()
            })
            .collect(),
        incomplete: false,
    }
}

fn evaluate(guard: &ChannelGuard, assignment: u8) -> bool {
    assert!(
        !guard.incomplete,
        "an incomplete guard has no exact truth table"
    );
    guard.terms.iter().any(|term| {
        term.iter().all(|literal| {
            let (variable, expected) = match literal {
                GuardLiteral::Transport { event, success, .. } => (event.0, *success),
                GuardLiteral::Boolean { evaluation, truth } => {
                    assert_eq!(evaluation.0, 0);
                    (2, *truth)
                }
                GuardLiteral::Result { .. } => panic!("Result guard has its own version oracle"),
                GuardLiteral::Optional { .. } => {
                    panic!("Optional guard has its own presence oracle")
                }
            };
            (assignment & (1 << variable) != 0) == expected
        })
    })
}

#[test]
fn physical_result_tags_keep_generations_distinct_without_inspection_authority() {
    let tag = |version, success| {
        ChannelGuard::literal(GuardLiteral::Result {
            producer: 17,
            version,
            success,
        })
    };
    assert!(tag(3, true).and(&tag(3, false)).unwrap().is_never());
    assert_eq!(
        tag(3, true).or(&tag(3, false)).unwrap(),
        ChannelGuard::always()
    );
    assert!(!tag(3, true).and(&tag(4, false)).unwrap().is_never());
    assert!(
        !tag(3, true)
            .and(&ChannelGuard::literal(literal(0, false)))
            .unwrap()
            .is_never()
    );
}

#[test]
fn result_versions_and_transport_events_preserve_every_three_variable_truth_table() {
    let variable = |index: u32, truth| {
        if index == 2 {
            GuardLiteral::Transport {
                event: ChannelMessageId(17),
                producer: 17,
                version: 3,
                success: truth,
            }
        } else {
            GuardLiteral::Result {
                producer: 17,
                version: index + 3,
                success: truth,
            }
        }
    };
    let evaluate = |guard: &ChannelGuard, assignment: u8| {
        assert!(!guard.incomplete);
        guard.terms.iter().any(|term| {
            term.iter().all(|literal| {
                let (index, expected) = match literal {
                    GuardLiteral::Result {
                        producer: 17,
                        version,
                        success,
                    } => {
                        assert!(matches!(version, 3 | 4));
                        (version - 3, *success)
                    }
                    GuardLiteral::Transport {
                        event: ChannelMessageId(17),
                        success,
                        ..
                    } => (2, *success),
                    _ => panic!("unexpected variable in the independent truth table"),
                };
                (assignment & (1 << index) != 0) == expected
            })
        })
    };
    for mask in 0..=u8::MAX {
        let formula = ChannelGuard {
            terms: (0..8_u8)
                .filter(|assignment| mask & (1 << assignment) != 0)
                .map(|assignment| {
                    (0..3)
                        .map(|index| variable(index, assignment & (1 << index) != 0))
                        .collect()
                })
                .collect(),
            incomplete: false,
        };
        let normalized = formula.normalized().unwrap();
        let complement = normalized.not().unwrap();
        for assignment in 0..8 {
            let truth = mask & (1 << assignment) != 0;
            assert_eq!(evaluate(&normalized, assignment), truth);
            assert_eq!(evaluate(&complement, assignment), !truth);
        }
        let union = normalized.or(&complement).unwrap();
        // DNF reduction preserves meaning; it does not promise a unique
        // representation for every tautology.
        assert!((0..8).all(|assignment| evaluate(&union, assignment)));
        assert!(normalized.and(&complement).unwrap().is_never());
    }
}

fn truth_table(guard: &ChannelGuard) -> u8 {
    (0..8).fold(0, |mask, assignment| {
        mask | (u8::from(evaluate(guard, assignment)) << assignment)
    })
}

#[test]
fn optional_result_and_transport_identities_are_independent_in_every_truth_table() {
    use ril_compiler_core::ids::OptionalTagId;
    let literal = |index: u32, truth| match index {
        0 => GuardLiteral::Optional {
            identity: OptionalTagId(17),
            present: truth,
        },
        1 => GuardLiteral::Result {
            producer: 17,
            version: 0,
            success: truth,
        },
        2 => GuardLiteral::Transport {
            event: ChannelMessageId(17),
            producer: 17,
            version: 0,
            success: truth,
        },
        _ => unreachable!(),
    };
    let evaluate = |guard: &ChannelGuard, assignment: u8| {
        assert!(!guard.incomplete);
        guard.terms.iter().any(|term| {
            term.iter().all(|literal| {
                let (index, expected) = match *literal {
                    GuardLiteral::Optional {
                        identity: OptionalTagId(17),
                        present,
                    } => (0, present),
                    GuardLiteral::Result {
                        producer: 17,
                        version: 0,
                        success,
                    } => (1, success),
                    GuardLiteral::Transport {
                        event: ChannelMessageId(17),
                        success,
                        ..
                    } => (2, success),
                    _ => panic!("unexpected variable in the independent presence oracle"),
                };
                (assignment & (1 << index) != 0) == expected
            })
        })
    };
    for mask in 0..=u8::MAX {
        let guard = ChannelGuard {
            terms: (0..8_u8)
                .filter(|assignment| mask & (1 << assignment) != 0)
                .map(|assignment| {
                    (0..3)
                        .map(|index| literal(index, assignment & (1 << index) != 0))
                        .collect()
                })
                .collect(),
            incomplete: false,
        }
        .normalized()
        .unwrap();
        let complement = guard.not().unwrap();
        for assignment in 0..8 {
            let truth = mask & (1 << assignment) != 0;
            assert_eq!(evaluate(&guard, assignment), truth);
            assert_eq!(evaluate(&complement, assignment), !truth);
        }
        let union = guard.or(&complement).unwrap();
        assert!((0..8).all(|assignment| evaluate(&union, assignment)));
        assert!(guard.and(&complement).unwrap().is_never());
    }
    let present = ChannelGuard::literal(literal(0, true));
    let unrelated = ChannelGuard::literal(GuardLiteral::Optional {
        identity: OptionalTagId(18),
        present: false,
    });
    assert!(!present.and(&unrelated).unwrap().is_never());
}

#[test]
fn every_three_variable_formula_preserves_its_truth_table_and_lattice_operations() {
    for mask in 0..=u8::MAX {
        let original = formula(mask);
        let normalized = original
            .normalized()
            .expect("three-variable formula is bounded");
        assert_eq!(truth_table(&normalized), mask);
        assert_eq!(normalized.normalized().as_ref(), Some(&normalized));
        let complement = normalized.not().unwrap();
        assert_eq!(truth_table(&complement), !mask);
        assert_eq!(truth_table(&normalized.or(&complement).unwrap()), u8::MAX);
        assert_eq!(truth_table(&normalized.and(&complement).unwrap()), 0);
        assert_eq!(normalized.or(&normalized).as_ref(), Some(&normalized));
        assert_eq!(normalized.and(&normalized).as_ref(), Some(&normalized));
        // Eight rotations per function exercise inclusion and incomparable
        // functions without a random test seed.
        for shift in 0..8 {
            let other = mask.rotate_left(shift) ^ 0b0101_0101;
            let right = formula(other).normalized().unwrap();
            assert_eq!(truth_table(&normalized.or(&right).unwrap()), mask | other);
            assert_eq!(truth_table(&normalized.and(&right).unwrap()), mask & other);
        }
    }
}

#[test]
fn aliases_of_one_transport_event_cannot_choose_conflicting_physical_outcomes() {
    let accepted = ChannelGuard::literal(literal(0, true));
    let rejected = ChannelGuard::literal(GuardLiteral::Transport {
        event: ChannelMessageId(0),
        producer: 91,
        version: 17,
        success: false,
    });
    assert!(accepted.and(&rejected).unwrap().is_never());
    assert_eq!(accepted.or(&rejected).unwrap(), ChannelGuard::always());
    // Independent physical events remain independent despite equal outcomes.
    let independent = ChannelGuard::literal(literal(1, false));
    assert_eq!(
        truth_table(&accepted.and(&independent).unwrap()),
        0b0010_0010
    );
}

#[test]
fn incomplete_or_exhausted_guards_never_supply_a_truth_certificate() {
    let incomplete = ChannelGuard::unavailable();
    assert!(!incomplete.is_never());
    assert!(incomplete.normalized().is_none());
    assert!(incomplete.not().is_none());
    for complete in [ChannelGuard::always(), ChannelGuard::never()] {
        assert!(incomplete.and(&complete).is_none());
        assert!(incomplete.or(&complete).is_none());
    }
    let oversized = ChannelGuard {
        terms: [(0..=MAX_GUARD_LITERALS)
            .map(|index| GuardLiteral::Boolean {
                evaluation: ConditionEvaluationId(index as u32),
                truth: true,
            })
            .collect::<BTreeSet<_>>()]
        .into(),
        incomplete: false,
    };
    assert!(oversized.normalized().is_none());
    assert!(oversized.and(&ChannelGuard::always()).is_none());
}
