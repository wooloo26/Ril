use super::*;

fn variable(name: &str) -> RowIdentity {
    RowIdentity::Binder(name.into())
}
fn labels(values: &[&str]) -> BTreeSet<String> {
    values.iter().map(|value| (*value).into()).collect()
}
fn fields(values: &[(&str, u8)]) -> Fields<u8> {
    values
        .iter()
        .map(|(name, value)| ((*name).into(), (false, *value)))
        .collect()
}
fn open(values: &[(&str, u8)], name: &str, lacks: &[&str]) -> Row<u8> {
    Row::open(
        fields(values),
        OpenTail {
            identity: variable(name),
            lacks: labels(lacks),
        },
    )
}
fn masked(mask: u8) -> Row<u8> {
    Row::closed(
        (0..3)
            .filter(|index| mask & (1 << index) != 0)
            .map(|index| (((b'a' + index) as char).to_string(), (false, index)))
            .collect(),
    )
}
fn mask(names: impl IntoIterator<Item = String>) -> u8 {
    names
        .into_iter()
        .fold(0, |mask, name| mask | 1 << (name.as_bytes()[0] - b'a'))
}

#[test]
fn closed_rows_match_an_independent_bitset_oracle() {
    let solver = Solver::new("closed", []);
    for a in 0..8 {
        for b in 0..8 {
            let left = masked(a);
            let right = masked(b);
            let difference = field_difference(&left.fields, &right.fields);
            assert_eq!(mask(difference.left_only.keys().cloned()), a & !b);
            assert_eq!(mask(difference.right_only.keys().cloned()), b & !a);
            assert_eq!(mask(difference.common.keys().cloned()), a & b);
            let overlap = solver.overlap(&left, &right).unwrap();
            assert_eq!(mask(overlap.definite), a & b);
            assert!(overlap.possible_labels.is_empty() && overlap.symbolic.is_empty());
            let mut equal = solver.clone();
            let before = equal.clone();
            let result = equal.unify(&left, &right);
            assert_eq!(result.is_ok(), a == b);
            if result.is_err() {
                assert_eq!(equal, before);
            }
            for selected in 0..8 {
                let selected = masked(selected).fields;
                let cuts: BTreeSet<_> = selected.keys().cloned().collect();
                let remainder = solver.remove(&left, &cuts).unwrap().exact().unwrap();
                assert_eq!(mask(remainder.fields.keys().cloned()), a & !mask(cuts));
                let union = solver.union(&left, &right, &selected);
                if (a & b) & !mask(selected.keys().cloned()) != 0 {
                    assert!(matches!(union, Err(RowError::Overlap(_))));
                } else {
                    let union = union.unwrap().exact().unwrap();
                    assert_eq!(
                        mask(union.fields.keys().cloned()),
                        a | b | mask(selected.keys().cloned())
                    );
                    for (label, value) in &selected {
                        assert_eq!(&union.fields[label], value);
                    }
                }
            }
        }
    }
}

#[test]
fn exact_field_identity_and_slot_mutability_are_not_erased() {
    let left = Row::closed(fields(&[("field", 1)]));
    let right = Row::closed(fields(&[("field", 2)]));
    let explicit = [("field".into(), (true, 9))].into();
    let merged = Solver::new("override", [])
        .union(&left, &right, &explicit)
        .unwrap()
        .exact()
        .unwrap();
    assert_eq!(merged.fields["field"], (true, 9));
    let a = Row::closed(fields(&[("field", 1)]));
    let mut mutable = a.clone();
    mutable.fields.get_mut("field").unwrap().0 = true;
    let mut solver = Solver::new("fields", []);
    assert_eq!(
        solver.unify(&a, &mutable),
        Err(RowError::FieldMutability("field".into()))
    );
    let b = Row::closed(fields(&[("field", 2)]));
    assert_eq!(
        solver.unify(&a, &b),
        Err(RowError::FieldType("field".into()))
    );
    let a = Row::closed([("value".into(), (false, "fn(mut Cell)->() &mut"))].into());
    let b = Row::closed([("value".into(), (false, "fn(Cell)->()"))].into());
    assert!(matches!(
        Solver::new("callables", []).unify(&a, &b),
        Err(RowError::FieldType(_))
    ));
}

#[test]
fn a_flexible_tail_is_the_exact_closed_field_difference() {
    let r = variable("callee:R");
    let mut solver = Solver::new("call:1", [r.clone()]);
    let expected = open(&[("id", 1)], "callee:R", &[]);
    let actual = Row::closed(fields(&[("id", 1), ("name", 2)]));
    assert_eq!(solver.unify(&expected, &actual).unwrap(), actual);
    assert_eq!(
        solver.binding(&r),
        Some(&Row::closed(fields(&[("name", 2)])))
    );
    assert!(solver.required_absences(&r).contains("id"));
}

#[test]
fn a_rigid_unknown_tail_is_identical_to_itself_and_never_defaults_to_empty() {
    let row = open(&[], "outer:R", &[]);
    let mut solver = Solver::new("identity", []);
    assert_eq!(solver.normalize(&row).unwrap(), row);
    assert_eq!(solver.unify(&row, &row).unwrap(), row);
    let before = solver.clone();
    assert_eq!(
        solver.unify(&row, &Row::closed(Fields::new())),
        Err(RowError::Rigid(variable("outer:R")))
    );
    assert_eq!(solver, before);
    assert!(!solver.normalize(&row).unwrap().is_closed());
}

#[test]
fn a_required_absence_is_not_an_assumption_about_a_rigid_caller_row() {
    let mut alias = Solver::new("alias", [variable("callee:S")]);
    let before = alias.clone();
    assert!(matches!(
        alias.unify(
            &open(&[], "callee:S", &["forbidden"]),
            &open(&[], "outer:R", &[])
        ),
        Err(RowError::UnprovedAbsence { .. })
    ));
    assert_eq!(alias, before);
    let row = open(&[], "outer:R", &["forbidden"]);
    let actual = open(&[], "outer:R", &[]);
    let mut solver = Solver::new("rigid", []);
    let before = solver.clone();
    assert!(matches!(
        solver.unify(&row, &actual),
        Err(RowError::UnprovedAbsence { .. })
    ));
    assert_eq!(solver, before);
    solver
        .declare_rigid(variable("outer:R"), ["forbidden".into()])
        .unwrap();
    assert_eq!(solver.unify(&row, &actual).unwrap(), row);
}

#[test]
fn flexible_rows_can_extend_known_rigid_rows_but_cannot_invent_their_members() {
    let mut solver = Solver::new("caller", [variable("callee:S")]);
    solver
        .declare_rigid(variable("caller:R"), ["id".into()])
        .unwrap();
    let actual = open(&[("id", 1)], "caller:R", &[]);
    let inferred = open(&[], "callee:S", &[]);
    let result = solver.unify(&actual, &inferred).unwrap();
    assert_eq!(result, actual);
    assert_eq!(solver.binding(&variable("callee:S")), Some(&actual));
    assert!(solver.binding(&variable("caller:R")).is_none());
    let mut solver = Solver::new("missing", [variable("callee:S")]);
    let actual = open(&[], "caller:R", &[]);
    let required = open(&[("id", 1)], "callee:S", &[]);
    assert!(matches!(
        solver.unify(&actual, &required),
        Err(RowError::Rigid(_))
    ));
}

#[test]
fn two_flexible_tails_share_a_fresh_residual_without_losing_unknown_members() {
    let mut solver = Solver::new("instance:7", [variable("R"), variable("S")]);
    let left = open(&[("a", 0)], "R", &[]);
    let right = open(&[("b", 1)], "S", &[]);
    let result = solver.unify(&left, &right).unwrap();
    assert_eq!(result.fields, fields(&[("a", 0), ("b", 1)]));
    let RowTail::Open(tail) = &result.tail else {
        panic!("unknown residual became a closed row");
    };
    assert_eq!(
        tail.identity,
        RowIdentity::Fresh {
            owner: "instance:7".into(),
            ordinal: 0
        }
    );
    assert_eq!(tail.lacks, labels(&["a", "b"]));
    let residual = Row::open(Fields::new(), tail.clone());
    solver
        .unify(&residual, &Row::closed(fields(&[("c", 2)])))
        .unwrap();
    assert_eq!(solver.normalize(&left).unwrap(), masked(7));
    assert_eq!(solver.normalize(&right).unwrap(), masked(7));
}

#[test]
fn forbidden_labels_and_self_extensions_fail_without_partial_assignments() {
    let mut solver = Solver::new("lacks", [variable("R")]);
    let before = solver.clone();
    assert!(matches!(
        solver.unify(&open(&[], "R", &["x"]), &Row::closed(fields(&[("x", 1)]))),
        Err(RowError::Lacks { .. })
    ));
    assert_eq!(solver, before);
    assert!(
        solver
            .unify(&open(&[], "R", &[]), &open(&[("x", 1)], "R", &[]))
            .is_err()
    );
    assert_eq!(solver, before);
    let mut solver = Solver::new("transaction", [variable("R"), variable("S")]);
    let before = solver.clone();
    assert!(
        solver
            .unify(
                &open(&[("a", 0)], "R", &[]),
                &open(&[("b", 1)], "S", &["a"])
            )
            .is_err()
    );
    assert_eq!(
        solver, before,
        "a failed second binding committed the first binding or residual identity"
    );
}

#[test]
fn absence_constraints_follow_aliases_and_residuals() {
    let mut solver = Solver::new("propagate", [variable("R"), variable("S")]);
    solver
        .unify(&open(&[], "R", &[]), &open(&[("b", 1)], "S", &[]))
        .unwrap();
    solver
        .unify(&open(&[], "R", &["x"]), &open(&[], "R", &[]))
        .unwrap();
    let normalized = solver.normalize(&open(&[], "S", &[])).unwrap();
    let RowTail::Open(tail) = normalized.tail else {
        panic!()
    };
    assert!(tail.lacks.contains("x"));
    let before = solver.clone();
    assert!(matches!(
        solver.unify(&open(&[], "R", &["b"]), &open(&[], "R", &[])),
        Err(RowError::Lacks { .. })
    ));
    assert_eq!(solver, before);
}

#[test]
fn overlap_conditions_cover_every_finite_completion_of_one_unknown_tail() {
    let solver = Solver::new("overlap", [variable("R")]);
    for prefix in 0..8 {
        for forbidden in 0..8 {
            let mut left = masked(prefix);
            let required = forbidden | prefix;
            left.tail = RowTail::Open(OpenTail {
                identity: variable("R"),
                lacks: masked(required).fields.keys().cloned().collect(),
            });
            for right in 0..8 {
                let overlap = solver.overlap(&left, &masked(right)).unwrap();
                let mut possible = 0;
                let mut common = 7;
                for completion in 0..8 {
                    if completion & required == 0 {
                        let intersection = (prefix | completion) & right;
                        possible |= intersection;
                        common &= intersection;
                    }
                }
                assert_eq!(mask(overlap.definite), common);
                assert_eq!(mask(overlap.possible_labels), possible & !common);
                assert!(overlap.symbolic.is_empty());
            }
        }
    }
}

#[test]
fn finite_lacks_sets_never_prove_two_open_tails_disjoint() {
    let solver = Solver::new("tails", [variable("R"), variable("S")]);
    let left = open(&[("a", 0)], "R", &["b", "c"]);
    let right = open(&[("b", 1)], "S", &["a", "c"]);
    let overlap = solver.overlap(&left, &right).unwrap();
    assert!(overlap.definite.is_empty() && overlap.possible_labels.is_empty());
    assert!(!overlap.proved_disjoint());
    assert_eq!(overlap.symbolic, [(variable("R"), variable("S"))].into());
    assert!(
        solver
            .union(&left, &right, &Fields::new())
            .unwrap()
            .exact()
            .is_none()
    );
    let same = solver.overlap(&left, &left).unwrap();
    assert!(same.symbolic.contains(&(variable("R"), variable("R"))));
}

#[test]
fn removing_or_overriding_unknown_members_keeps_an_explicit_pending_cut() {
    let solver = Solver::new("cuts", [variable("R")]);
    let row = open(&[("a", 0)], "R", &[]);
    let remainder = solver
        .remove(&row, &labels(&["a"]))
        .unwrap()
        .exact()
        .unwrap();
    assert!(remainder.fields.is_empty());
    assert!(
        matches!(remainder.tail,RowTail::Open(OpenTail {identity:RowIdentity::Binder(ref name),..}) if name=="R")
    );
    let unknown = solver.remove(&row, &labels(&["unknown"])).unwrap();
    assert_eq!(unknown.pending, labels(&["unknown"]));
    assert!(unknown.exact().is_none());
    let row = open(&[("b", 1)], "R", &[]);
    let plan = solver
        .union(
            &row,
            &Row::closed(fields(&[("a", 0)])),
            &fields(&[("a", 2)]),
        )
        .unwrap();
    assert!(plan.overlap.proved_disjoint());
    assert_eq!(plan.pending_removals[&variable("R")], labels(&["a"]));
    assert!(
        plan.exact().is_none(),
        "an override silently erased a possible R.a"
    );
    let row = open(&[("b", 1)], "R", &["a"]);
    assert!(
        solver
            .union(
                &row,
                &Row::closed(fields(&[("a", 0)])),
                &fields(&[("a", 2)])
            )
            .unwrap()
            .exact()
            .is_some()
    );
}

#[test]
fn budget_failure_and_typed_identity_namespaces_are_explicit() {
    let a: Row<u8> = Row::closed(
        (0..20)
            .map(|index| (format!("field_{index}"), (false, index)))
            .collect(),
    );
    let mut solver = Solver::new("budget", []).with_budget(4);
    let before = solver.clone();
    assert_eq!(solver.unify(&a, &a), Err(RowError::Budget));
    assert_eq!(solver, before);
    assert_ne!(
        RowIdentity::Binder("scope:0".into()),
        RowIdentity::Fresh {
            owner: "scope".into(),
            ordinal: 0
        }
    );
    assert_ne!(
        RowIdentity::Fresh {
            owner: "a".into(),
            ordinal: 0
        },
        RowIdentity::Fresh {
            owner: "b".into(),
            ordinal: 0
        }
    );
}
