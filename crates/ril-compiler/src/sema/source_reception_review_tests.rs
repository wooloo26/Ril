//! Independent review tests for `source_reception`, registered after v37.
//! The finite oracle models
//! source dimensions and modes; it grants no runtime/permission/row authority.
use super::effect_identity::ArgumentKey;
use super::source_reception::{self as relation, Construction};
use ril_compiler_core::source::FileId;
use ril_syntax::ast::ParameterMode;

fn int() -> ArgumentKey {
    ArgumentKey::Name {
        name: "int".into(),
        arguments: vec![],
    }
}

#[test]
fn projection_keeps_nested_dimensions_and_refuses_excessive_row_scans() {
    use super::facts::Slot;
    let hir = crate::hir::nodes::HirProgram::lower(&ril_syntax::ast::Program::default()).unwrap();
    let project = |key: &ArgumentKey, slot: Slot| {
        let mut work = super::source_types::WorkLimit::new(4096);
        let source = super::source_types::declarations::schema(key, &hir, &mut work)?;
        let path = super::source_types::steps_in(&[slot], &mut work)?;
        source.project_steps(&path, &mut work)
    };
    let source = record(false, array(Some(0), array(Some(3), int())));
    let member = project(&source, Slot::Field("items".into())).unwrap();
    assert_eq!(
        super::source_types::SourceSchema::import(
            &array(Some(0), array(Some(2), int())),
            None,
            &mut super::source_types::WorkLimit::new(4096)
        )
        .unwrap()
        .receive_schema(
            &member,
            None,
            &mut super::source_types::WorkLimit::new(4096)
        ),
        Ok(false),
    );
    assert!(project(&source, Slot::Field("missing".into())).is_err());
    let wide = ArgumentKey::Record {
        fields: (0..4097)
            .map(|index| (format!("field{index}"), false, int()))
            .collect(),
        row: None,
    };
    assert!(project(&wide, Slot::Field("field0".into())).is_err());
}

fn array(length: Option<u64>, element: ArgumentKey) -> ArgumentKey {
    ArgumentKey::Array {
        length: length.map(|value| format!("const(int:{value})")),
        element: Box::new(element),
    }
}

fn callback(mode: ParameterMode, input: ArgumentKey, result: ArgumentKey) -> ArgumentKey {
    ArgumentKey::Callable {
        parameters: vec![(mode, input)],
        result: Box::new(result),
        annotations: vec![],
    }
}

fn record(mutable: bool, member: ArgumentKey) -> ArgumentKey {
    ArgumentKey::Record {
        fields: vec![("items".into(), mutable, member)],
        row: None,
    }
}

fn fresh(source: &str) -> Construction {
    let parsed = ril_syntax::parse_expression(source, FileId(0));
    assert!(
        parsed.diagnostics.is_empty() && !parsed.incomplete,
        "{source}\n{:?}",
        parsed.diagnostics
    );
    relation::construction(&parsed.expression, &mut 4096).unwrap()
}

// Reference model deliberately does not recurse through production keys.
// Dynamic receiving accepts an already fixed root; fixed receiving requires
// that same fixed source. Stored element positions remain exactly invariant.
fn root_dimension_fits(expected: Option<u64>, actual: Option<u64>) -> bool {
    expected.is_none() || expected == actual
}

#[test]
fn finite_stored_outer_array_model_never_weakens_element_dimensions() {
    let dimensions = [None, Some(0), Some(1), Some(2)];
    for expected_outer in dimensions {
        for actual_outer in dimensions {
            for expected_inner in dimensions {
                for actual_inner in dimensions {
                    let expected = array(expected_outer, array(expected_inner, int()));
                    let actual = array(actual_outer, array(actual_inner, int()));
                    let oracle = root_dimension_fits(expected_outer, actual_outer)
                        && expected_inner == actual_inner;
                    assert_eq!(
                        relation::compatible(&expected, &actual, None, &mut 4096),
                        Some(oracle),
                        "expected={expected:?} actual={actual:?}"
                    );
                    // Exhaustion may remove a proof, never invent one. This
                    // also includes outer length zero without graph children.
                    for allowance in 0..32 {
                        let mut remaining = allowance;
                        let result = relation::compatible(&expected, &actual, None, &mut remaining);
                        assert!(remaining <= allowance);
                        if result == Some(true) {
                            assert!(oracle, "fuel={allowance} {expected:?} <- {actual:?}");
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn finite_callable_model_keeps_read_contravariance_and_write_invariance() {
    let dimensions = [None, Some(0), Some(1), Some(2)];
    for mode in [
        ParameterMode::Read,
        ParameterMode::Mut,
        ParameterMode::SharedMut,
    ] {
        for expected_length in dimensions {
            for actual_length in dimensions {
                let expected = callback(mode, array(expected_length, int()), int());
                let actual = callback(mode, array(actual_length, int()), int());
                let oracle = if mode == ParameterMode::Read {
                    root_dimension_fits(actual_length, expected_length)
                } else {
                    expected_length == actual_length
                };
                assert_eq!(
                    relation::compatible(&expected, &actual, None, &mut 4096),
                    Some(oracle),
                    "{expected:?} <- {actual:?}"
                );
                // A callable stored as an array element is fully invariant,
                // including its otherwise contravariant Read parameters.
                assert_eq!(
                    relation::compatible(
                        &array(Some(0), expected),
                        &array(Some(0), actual),
                        None,
                        &mut 4096
                    ),
                    Some(expected_length == actual_length)
                );
            }
        }
    }
}

#[test]
fn fresh_record_and_tuple_children_receive_their_real_array_contexts() {
    let expected_record = record(false, array(Some(2), int()));
    let actual_record = record(false, array(None, int()));
    let record_construction = fresh(".{items:[7,9]}");
    assert_eq!(
        relation::compatible(
            &expected_record,
            &actual_record,
            Some(&record_construction),
            &mut 4096
        ),
        Some(true)
    );
    assert_eq!(
        relation::compatible(&expected_record, &actual_record, None, &mut 4096),
        Some(false)
    );

    let expected_tuple = ArgumentKey::Tuple(vec![array(Some(2), int()), int()]);
    let actual_tuple = ArgumentKey::Tuple(vec![array(None, int()), int()]);
    let tuple_construction = fresh("([7,9],0)");
    assert_eq!(
        relation::compatible(
            &expected_tuple,
            &actual_tuple,
            Some(&tuple_construction),
            &mut 4096
        ),
        Some(true)
    );
    assert_eq!(
        relation::compatible(&expected_tuple, &actual_tuple, None, &mut 4096),
        Some(false)
    );
}

#[test]
fn fresh_aggregate_does_not_upgrade_a_stored_child_by_its_backing_count() {
    let expected = record(false, array(Some(2), int()));
    let actual = record(false, array(None, int()));
    let construction = fresh(".{items:stored}");
    assert_eq!(
        relation::compatible(&expected, &actual, Some(&construction), &mut 4096),
        Some(false)
    );
    for source in ["stored", "make()", "make([7,9])"] {
        assert!(matches!(fresh(source), Construction::Opaque));
    }
}

#[test]
fn stored_tuple_map_and_mutable_record_positions_remain_invariant() {
    let expected_child = array(None, int());
    let actual_child = array(Some(2), int());
    let pairs = [
        (
            ArgumentKey::Tuple(vec![expected_child.clone(), int()]),
            ArgumentKey::Tuple(vec![actual_child.clone(), int()]),
        ),
        (
            ArgumentKey::Map {
                key: Box::new(int()),
                value: Box::new(expected_child.clone()),
            },
            ArgumentKey::Map {
                key: Box::new(int()),
                value: Box::new(actual_child.clone()),
            },
        ),
        (
            record(true, expected_child.clone()),
            record(true, actual_child.clone()),
        ),
    ];
    for (expected, actual) in pairs {
        assert_eq!(
            relation::compatible(&expected, &actual, None, &mut 4096),
            Some(false)
        );
    }
    assert_eq!(
        relation::compatible(
            &record(false, expected_child),
            &record(false, actual_child),
            None,
            &mut 4096
        ),
        Some(true)
    );
}

#[test]
fn unresolved_annotation_spelling_does_not_become_a_definite_type_conflict() {
    let with_row = |row: &str| {
        array(
            Some(0),
            ArgumentKey::Callable {
                parameters: vec![(
                    ParameterMode::Read,
                    callback(ParameterMode::Read, int(), int()),
                )],
                result: Box::new(int()),
                annotations: vec![row.into()],
            },
        )
    };
    // ArgumentKey currently preserves annotation order and effect-set alias
    // spelling. The coordinate helper cannot prove these rows unequal.
    assert_eq!(
        relation::compatible(&with_row("@{A,B}"), &with_row("@{B,A}"), None, &mut 4096),
        None
    );
    assert_eq!(
        relation::compatible(
            &with_row("@Async"),
            &with_row("@{Fiber,Concurrent}"),
            None,
            &mut 4096
        ),
        None
    );
}

#[test]
fn explicitly_typed_record_is_not_an_unconstrained_member_construction() {
    // `Fixed` has already fixed this mutable field's source type. Only its own
    // constructor receiving stage may use the inner array's fresh syntax.
    let construction = fresh("Fixed.{items:[7,9]}");
    assert!(matches!(construction, Construction::Opaque));
    assert_eq!(
        relation::compatible(
            &record(true, array(None, int())),
            &record(true, array(Some(2), int())),
            Some(&construction),
            &mut 4096
        ),
        Some(false)
    );
}

#[test]
fn closed_selected_remainders_preserve_the_whole_record_schema() {
    for mutable in [false, true] {
        for member in [
            array(Some(2), int()),
            callback(ParameterMode::Mut, int(), int()),
        ] {
            let flat = record(mutable, member.clone());
            let selected = ArgumentKey::Record {
                fields: vec![],
                row: Some(Box::new(flat.clone())),
            };
            assert_eq!(
                relation::compatible(&flat, &selected, None, &mut 4096),
                Some(true)
            );
            assert_eq!(
                relation::compatible(&selected, &flat, None, &mut 4096),
                Some(true)
            );
            let wrong = record(mutable, array(Some(3), int()));
            assert_eq!(
                relation::compatible(&selected, &wrong, None, &mut 4096),
                Some(false)
            );
        }
    }
}

#[test]
fn remainder_views_never_discard_open_identity_overlap_or_member_modes() {
    let closed = record(false, array(Some(2), int()));
    let mut open = closed.clone();
    let ArgumentKey::Record { row, .. } = &mut open else {
        unreachable!()
    };
    *row = Some(Box::new(ArgumentKey::Binder {
        identity: "caller:R".into(),
        sort: super::effect_identity::StaticBinderSort::Type,
    }));
    assert_eq!(relation::compatible(&closed, &open, None, &mut 4096), None);
    assert_eq!(
        relation::compatible(&open, &open, None, &mut 4096),
        Some(true)
    );
    let overlap = ArgumentKey::Record {
        fields: vec![("items".into(), false, array(Some(2), int()))],
        row: Some(Box::new(closed.clone())),
    };
    assert_eq!(
        relation::compatible(&closed, &overlap, None, &mut 4096),
        None
    );
    let writable = ArgumentKey::Record {
        fields: vec![],
        row: Some(Box::new(record(true, array(Some(2), int())))),
    };
    assert_eq!(
        relation::compatible(&closed, &writable, None, &mut 4096),
        Some(false)
    );
    assert_eq!(relation::compatible(&closed, &writable, None, &mut 0), None);
}

#[test]
fn receiving_immutable_qualification_preserves_written_inner_dimensions() {
    let immutable = |inner| ArgumentKey::Name {
        name: "Immut".into(),
        arguments: vec![inner],
    };
    for length in [None, Some(0), Some(2)] {
        let expected = immutable(array(length, int()));
        let original = array(length, int());
        assert_eq!(
            relation::compatible(&expected, &original, None, &mut 4096),
            Some(true)
        );
    }
    assert_eq!(
        relation::compatible(
            &immutable(array(Some(2), int())),
            &array(None, int()),
            None,
            &mut 4096,
        ),
        Some(false)
    );
    assert_eq!(
        relation::compatible(
            &immutable(array(Some(2), int())),
            &array(None, int()),
            Some(&fresh("[7,9]")),
            &mut 4096,
        ),
        Some(true)
    );
}

#[test]
fn immutable_coordinate_view_does_not_retype_stored_container_elements() {
    let original = array(Some(0), array(Some(2), int()));
    let expected = array(
        Some(0),
        ArgumentKey::Name {
            name: "Immut".into(),
            arguments: vec![array(Some(2), int())],
        },
    );
    assert_eq!(
        relation::compatible(&expected, &original, None, &mut 4096),
        Some(false)
    );
}
