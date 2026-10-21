//! Known coordinate conflicts and candidates under genuine symbolic member types.
//! This decides only type incompatibility; it never proves source independence.
use crate::sema::effect_identity::ArgumentKey;
use crate::sema::effect_identity::StaticBinderSort;
use crate::sema::record_bounds::BoundScope;

fn constant_dimension(value: &str) -> Option<u64> {
    value
        .strip_prefix("const(int:")?
        .strip_suffix(')')?
        .parse()
        .ok()
}

/// Caller must first validate the complete original source coordinates. A
/// different U/V identity alone is an unresolved type equation; fixed known
/// dimensions, callable modes and explicit qualifications cannot be erased by
/// that unknown element coordinate.
pub(super) fn definite_member_conflict(
    left: &ArgumentKey,
    right: &ArgumentKey,
    depth: usize,
) -> bool {
    if depth >= 64 || left == right {
        return false;
    }
    let child = |left, right| definite_member_conflict(left, right, depth + 1);
    match (left, right) {
        (ArgumentKey::Closed(_), _) | (_, ArgumentKey::Closed(_)) => false,
        (ArgumentKey::Binder { .. }, _) | (_, ArgumentKey::Binder { .. }) => false,
        (
            ArgumentKey::Array {
                length: a,
                element: left,
            },
            ArgumentKey::Array {
                length: b,
                element: right,
            },
        ) => {
            let dimension_conflict = match (a, b) {
                (Some(a), Some(b)) => matches!((constant_dimension(a),constant_dimension(b)),
                    (Some(a),Some(b)) if a!=b),
                _ => false,
            };
            dimension_conflict || child(left, right)
        }
        (
            ArgumentKey::Callable {
                parameters: a,
                result: left,
                annotations: first,
            },
            ArgumentKey::Callable {
                parameters: b,
                result: right,
                annotations: second,
            },
        ) => {
            a.len() != b.len()
                || first != second
                || a.iter()
                    .zip(b)
                    .any(|((a, left), (b, right))| a != b || child(left, right))
                || child(left, right)
        }
        (ArgumentKey::Tuple(a), ArgumentKey::Tuple(b)) => {
            a.len() != b.len() || a.iter().zip(b).any(|(a, b)| child(a, b))
        }
        (
            ArgumentKey::Name {
                name: a,
                arguments: left,
            },
            ArgumentKey::Name {
                name: b,
                arguments: right,
            },
        ) => {
            a != b || left.len() != right.len() || left.iter().zip(right).any(|(a, b)| child(a, b))
        }
        (
            ArgumentKey::Map {
                key: a,
                value: left,
            },
            ArgumentKey::Map {
                key: b,
                value: right,
            },
        ) => child(a, b) || child(left, right),
        (
            ArgumentKey::Record {
                fields: a,
                row: left,
            },
            ArgumentKey::Record {
                fields: b,
                row: right,
            },
        ) => {
            let closed_labels_differ = left.is_none()
                && right.is_none()
                && (a.len() != b.len()
                    || a.iter()
                        .map(|field| &field.0)
                        .ne(b.iter().map(|field| &field.0)));
            closed_labels_differ
                || a.iter().any(|(name, mode, key)| {
                    b.iter().any(|(other, other_mode, other_key)| {
                        name == other && (mode != other_mode || child(key, other_key))
                    })
                })
        }
        // Computations and unsupported shape comparisons retain an obligation.
        _ => left.is_closed() && right.is_closed(),
    }
}

/// A producer-only admission filter for the missing array/callable source
/// witness branch. It is not the source proof: callers must already have the
/// genuine original formal/header anchor and exact stored field. The independent
/// staged receiver replay checks these conditions again from real declarations.
/// Ordinary unknown types, unknown dimensions and opaque nested rows stay NI.
pub(super) fn symbolic_member_candidate(key: &ArgumentKey, scope: &BoundScope) -> bool {
    if !matches!(
        key,
        ArgumentKey::Array { .. } | ArgumentKey::Callable { .. }
    ) {
        return false;
    }
    let mut pending = vec![(key, 0usize)];
    let mut work = 4096usize;
    let mut found = false;
    while let Some((key, depth)) = pending.pop() {
        if depth >= 64 || work == 0 {
            return false;
        }
        work -= 1;
        match key {
            ArgumentKey::GenericBuiltin(_) => {}
            ArgumentKey::Closed(_) => return false,
            ArgumentKey::Binder {
                identity,
                sort: StaticBinderSort::Type,
            } => {
                if !scope.types.values().any(|actual| actual == identity) {
                    return false;
                }
                found = true;
            }
            ArgumentKey::Name { arguments, .. } | ArgumentKey::Tuple(arguments) => {
                pending.extend(arguments.iter().map(|key| (key, depth + 1)));
            }
            ArgumentKey::Array { length, element } => {
                if length
                    .as_ref()
                    .is_some_and(|length| constant_dimension(length).is_none())
                {
                    return false;
                }
                pending.push((element, depth + 1));
            }
            ArgumentKey::Callable {
                parameters,
                result,
                annotations,
            } => {
                if annotations.iter().any(|annotation| {
                    !matches!(
                        annotation.as_str(),
                        "&mut" | "&^mut" | "&closure" | "&capture" | "@{}" | "&{}"
                    )
                }) {
                    return false;
                }
                pending.extend(parameters.iter().map(|(_, key)| (key, depth + 1)));
                pending.push((result, depth + 1));
            }
            ArgumentKey::Record { fields, row: None } => {
                pending.extend(fields.iter().map(|(_, _, key)| (key, depth + 1)));
            }
            ArgumentKey::Record { row: Some(_), .. } => return false,
            ArgumentKey::Map { key, value } => {
                pending.push((key, depth + 1));
                pending.push((value, depth + 1));
            }
        }
    }
    found
}

#[cfg(test)]
mod tests {
    use super::*;
    use ril_syntax::ast::ParameterMode;

    fn binder(identity: &str) -> ArgumentKey {
        ArgumentKey::Binder {
            identity: identity.into(),
            sort: StaticBinderSort::Type,
        }
    }

    #[test]
    fn symbolic_element_does_not_erase_a_known_inner_dimension_under_empty_storage() {
        let array = |length| ArgumentKey::Array {
            length: Some(format!("const(int:{length})")),
            element: Box::new(binder("real:U")),
        };
        let empty = |element| ArgumentKey::Array {
            length: Some("const(int:0)".into()),
            element: Box::new(element),
        };
        assert!(definite_member_conflict(
            &empty(array(2)),
            &empty(array(3)),
            0
        ));
    }

    #[test]
    fn symbolic_parameter_and_result_do_not_erase_callable_modes() {
        let callable = |mode, annotations| ArgumentKey::Callable {
            parameters: vec![(mode, binder("real:U"))],
            result: Box::new(binder("real:U")),
            annotations,
        };
        assert!(definite_member_conflict(
            &callable(ParameterMode::Read, vec![]),
            &callable(ParameterMode::Mut, vec!["&mut".into()]),
            0
        ));
    }

    #[test]
    fn different_genuine_type_coordinates_do_not_prove_object_or_type_disjointness() {
        assert!(!definite_member_conflict(
            &binder("first:U"),
            &binder("second:U"),
            0
        ));
        let symbolic_length = |name: &str| ArgumentKey::Array {
            length: Some(name.into()),
            element: Box::new(binder("real:U")),
        };
        assert!(!definite_member_conflict(
            &symbolic_length("n"),
            &symbolic_length("m"),
            0
        ));
    }

    fn scope() -> BoundScope {
        BoundScope {
            types: [("U".into(), "real:U".into())].into(),
            rows: Default::default(),
        }
    }

    #[test]
    fn a_known_dimension_with_its_real_nearest_u_is_only_a_candidate() {
        let key = ArgumentKey::Array {
            length: Some("const(int:2)".into()),
            element: Box::new(binder("real:U")),
        };
        assert!(symbolic_member_candidate(&key, &scope()));
        assert!(!symbolic_member_candidate(&key, &BoundScope::default()));
        let other = BoundScope {
            types: [("U".into(), "other:U".into())].into(),
            rows: Default::default(),
        };
        assert!(!symbolic_member_candidate(&key, &other));
    }

    #[test]
    fn empty_outer_storage_does_not_resolve_an_unknown_inner_dimension() {
        let key = ArgumentKey::Array {
            length: Some("const(int:0)".into()),
            element: Box::new(ArgumentKey::Array {
                length: Some("n".into()),
                element: Box::new(binder("real:U")),
            }),
        };
        assert!(!symbolic_member_candidate(&key, &scope()));
    }

    #[test]
    fn closed_composites_and_raw_u_keep_their_existing_proof_paths() {
        let key = ArgumentKey::Array {
            length: Some("const(int:2)".into()),
            element: Box::new(ArgumentKey::Name {
                name: "int".into(),
                arguments: vec![],
            }),
        };
        assert!(!symbolic_member_candidate(&key, &scope()));
        assert!(!symbolic_member_candidate(&binder("real:U"), &scope()));
    }

    #[test]
    fn an_unknown_effect_bound_cannot_be_laundered_by_a_symbolic_parameter() {
        let key = ArgumentKey::Callable {
            parameters: vec![(ParameterMode::Read, binder("real:U"))],
            result: Box::new(binder("real:U")),
            annotations: vec!["&SomeState".into()],
        };
        assert!(!symbolic_member_candidate(&key, &scope()));
    }
}
