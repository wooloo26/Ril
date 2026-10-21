//! The source-coordinate part of receiving is one relation over graph IDs.
//! It grants no heap capability, effect, resource or Result authority.
use super::{SourceTypeQueries, graph::*};
use crate::sema::{effect_identity::ArgumentKey, source_reception::Construction};
use ril_syntax::ast::ParameterMode;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Position {
    Receiving,
    Invariant,
}

fn complete(
    graph: &impl SourceGraph,
    root: SourceTypeId,
    work: &mut WorkLimit,
) -> Result<(), SourceTypesError> {
    work.charge(1)?;
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    while let Some(id) = pending.pop() {
        work.charge(1)?;
        if !seen.insert(id) {
            continue;
        }
        let node = graph.get(id)?;
        node.charge(work)?;
        if matches!(
            node,
            SourceNode::OpaqueComputation(_) | SourceNode::Unresolved { .. }
        ) {
            return Err(SourceTypesError::Unresolved);
        }
        pending.extend(node.children());
    }
    Ok(())
}

type RecordView<'a> = (
    BTreeMap<&'a str, (bool, SourceTypeId)>,
    Option<SourceTypeId>,
);

fn record_view<'a>(
    graph: &'a impl SourceTypeQueries,
    root: SourceTypeId,
    work: &mut WorkLimit,
) -> Result<RecordView<'a>, SourceTypesError> {
    let mut cursor = Some(root);
    let mut seen = BTreeSet::new();
    let closed = loop {
        work.charge(1)?;
        let Some(id) = cursor else {
            break true;
        };
        let id = graph.unalias(id, work)?;
        if !seen.insert(id) {
            return Err(SourceTypesError::RowCycle);
        }
        match graph.get(id)? {
            SourceNode::Record { row, .. } => cursor = *row,
            _ => break false,
        }
    };
    let mut fields = BTreeMap::new();
    cursor = Some(root);
    loop {
        work.charge(1)?;
        let Some(id) = cursor else {
            return Ok((fields, None));
        };
        let id = graph.unalias(id, work)?;
        let SourceNode::Record { fields: next, row } = graph.get(id)? else {
            return Ok((fields, Some(id)));
        };
        for field in next {
            work.charge(1)?;
            work.text(&field.label)?;
            if fields
                .insert(field.label.as_str(), (field.mutable, field.value))
                .is_some()
            {
                return Err(SourceTypesError::DuplicateField);
            }
        }
        if !closed {
            return Ok((fields, *row));
        }
        cursor = *row;
    }
}

struct ReceptionState<'a> {
    work: &'a mut WorkLimit,
    seen: &'a mut BTreeSet<(SourceTypeId, SourceTypeId, Position)>,
}

fn compare(
    graph: &impl SourceTypeQueries,
    expected: SourceTypeId,
    actual: SourceTypeId,
    fresh: Option<&Construction>,
    position: Position,
    state: ReceptionState<'_>,
    depth: usize,
) -> Result<bool, SourceTypesError> {
    let ReceptionState { work, seen } = state;
    work.charge(1)?;
    if depth > 64 {
        return Err(SourceTypesError::BudgetExceeded);
    }
    let expected = graph.unalias(expected, work)?;
    let actual = graph.unalias(actual, work)?;
    let left = graph.get(expected)?;
    let right = graph.get(actual)?;
    left.charge(work)?;
    right.charge(work)?;
    if let SourceNode::GenericBuiltin(declaration) = right {
        if let SourceNode::GenericBuiltin(expected) = left {
            return Ok(expected == declaration);
        }
        // Instantiation is available at a receiving boundary. Invariant
        // comparison of two already chosen signatures never generalizes one.
        if position == Position::Receiving {
            return Ok(
                super::polymorphic::instantiate(graph, *declaration, expected, work)?.is_some(),
            );
        }
        return Ok(false);
    }
    if position == Position::Receiving {
        let inner = |node: &SourceNode| match node {
            SourceNode::Container {
                kind: SourceContainer::Immutable,
                arguments,
            } => arguments.first().copied(),
            _ => None,
        };
        if let Some(left) = inner(left) {
            return compare(
                graph,
                left,
                inner(right).unwrap_or(actual),
                fresh,
                position,
                ReceptionState { work, seen },
                depth + 1,
            );
        }
        if let Some(right) = inner(right) {
            return compare(
                graph,
                expected,
                right,
                fresh,
                position,
                ReceptionState { work, seen },
                depth + 1,
            );
        }
    }
    // Recursive declaration edges form finite regular schemas. A fresh syntax
    // construction is finite and must check every one of its physical children.
    if fresh.is_none() && !seen.insert((expected, actual, position)) {
        return Ok(true);
    }
    let mut child = |left, right, fresh, position| {
        compare(
            graph,
            left,
            right,
            fresh,
            position,
            ReceptionState { work, seen },
            depth + 1,
        )
    };
    Ok(match (left, right) {
        (SourceNode::Scalar(left), SourceNode::Scalar(right)) => left == right,
        (SourceNode::Nominal(left), SourceNode::Nominal(right)) => left == right,
        (SourceNode::Binder(left), SourceNode::Binder(right)) if left == right => true,
        (SourceNode::Binder(_), _) | (_, SourceNode::Binder(_)) => {
            return Err(SourceTypesError::Unresolved);
        }
        (
            SourceNode::Array {
                length: left,
                element: le,
            },
            SourceNode::Array {
                length: right,
                element: re,
            },
        ) => {
            let items = match fresh {
                Some(Construction::Array(items)) => Some(items),
                _ => None,
            };
            let lengths = match (*left, *right) {
                (SourceLength::Fixed(left), SourceLength::Fixed(right)) => left == right,
                (SourceLength::Fixed(left), SourceLength::Dynamic) => {
                    items.is_some_and(|items| left == items.len() as u64)
                }
                (SourceLength::Dynamic, SourceLength::Fixed(_)) => position == Position::Receiving,
                (SourceLength::Dynamic, SourceLength::Dynamic) => true,
            };
            if !lengths {
                return Ok(false);
            }
            if let Some(items) = items {
                for item in items {
                    if !child(*le, *re, Some(item), Position::Receiving)? {
                        return Ok(false);
                    }
                }
                true
            } else {
                child(*le, *re, None, Position::Invariant)?
            }
        }
        (
            SourceNode::Callable {
                parameters: lp,
                result: lr,
                annotations: la,
            },
            SourceNode::Callable {
                parameters: rp,
                result: rr,
                annotations: ra,
            },
        ) => {
            if position == Position::Invariant && la != ra {
                return Err(SourceTypesError::Unresolved);
            }
            if lp.len() != rp.len() {
                return Ok(false);
            }
            for ((lm, left), (rm, right)) in lp.iter().zip(rp) {
                if lm != rm {
                    return Ok(false);
                }
                let fits = if *lm == ParameterMode::Read && position == Position::Receiving {
                    child(*right, *left, None, Position::Receiving)?
                } else {
                    child(*left, *right, None, Position::Invariant)?
                };
                if !fits {
                    return Ok(false);
                }
            }
            child(*lr, *rr, None, position)?
        }
        (
            SourceNode::Container {
                kind: left,
                arguments: la,
            },
            SourceNode::Container {
                kind: right,
                arguments: ra,
            },
        ) => {
            if left != right || la.len() != ra.len() {
                return Ok(false);
            }
            for (left, right) in la.iter().zip(ra) {
                if !child(*left, *right, None, Position::Invariant)? {
                    return Ok(false);
                }
            }
            true
        }
        (
            SourceNode::OpaqueName {
                name: left,
                arguments: la,
            },
            SourceNode::OpaqueName {
                name: right,
                arguments: ra,
            },
        ) => {
            if left != right || la.len() != ra.len() {
                return Ok(false);
            }
            for (left, right) in la.iter().zip(ra) {
                if !child(*left, *right, None, Position::Invariant)? {
                    return Ok(false);
                }
            }
            true
        }
        (SourceNode::Tuple(left), SourceNode::Tuple(right)) => {
            if left.len() != right.len() {
                return Ok(false);
            }
            let members = match fresh {
                Some(Construction::Tuple(items)) if items.len() == left.len() => Some(items),
                Some(Construction::Tuple(_)) => return Err(SourceTypesError::Unresolved),
                _ => None,
            };
            for (index, (left, right)) in left.iter().zip(right).enumerate() {
                let fresh = members.map(|items| &items[index]);
                let position = if fresh.is_some() {
                    Position::Receiving
                } else {
                    Position::Invariant
                };
                if !child(*left, *right, fresh, position)? {
                    return Ok(false);
                }
            }
            true
        }
        (SourceNode::Map { key: lk, value: lv }, SourceNode::Map { key: rk, value: rv }) => {
            child(*lk, *rk, None, Position::Invariant)?
                && child(*lv, *rv, None, Position::Invariant)?
        }
        (SourceNode::Record { .. }, SourceNode::Record { .. }) => {
            let (left, lr) = record_view(graph, expected, work)?;
            let (right, rr) = record_view(graph, actual, work)?;
            if left.len() != right.len() {
                return if lr.is_some() || rr.is_some() {
                    Err(SourceTypesError::Unresolved)
                } else {
                    Ok(false)
                };
            }
            let members = match fresh {
                Some(Construction::Record(fields)) => Some(fields),
                _ => None,
            };
            for ((ln, (lm, left)), (rn, (rm, right))) in left.iter().zip(&right) {
                if lm != rm || ln != rn {
                    return Ok(false);
                }
                let fresh = members.and_then(|members| members.get(*ln));
                let position = if fresh.is_some() {
                    Position::Receiving
                } else if *lm {
                    Position::Invariant
                } else {
                    position
                };
                if !compare(
                    graph,
                    *left,
                    *right,
                    fresh,
                    position,
                    ReceptionState { work, seen },
                    depth + 1,
                )? {
                    return Ok(false);
                }
            }
            match (lr, rr) {
                (None, None) => true,
                (Some(left), Some(right)) => compare(
                    graph,
                    left,
                    right,
                    None,
                    Position::Invariant,
                    ReceptionState { work, seen },
                    depth + 1,
                )?,
                _ => return Err(SourceTypesError::Unresolved),
            }
        }
        (SourceNode::OpaqueComputation(_) | SourceNode::Unresolved { .. }, _)
        | (_, SourceNode::OpaqueComputation(_) | SourceNode::Unresolved { .. }) => {
            return Err(SourceTypesError::Unresolved);
        }
        _ => false,
    })
}

pub(crate) fn receive(
    graph: &impl SourceTypeQueries,
    expected: SourceTypeId,
    actual: SourceTypeId,
    fresh: Option<&Construction>,
    work: &mut WorkLimit,
) -> Result<bool, SourceTypesError> {
    complete(graph, expected, work)?;
    complete(graph, actual, work)?;
    compare(
        graph,
        expected,
        actual,
        fresh,
        Position::Receiving,
        ReceptionState {
            work,
            seen: &mut BTreeSet::new(),
        },
        0,
    )
}

struct GraphPair<'a, L, R> {
    left: &'a L,
    right: &'a R,
}

impl<L: SourceGraph, R: SourceGraph> SourceGraph for GraphPair<'_, L, R> {
    fn get(&self, id: SourceTypeId) -> Result<&SourceNode, SourceTypesError> {
        match self.left.get(id) {
            Err(SourceTypesError::ForeignIdentity) => self.right.get(id),
            result => result,
        }
    }
}

/// Declaration views are invariant, including their outer array dimensions.
/// Comparing two validated arenas does not make their IDs interchangeable.
pub(crate) fn receive_from(
    expected_graph: &impl SourceTypeQueries,
    expected: SourceTypeId,
    actual_graph: &impl SourceTypeQueries,
    actual: SourceTypeId,
    fresh: Option<&Construction>,
    work: &mut WorkLimit,
) -> Result<bool, SourceTypesError> {
    receive(
        &GraphPair {
            left: expected_graph,
            right: actual_graph,
        },
        expected,
        actual,
        fresh,
        work,
    )
}

/// Equality within an already combined graph. Reusing that graph also avoids
/// recursively nesting GraphPair types during polymorphic correlation checks.
pub(crate) fn equivalent_in(
    graph: &impl SourceTypeQueries,
    expected: SourceTypeId,
    actual: SourceTypeId,
    work: &mut WorkLimit,
) -> Result<bool, SourceTypesError> {
    complete(graph, expected, work)?;
    complete(graph, actual, work)?;
    compare(
        graph,
        expected,
        actual,
        None,
        Position::Invariant,
        ReceptionState {
            work,
            seen: &mut BTreeSet::new(),
        },
        0,
    )
}

pub(crate) fn equivalent(
    left: &impl SourceTypeQueries,
    expected: SourceTypeId,
    right: &impl SourceTypeQueries,
    actual: SourceTypeId,
    work: &mut WorkLimit,
) -> Result<bool, SourceTypesError> {
    let graph = GraphPair { left, right };
    complete(&graph, expected, work)?;
    complete(&graph, actual, work)?;
    compare(
        &graph,
        expected,
        actual,
        None,
        Position::Invariant,
        ReceptionState {
            work,
            seen: &mut BTreeSet::new(),
        },
        0,
    )
}

/// One transitional ingress; the relation itself never parses a key or erases
/// dimensions. Callers that already own graph IDs invoke `receive` directly.
pub(crate) fn receive_keys(
    expected: &ArgumentKey,
    actual: &ArgumentKey,
    fresh: Option<&Construction>,
    work: &mut usize,
) -> Option<bool> {
    let mut budget = WorkLimit::new(*work);
    let result = (|| {
        let mut builder = SourceBuilder::new()?;
        let expected = builder.import_key(expected, &mut budget)?;
        let actual = builder.import_key(actual, &mut budget)?;
        receive(&builder, expected, actual, fresh, &mut budget)
    })();
    *work = budget.remaining();
    result.ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recursive_receiving_checks_the_whole_regular_schema() {
        let mut builder = SourceBuilder::new().unwrap();
        let mut work = WorkLimit::new(10_000);
        let scalar = builder
            .insert(SourceNode::Scalar(SourceScalar::Int), &mut work)
            .unwrap();
        let roots: Vec<_> = (0..3)
            .map(|_| builder.reserve(&mut work).unwrap())
            .collect();
        for (root, length) in roots.iter().zip([3, 3, 2]) {
            let element = builder
                .insert(
                    SourceNode::Array {
                        length: SourceLength::Fixed(length),
                        element: scalar,
                    },
                    &mut work,
                )
                .unwrap();
            builder
                .define(
                    *root,
                    SourceNode::Record {
                        fields: vec![
                            SourceField {
                                label: "next".into(),
                                mutable: false,
                                value: *root,
                            },
                            SourceField {
                                label: "values".into(),
                                mutable: true,
                                value: element,
                            },
                        ],
                        row: None,
                    },
                    &mut work,
                )
                .unwrap();
        }
        let graph = builder.freeze(&mut work).unwrap();
        assert_eq!(
            receive(&graph, roots[0], roots[1], None, &mut work),
            Ok(true)
        );
        assert_eq!(
            receive(&graph, roots[0], roots[2], None, &mut work),
            Ok(false)
        );
        assert_eq!(
            receive(&graph, roots[0], roots[1], None, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        );
    }

    #[test]
    fn contextual_empty_construction_cannot_hide_an_unknown_actual_schema() {
        let mut builder = SourceBuilder::new().unwrap();
        let mut work = WorkLimit::new(1_000);
        let scalar = builder
            .insert(SourceNode::Scalar(SourceScalar::Int), &mut work)
            .unwrap();
        let unknown = builder
            .insert(
                SourceNode::Unresolved {
                    description: "unresolved source".into(),
                    arguments: vec![],
                },
                &mut work,
            )
            .unwrap();
        let expected = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(0),
                    element: scalar,
                },
                &mut work,
            )
            .unwrap();
        let actual = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(0),
                    element: unknown,
                },
                &mut work,
            )
            .unwrap();
        assert_eq!(
            receive(
                &builder,
                expected,
                actual,
                Some(&Construction::Array(vec![])),
                &mut work
            ),
            Err(SourceTypesError::Unresolved)
        );
    }
}
