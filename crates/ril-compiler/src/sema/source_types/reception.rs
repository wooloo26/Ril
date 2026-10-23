//! The source-coordinate part of receiving is one relation over graph IDs.
//! It grants no heap capability, effect, resource or Result authority.
use super::{SourceTypeQueries, graph::*};
use crate::sema::context::FrozenEnvironment;
use crate::sema::{effect_identity::ArgumentKey, source_reception::Construction};
use ril_syntax::ast::ParameterMode;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Position {
    Receiving,
    Invariant,
}

pub(super) fn complete(
    graph: &impl SourceGraph,
    root: SourceTypeId,
    work: &mut WorkLimit,
) -> Result<(), SourceTypesError> {
    work.charge(1)?;
    let mut pending = vec![(root, false)];
    let mut seen = BTreeSet::new();
    while let Some((id, nominal_argument)) = pending.pop() {
        work.charge(1)?;
        if !seen.insert((id, nominal_argument)) {
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
        match node {
            SourceNode::StaticValue(_) if !nominal_argument => {
                return Err(SourceTypesError::Unresolved);
            }
            SourceNode::OpaqueName { arguments, .. } => {
                pending.extend(arguments.iter().map(|id| (*id, true)));
            }
            SourceNode::Alias { target, .. } => pending.push((*target, nominal_argument)),
            _ => pending.extend(node.children().into_iter().map(|id| (id, false))),
        }
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
    annotations: Option<AnnotationContexts<'a>>,
}

#[derive(Clone, Copy)]
struct AnnotationContexts<'a> {
    left: &'a FrozenEnvironment,
    right: &'a FrozenEnvironment,
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
    let ReceptionState {
        work,
        seen,
        annotations,
    } = state;
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
    if let Some(contexts) = annotations
        && contexts.left.id() != contexts.right.id()
        && (matches!(
            left,
            SourceNode::Binder(_)
                | SourceNode::OpaqueName { .. }
                | SourceNode::KeyProjection { .. }
        ) || matches!(
            right,
            SourceNode::Binder(_)
                | SourceNode::OpaqueName { .. }
                | SourceNode::KeyProjection { .. }
        ))
    {
        return Err(SourceTypesError::Unresolved);
    }
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
                ReceptionState {
                    work,
                    seen,
                    annotations,
                },
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
                ReceptionState {
                    work,
                    seen,
                    annotations,
                },
                depth + 1,
            );
        }
    }
    // Recursive declaration edges form finite regular schemas. A fresh syntax
    // construction is finite and must check every one of its physical children.
    if fresh.is_none() && !seen.insert((expected, actual, position)) {
        return Ok(true);
    }
    if let (
        SourceNode::Callable {
            annotations: left,
            row_identity: left_row,
            ..
        },
        SourceNode::Callable {
            annotations: right,
            row_identity: right_row,
            ..
        },
    ) = (left, right)
    {
        if let Some(contexts) = annotations {
            match super::annotation_identity::equivalent(
                left,
                contexts.left,
                right,
                contexts.right,
                work,
            )? {
                super::annotation_identity::RowEquality::Known(false) => return Ok(false),
                super::annotation_identity::RowEquality::Known(true) => {}
                super::annotation_identity::RowEquality::Original => {
                    let (Some(left_row), Some(right_row)) = (left_row, right_row) else {
                        return Err(SourceTypesError::Unresolved);
                    };
                    work.charge(1 + left_row.parameters.len() + right_row.parameters.len())?;
                    if contexts.left.id() != contexts.right.id() {
                        return Err(SourceTypesError::Unresolved);
                    }
                    if left != right
                        || left_row.origin != right_row.origin
                        || left_row.parameters.len() != right_row.parameters.len()
                    {
                        return Ok(false);
                    }
                    for ((left_id, left), (right_id, right)) in
                        left_row.parameters.iter().zip(&right_row.parameters)
                    {
                        if left_id != right_id
                            || !compare(
                                graph,
                                *left,
                                *right,
                                None,
                                Position::Invariant,
                                ReceptionState {
                                    work,
                                    seen,
                                    annotations,
                                },
                                depth + 1,
                            )?
                        {
                            return Ok(false);
                        }
                    }
                }
            }
        } else if (position == Position::Invariant && left != right)
            || ((left_row.is_some() || right_row.is_some())
                && super::annotation_identity::requires_original(left, work)?)
        {
            return Err(SourceTypesError::Unresolved);
        }
    }
    let mut child = |left, right, fresh, position| {
        compare(
            graph,
            left,
            right,
            fresh,
            position,
            ReceptionState {
                work,
                seen,
                annotations,
            },
            depth + 1,
        )
    };
    Ok(match (left, right) {
        (SourceNode::Scalar(left), SourceNode::Scalar(right)) => left == right,
        (SourceNode::Nominal(left), SourceNode::Nominal(right)) => left == right,
        (SourceNode::StaticValue(left), SourceNode::StaticValue(right)) => left == right,
        (SourceNode::Binder(left), SourceNode::Binder(right)) if left == right => true,
        (
            SourceNode::KeyProjection {
                origin: lo,
                parameter: lp,
                identity: li,
                base: lb,
            },
            SourceNode::KeyProjection {
                origin: ro,
                parameter: rp,
                identity: ri,
                base: rb,
            },
        ) => {
            (position == Position::Receiving || lo == ro)
                && lp == rp
                && li == ri
                && child(*lb, *rb, None, Position::Invariant)?
        }
        (SourceNode::KeyProjection { .. }, _) | (_, SourceNode::KeyProjection { .. }) => {
            return Err(SourceTypesError::Unresolved);
        }
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
                ..
            },
            SourceNode::Callable {
                parameters: rp,
                result: rr,
                ..
            },
        ) => {
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
                    ReceptionState {
                        work,
                        seen,
                        annotations,
                    },
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
                    ReceptionState {
                        work,
                        seen,
                        annotations,
                    },
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
            annotations: None,
        },
        0,
    )
}

/// Relational lookup after both inputs pass completeness in their own graphs.
/// A writer may publish several immutable prefixes: later IDs are visible only
/// in the later prefix, while IDs shared by both retain the same actual node.
/// This union must never supply an input's missing-root or missing-edge proof.
struct GraphPair<'a, L, R> {
    left: &'a L,
    right: &'a R,
}

impl<L: SourceGraph, R: SourceGraph> SourceGraph for GraphPair<'_, L, R> {
    fn get(&self, id: SourceTypeId) -> Result<&SourceNode, SourceTypesError> {
        match self.left.get(id) {
            Ok(left) => match self.right.get(id) {
                Ok(right) if std::ptr::eq(left, right) => Ok(left),
                Ok(_) => Err(SourceTypesError::ForeignIdentity),
                Err(SourceTypesError::ForeignIdentity | SourceTypesError::MissingNode) => Ok(left),
                Err(error) => Err(error),
            },
            Err(error @ (SourceTypesError::ForeignIdentity | SourceTypesError::MissingNode)) => {
                match self.right.get(id) {
                    Ok(right) => Ok(right),
                    Err(SourceTypesError::ForeignIdentity) => Err(error),
                    Err(error) => Err(error),
                }
            }
            Err(error) => Err(error),
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
    // Each root and all its edges belong to its own immutable prefix. Only
    // after that check may the relational walk see the union of two prefixes.
    complete(expected_graph, expected, work)?;
    complete(actual_graph, actual, work)?;
    compare(
        &GraphPair {
            left: expected_graph,
            right: actual_graph,
        },
        expected,
        actual,
        fresh,
        Position::Receiving,
        ReceptionState {
            work,
            seen: &mut BTreeSet::new(),
            annotations: None,
        },
        0,
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
            annotations: None,
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
    complete(left, expected, work)?;
    complete(right, actual, work)?;
    compare(
        &graph,
        expected,
        actual,
        None,
        Position::Invariant,
        ReceptionState {
            work,
            seen: &mut BTreeSet::new(),
            annotations: None,
        },
        0,
    )
}

pub(super) fn equivalent_with_environments(
    left: &impl SourceTypeQueries,
    expected: SourceTypeId,
    right: &impl SourceTypeQueries,
    actual: SourceTypeId,
    environments: (&FrozenEnvironment, &FrozenEnvironment),
    work: &mut WorkLimit,
) -> Result<bool, SourceTypesError> {
    work.charge(1)?;
    if environments.0.is_poisoned() || environments.1.is_poisoned() {
        return Err(SourceTypesError::Unresolved);
    }
    let graph = GraphPair { left, right };
    complete(left, expected, work)?;
    complete(right, actual, work)?;
    compare(
        &graph,
        expected,
        actual,
        None,
        Position::Invariant,
        ReceptionState {
            work,
            seen: &mut BTreeSet::new(),
            annotations: Some(AnnotationContexts {
                left: environments.0,
                right: environments.1,
            }),
        },
        0,
    )
}

/// Transitional Type-key ingress for consumers that have not retained graph
/// IDs yet. The graph relation compares complete schemas, including closed
/// row composition; syntax-tree layout is not a Type identity.
pub(crate) fn equivalent_keys(
    expected: &ArgumentKey,
    actual: &ArgumentKey,
    work: &mut WorkLimit,
) -> Result<bool, SourceTypesError> {
    let mut builder = SourceBuilder::new()?;
    let expected = builder.import_key(expected, work)?;
    let actual = builder.import_key(actual, work)?;
    equivalent_in(&builder, expected, actual, work)
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

    fn published_prefixes() -> (SourceTypes, SourceTypeId, SourceTypes, SourceTypeId) {
        let mut builder = SourceBuilder::new().unwrap();
        let mut work = WorkLimit::new(4096);
        let leaf = builder
            .insert(SourceNode::Scalar(SourceScalar::I8), &mut work)
            .unwrap();
        let older_root = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(2),
                    element: leaf,
                },
                &mut work,
            )
            .unwrap();
        let older = builder.snapshot(&mut work).unwrap();
        let newer_root = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(2),
                    element: leaf,
                },
                &mut work,
            )
            .unwrap();
        let newer = builder.freeze(&mut work).unwrap();
        (older, older_root, newer, newer_root)
    }

    #[test]
    fn relational_graph_queries_keep_each_actual_snapshot_prefix() {
        let (older, old, newer, new) = published_prefixes();
        let environment = FrozenEnvironment::default();
        for (left, expected, right, actual) in
            [(&older, old, &newer, new), (&newer, new, &older, old)]
        {
            assert_eq!(
                equivalent(left, expected, right, actual, &mut WorkLimit::new(4096)),
                Ok(true)
            );
            assert_eq!(
                receive_from(
                    left,
                    expected,
                    right,
                    actual,
                    None,
                    &mut WorkLimit::new(4096)
                ),
                Ok(true)
            );
            assert_eq!(
                equivalent_with_environments(
                    left,
                    expected,
                    right,
                    actual,
                    (&environment, &environment),
                    &mut WorkLimit::new(4096)
                ),
                Ok(true)
            );
        }
    }

    #[test]
    fn relational_graph_queries_cannot_borrow_missing_roots_or_edges() {
        let (older, old, newer, new) = published_prefixes();
        let environment = FrozenEnvironment::default();
        assert_eq!(
            equivalent(&older, new, &newer, new, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::MissingNode)
        );
        assert_eq!(
            receive_from(&newer, new, &older, new, None, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::MissingNode)
        );
        assert_eq!(
            equivalent_with_environments(
                &older,
                new,
                &newer,
                new,
                (&environment, &environment),
                &mut WorkLimit::new(4096)
            ),
            Err(SourceTypesError::MissingNode)
        );

        struct Overridden<'a> {
            source: &'a SourceTypes,
            id: SourceTypeId,
            node: SourceNode,
        }
        impl SourceGraph for Overridden<'_> {
            fn get(&self, id: SourceTypeId) -> Result<&SourceNode, SourceTypesError> {
                if id == self.id {
                    Ok(&self.node)
                } else {
                    self.source.get(id)
                }
            }
        }
        let missing_edge = Overridden {
            source: &older,
            id: old,
            node: SourceNode::Array {
                length: SourceLength::Fixed(2),
                element: new,
            },
        };
        assert_eq!(
            equivalent(&missing_edge, old, &newer, new, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::MissingNode)
        );
        let mut foreign_builder = SourceBuilder::new().unwrap();
        let mut work = WorkLimit::new(4096);
        let foreign_leaf = foreign_builder
            .insert(SourceNode::Scalar(SourceScalar::I8), &mut work)
            .unwrap();
        let foreign_root = foreign_builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(2),
                    element: foreign_leaf,
                },
                &mut work,
            )
            .unwrap();
        let foreign = foreign_builder.freeze(&mut work).unwrap();
        let foreign_edge = Overridden {
            source: &older,
            id: old,
            node: SourceNode::Array {
                length: SourceLength::Fixed(2),
                element: foreign_leaf,
            },
        };
        assert_eq!(
            equivalent(
                &foreign_edge,
                old,
                &foreign,
                foreign_root,
                &mut WorkLimit::new(4096)
            ),
            Err(SourceTypesError::ForeignIdentity)
        );
        // Equal contents cannot replace a shared immutable node's identity.
        let copied_node = Overridden {
            source: &older,
            id: old,
            node: older.get(old).unwrap().clone(),
        };
        assert_eq!(
            equivalent(&copied_node, old, &newer, old, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::ForeignIdentity)
        );
    }

    #[test]
    fn relational_graph_queries_spend_one_exact_shared_allowance() {
        let (older, old, newer, new) = published_prefixes();
        let environment = FrozenEnvironment::default();
        for mode in 0..3 {
            let query = |work: &mut WorkLimit| match mode {
                0 => equivalent(&older, old, &newer, new, work),
                1 => receive_from(&older, old, &newer, new, None, work),
                _ => equivalent_with_environments(
                    &older,
                    old,
                    &newer,
                    new,
                    (&environment, &environment),
                    work,
                ),
            };
            let mut work = WorkLimit::new(4096);
            assert_eq!(query(&mut work), Ok(true));
            let used = 4096 - work.remaining();
            let mut exact = WorkLimit::new(used);
            assert_eq!(query(&mut exact), Ok(true));
            assert_eq!(exact.remaining(), 0);
            for short in [0, used - 1] {
                assert_eq!(
                    query(&mut WorkLimit::new(short)),
                    Err(SourceTypesError::BudgetExceeded)
                );
            }
        }
    }

    #[test]
    fn composed_type_keys_compare_graphs_without_erasing_empty_inner_dimensions() {
        let int = ArgumentKey::Name {
            name: "int".into(),
            arguments: vec![],
        };
        let hidden = |n| ArgumentKey::Array {
            length: Some("const(int:0)".into()),
            element: Box::new(ArgumentKey::Array {
                length: Some(format!("const(int:{n})")),
                element: Box::new(int.clone()),
            }),
        };
        let flat = ArgumentKey::Record {
            fields: vec![("empty".into(), false, hidden(3))],
            row: None,
        };
        let composed = |n| ArgumentKey::Record {
            fields: vec![],
            row: Some(Box::new(ArgumentKey::Record {
                fields: vec![("empty".into(), false, hidden(n))],
                row: None,
            })),
        };
        assert_eq!(
            equivalent_keys(&flat, &composed(3), &mut WorkLimit::new(4096)),
            Ok(true)
        );
        assert_eq!(
            equivalent_keys(&flat, &composed(4), &mut WorkLimit::new(4096)),
            Ok(false)
        );
        assert_eq!(
            equivalent_keys(&flat, &composed(3), &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        );
    }

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
