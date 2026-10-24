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
        if let SourceNode::Callable {
            interpretation: Some(context),
            ..
        } = node
            && context.is_poisoned()
        {
            return Err(SourceTypesError::Unresolved);
        }
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

type ComparedTypes = (
    SourceTypeId,
    SourceTypeId,
    Position,
    Option<(
        crate::sema::context::FrozenEnvId,
        crate::sema::context::FrozenEnvId,
    )>,
);

struct ReceptionState<'a> {
    work: &'a mut WorkLimit,
    seen: &'a mut BTreeSet<ComparedTypes>,
    annotations: Option<AnnotationContexts<'a>>,
    // Structural receiving leaves latent row bounds to the value checker.
    // Capturing a scope must not turn that upper-bound check into equality.
    compare_rows: bool,
}

#[derive(Clone, Copy)]
struct AnnotationContexts<'a> {
    left: &'a FrozenEnvironment,
    right: &'a FrozenEnvironment,
}

/// Compare a resolved binder's interpretation, independently of capture
/// allocation. Distinct instances still need the same complete selected type.
pub(crate) fn same_binder_selection(
    identity: &str,
    left: &FrozenEnvironment,
    right: &FrozenEnvironment,
    work: &mut WorkLimit,
) -> Result<bool, SourceTypesError> {
    work.text(identity)?;
    if left.is_poisoned() || right.is_poisoned() {
        return Ok(false);
    }
    for environment in [left, right] {
        work.charge(environment.generic_context.len() + 4)?;
        let mut declared = environment.generic_sources.contains_key(identity)
            || environment.generic_substitutions.contains_key(identity);
        for actual in environment.generic_context.values() {
            work.text(actual)?;
            declared |= actual == identity;
        }
        if !declared {
            return Ok(false);
        }
    }
    if left.same_types(right) {
        return Ok(true);
    }
    if left.static_key_arguments.get(identity) != right.static_key_arguments.get(identity) {
        return Ok(false);
    }
    match (
        left.generic_sources.get(identity),
        right.generic_sources.get(identity),
    ) {
        (Some(left), Some(right)) => {
            if std::sync::Arc::ptr_eq(left, right) {
                Ok(true)
            } else {
                left.schema.equivalent_in(
                    &right.schema,
                    &left.environment,
                    &right.environment,
                    work,
                )
            }
        }
        (None, None) => Ok(!left.generic_substitutions.contains_key(identity)
            && !right.generic_substitutions.contains_key(identity)),
        _ => Ok(false),
    }
}

fn same_binder_interpretation(
    left: &SourceNode,
    right: &SourceNode,
    contexts: AnnotationContexts<'_>,
    work: &mut WorkLimit,
) -> Result<bool, SourceTypesError> {
    match (left, right) {
        (SourceNode::Binder(left), SourceNode::Binder(right)) => {
            work.text(left)?;
            work.text(right)?;
            if left != right {
                return Ok(false);
            }
            same_binder_selection(left, contexts.left, contexts.right, work)
        }
        (
            SourceNode::KeyProjection {
                parameter: left_parameter,
                identity: left,
                ..
            },
            SourceNode::KeyProjection {
                parameter: right_parameter,
                identity: right,
                ..
            },
        ) => {
            work.text(left)?;
            work.text(right)?;
            let declared = [contexts.left, contexts.right]
                .into_iter()
                .all(|environment| {
                    environment.static_key_arguments.contains_key(left)
                        || environment
                            .generic_context
                            .values()
                            .any(|identity| identity == left)
                });
            Ok(declared
                && left_parameter == right_parameter
                && left == right
                && contexts.left.static_key_arguments.get(left)
                    == contexts.right.static_key_arguments.get(right))
        }
        _ => Ok(false),
    }
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
        compare_rows,
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
    fn contextual<'a>(
        node: &'a SourceNode,
        fallback: Option<&'a FrozenEnvironment>,
    ) -> Option<&'a FrozenEnvironment> {
        match node {
            SourceNode::Callable {
                interpretation: Some(context),
                ..
            } => Some(context),
            _ => fallback,
        }
    }
    let annotations = match (
        contextual(left, annotations.map(|c| c.left)),
        contextual(right, annotations.map(|c| c.right)),
    ) {
        (Some(left), Some(right)) => Some(AnnotationContexts { left, right }),
        _ => None,
    };
    left.charge(work)?;
    right.charge(work)?;
    // Bottom is a subtype at a receiving position, including a callable's
    // covariant result. This proves only type compatibility, never an exit.
    // Invariant storage/parameter comparisons retain exact type identity.
    if position == Position::Receiving && matches!(right, SourceNode::Scalar(SourceScalar::Never)) {
        return Ok(true);
    }
    if let Some(contexts) = annotations
        && (compare_rows || position == Position::Invariant)
        && contexts.left.id() != contexts.right.id()
        && (matches!(
            left,
            SourceNode::Binder(_)
                | SourceNode::KeyProjection { .. }
                | SourceNode::OpaqueName {
                    declaration: None,
                    ..
                }
        ) || matches!(
            right,
            SourceNode::Binder(_)
                | SourceNode::KeyProjection { .. }
                | SourceNode::OpaqueName {
                    declaration: None,
                    ..
                }
        ))
        && !same_binder_interpretation(left, right, contexts, work)?
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
                    compare_rows,
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
                    compare_rows,
                    work,
                    seen,
                    annotations,
                },
                depth + 1,
            );
        }
    }
    if let SourceNode::NullaryConstructor {
        declaration,
        source,
    } = right
    {
        if let SourceNode::NullaryConstructor {
            declaration: expected,
            source: original,
        } = left
        {
            return Ok(declaration == expected && source == original);
        }
        let receiver = match declaration {
            ril_compiler_core::builtin_calls::NullaryConstructor::None => {
                matches!(left, SourceNode::Container { kind: SourceContainer::Option, arguments } if arguments.len() == 1)
            }
        };
        if position != Position::Receiving || !receiver {
            return Ok(false);
        }
        if !matches!(fresh, Some(Construction::Nullary { declaration: actual, source: occurrence }) if actual == declaration && occurrence == source)
        {
            // A stored, still uninstantiated template needs an inference
            // equation. Missing receiving evidence is not a type mismatch.
            return Err(SourceTypesError::Unresolved);
        }
        return Ok(true);
    }
    // Recursive declaration edges form finite regular schemas. A fresh syntax
    // construction is finite and must check every one of its physical children.
    if fresh.is_none()
        && !seen.insert((
            expected,
            actual,
            position,
            annotations.map(|c| (c.left.id(), c.right.id())),
        ))
    {
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
        if let Some(contexts) = annotations
            && (compare_rows || position == Position::Invariant)
            && !(position == Position::Receiving && left.is_empty())
        {
            match super::annotation_identity::equivalent(
                left,
                contexts.left,
                right,
                contexts.right,
                work,
            )? {
                super::annotation_identity::RowEquality::Known(false) => {
                    return if position == Position::Receiving {
                        // A receiving row is an upper bound. Its satisfaction needs
                        // the callable contract derivation, not row equality.
                        Err(SourceTypesError::Unresolved)
                    } else {
                        Ok(false)
                    };
                }
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
                        return if position == Position::Receiving {
                            Err(SourceTypesError::Unresolved)
                        } else {
                            Ok(false)
                        };
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
                                    compare_rows,
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
                compare_rows,
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
            drop(child);
            let mut callable_child = |left, right, position, reverse| {
                compare(
                    graph,
                    left,
                    right,
                    None,
                    position,
                    ReceptionState {
                        compare_rows,
                        work,
                        seen,
                        annotations: if reverse {
                            annotations.map(|contexts| AnnotationContexts {
                                left: contexts.right,
                                right: contexts.left,
                            })
                        } else {
                            annotations
                        },
                    },
                    depth + 1,
                )
            };
            for ((lm, left), (rm, right)) in lp.iter().zip(rp) {
                if lm != rm {
                    return Ok(false);
                }
                let fits = if *lm == ParameterMode::Read && position == Position::Receiving {
                    callable_child(*right, *left, Position::Receiving, true)?
                } else {
                    callable_child(*left, *right, Position::Invariant, false)?
                };
                if !fits {
                    return Ok(false);
                }
            }
            callable_child(*lr, *rr, position, false)?
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
                declaration: left_declaration,
                name: left,
                arguments: la,
            },
            SourceNode::OpaqueName {
                declaration: right_declaration,
                name: right,
                arguments: ra,
            },
        ) => {
            if left != right || la.len() != ra.len() || left_declaration != right_declaration {
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
                        compare_rows,
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
                        compare_rows,
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
            compare_rows: false,
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
    receive_from_in(
        expected_graph,
        expected,
        actual_graph,
        actual,
        fresh,
        None,
        work,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn receive_from_in(
    expected_graph: &impl SourceTypeQueries,
    expected: SourceTypeId,
    actual_graph: &impl SourceTypeQueries,
    actual: SourceTypeId,
    fresh: Option<&Construction>,
    environments: Option<(&FrozenEnvironment, &FrozenEnvironment)>,
    work: &mut WorkLimit,
) -> Result<bool, SourceTypesError> {
    // Each root and all its edges belong to its own immutable prefix. Only
    // after that check may the relational walk see the union of two prefixes.
    work.charge(1)?;
    if environments.is_some_and(|(left, right)| left.is_poisoned() || right.is_poisoned()) {
        return Err(SourceTypesError::Unresolved);
    }
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
            compare_rows: environments.is_some(),
            work,
            seen: &mut BTreeSet::new(),
            annotations: environments.map(|(left, right)| AnnotationContexts { left, right }),
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
            compare_rows: true,
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
            compare_rows: true,
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
            compare_rows: true,
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
    fn equivalent_inputs(
        expected: &ArgumentKey,
        actual: &ArgumentKey,
        work: &mut WorkLimit,
    ) -> Result<bool, SourceTypesError> {
        let mut builder = SourceBuilder::new()?;
        let expected = builder.import_key(expected, work)?;
        let actual = builder.import_key(actual, work)?;
        equivalent_in(&builder, expected, actual, work)
    }
    use super::*;

    #[test]
    fn bottom_receives_covariantly_but_cannot_erase_invariant_parameters_or_unknowns() {
        let mut work = WorkLimit::new(100_000);
        let mut graph = SourceBuilder::new().unwrap();
        let unit = graph
            .insert(SourceNode::Scalar(SourceScalar::Unit), &mut work)
            .unwrap();
        let bottom = graph
            .insert(SourceNode::Scalar(SourceScalar::Never), &mut work)
            .unwrap();
        let unknown = graph
            .insert(
                SourceNode::Unresolved {
                    description: "missing header".into(),
                    arguments: vec![],
                },
                &mut work,
            )
            .unwrap();
        let callback = |graph: &mut SourceBuilder,
                        parameter: Option<(ParameterMode, SourceTypeId)>,
                        result,
                        work: &mut WorkLimit| {
            graph
                .insert(
                    SourceNode::Callable {
                        parameters: parameter.into_iter().collect(),
                        result,
                        annotations: vec![],
                        row_identity: None,
                        interpretation: None,
                    },
                    work,
                )
                .unwrap()
        };
        let expected = callback(
            &mut graph,
            None::<(ParameterMode, SourceTypeId)>,
            unit,
            &mut work,
        );
        let actual = callback(&mut graph, None, bottom, &mut work);
        assert_eq!(receive(&graph, expected, actual, None, &mut work), Ok(true));
        assert_eq!(
            equivalent_in(&graph, expected, actual, &mut work),
            Ok(false)
        );
        assert_eq!(
            receive(&graph, actual, expected, None, &mut work),
            Ok(false)
        );
        let expected_mut = callback(
            &mut graph,
            Some((ParameterMode::Mut, unit)),
            unit,
            &mut work,
        );
        let actual_mut = callback(
            &mut graph,
            Some((ParameterMode::Mut, bottom)),
            unit,
            &mut work,
        );
        assert_eq!(
            receive(&graph, expected_mut, actual_mut, None, &mut work),
            Ok(false)
        );
        assert_eq!(
            receive(&graph, unknown, bottom, None, &mut work),
            Err(SourceTypesError::Unresolved)
        );
        assert_eq!(
            receive(&graph, expected, actual, None, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        );
    }

    #[test]
    fn binder_comparison_uses_resolved_identity_and_checks_each_selection() {
        use crate::sema::source_types::SourceSchema;
        use crate::sema::{context::TypingEnvironment, effect_identity::StaticBinderSort};
        let mut environment = TypingEnvironment::default();
        environment
            .generic_context
            .insert("T".into(), "decl:T".into());
        let original = environment.freeze();
        let derived = original.with_contract_bindings(BTreeMap::from([("x".into(), 7)]));
        let key = ArgumentKey::Binder {
            identity: "decl:T".into(),
            sort: StaticBinderSort::Type,
        };
        let mut work = WorkLimit::new(16384);
        let schema = SourceSchema::import(&key, None, &mut work).unwrap();
        assert!(
            schema
                .receive_schema_in(&schema, &original, &derived, None, &mut work)
                .unwrap()
        );
        assert!(
            schema
                .equivalent_in(&schema, &original, &derived, &mut work)
                .unwrap()
        );
        let independent = original.thaw().freeze();
        assert!(
            schema
                .receive_schema_in(&schema, &original, &independent, None, &mut work)
                .unwrap()
        );
        assert!(
            schema
                .receive_schema_in(
                    &schema,
                    &original,
                    &FrozenEnvironment::poisoned(),
                    None,
                    &mut work
                )
                .is_err()
        );
        assert!(
            schema
                .receive_schema_in(&schema, &original, &derived, None, &mut WorkLimit::new(0))
                .is_err()
        );
    }

    #[test]
    fn selected_binders_compare_complete_types_across_captures() {
        use crate::sema::{
            context::TypingEnvironment,
            model::SourceTypeWitness,
            source_types::{SourceSchema, TypeSourceSelection},
        };
        use ril_compiler_core::source::{FileId, Span};
        use std::sync::Arc;
        let mut work = WorkLimit::new(32768);
        let mut capture = |extent: &str| {
            let key = ArgumentKey::Array {
                length: Some("const(int:0)".into()),
                element: Box::new(ArgumentKey::Array {
                    length: Some(format!("const(int:{extent})")),
                    element: Box::new(ArgumentKey::Name {
                        name: "int".into(),
                        arguments: vec![],
                    }),
                }),
            };
            let schema = SourceSchema::import(&key, None, &mut work).unwrap();
            let syntax = schema
                .syntax_projection(
                    Span {
                        file: FileId(0),
                        start: 0,
                        end: 0,
                    },
                    &mut work,
                    &mut |_, _, _| Err(SourceTypesError::Unresolved),
                )
                .unwrap();
            let witness = SourceTypeWitness {
                key: crate::static_eval::normalized_argument_key(&syntax),
                syntax,
            };
            let source = TypeSourceSelection::from_closed(
                Arc::new(witness),
                TypingEnvironment::default().freeze(),
            )
            .unwrap();
            let mut environment = TypingEnvironment::default();
            environment
                .generic_context
                .insert("T".into(), "factory:T".into());
            environment
                .generic_sources
                .insert("factory:T".into(), source);
            environment.freeze()
        };
        let first = capture("2");
        let same = capture("2");
        let different = capture("3");
        assert!(same_binder_selection("factory:T", &first, &same, &mut work).unwrap());
        assert!(!same_binder_selection("factory:T", &first, &different, &mut work).unwrap());
        assert!(!same_binder_selection("other:T", &first, &same, &mut work).unwrap());
        assert!(
            !same_binder_selection(
                "factory:T",
                &first,
                &FrozenEnvironment::poisoned(),
                &mut work
            )
            .unwrap()
        );
        assert!(same_binder_selection("factory:T", &first, &same, &mut WorkLimit::new(0)).is_err());
    }

    #[test]
    fn resolved_nominals_use_declarations_and_unresolved_names_keep_their_scope() {
        use crate::sema::{context::TypingEnvironment, source_types::SourceSchema};
        use ril_compiler_core::ids::StmtId;
        let mut work = WorkLimit::new(8192);
        let mut nominal = |declaration: Option<StmtId>| {
            let mut builder = SourceBuilder::new().unwrap();
            let root = builder
                .insert(
                    SourceNode::OpaqueName {
                        declaration: declaration.map(NominalDeclaration::Hir),
                        name: "Cell".into(),
                        arguments: vec![],
                    },
                    &mut work,
                )
                .unwrap();
            let types = builder.freeze(&mut work).unwrap();
            SourceSchema::frozen_view(&types, root, None, &mut work).unwrap()
        };
        let first = nominal(Some(StmtId(1)));
        let same = nominal(Some(StmtId(1)));
        let distinct = nominal(Some(StmtId(2)));
        let unresolved = nominal(None);
        let left = TypingEnvironment::default().freeze();
        let right = TypingEnvironment::default().freeze();
        assert!(
            first
                .equivalent_in(&same, &left, &right, &mut work)
                .unwrap()
        );
        assert!(
            !first
                .equivalent_in(&distinct, &left, &right, &mut work)
                .unwrap()
        );
        assert!(
            unresolved
                .equivalent_in(&unresolved, &left, &right, &mut work)
                .is_err()
        );
        assert!(
            !first
                .equivalent_in(&unresolved, &left, &left, &mut work)
                .unwrap()
        );
        assert!(!first.requires_declaration_environment(&mut work).unwrap());
        assert!(
            unresolved
                .requires_declaration_environment(&mut work)
                .unwrap()
        );
    }

    #[test]
    fn key_projection_identity_compares_selected_keys_across_snapshots() {
        use crate::sema::{
            context::TypingEnvironment, model::StaticCoordinate, source_types::SourceSchema,
        };
        use ril_compiler_core::ids::{GenericParamId, TypeExprId};
        let mut work = WorkLimit::new(8192);
        let mut builder = SourceBuilder::new().unwrap();
        let base = builder
            .insert(SourceNode::Binder("declaration:T".into()), &mut work)
            .unwrap();
        let root = builder
            .insert(
                SourceNode::KeyProjection {
                    origin: KeyProjectionOrigin::Type(TypeExprId(1)),
                    parameter: GenericParamId(2),
                    identity: "declaration:K".into(),
                    base,
                },
                &mut work,
            )
            .unwrap();
        let types = builder.freeze(&mut work).unwrap();
        let schema = SourceSchema::frozen_view(&types, root, None, &mut work).unwrap();
        let mut environment = TypingEnvironment::default();
        environment
            .generic_context
            .insert("T".into(), "declaration:T".into());
        environment
            .generic_context
            .insert("K".into(), "declaration:K".into());
        environment.static_key_arguments.insert(
            "declaration:K".into(),
            StaticCoordinate::Label("left".into()),
        );
        let left = environment.clone().freeze();
        let same = environment.clone().freeze();
        environment.static_key_arguments.insert(
            "declaration:K".into(),
            StaticCoordinate::Label("right".into()),
        );
        let distinct = environment.freeze();
        assert!(
            schema
                .equivalent_in(&schema, &left, &same, &mut work)
                .unwrap()
        );
        assert!(
            schema
                .equivalent_in(&schema, &left, &distinct, &mut work)
                .is_err()
        );
        assert!(
            schema
                .equivalent_in(
                    &schema,
                    &left,
                    &TypingEnvironment::default().freeze(),
                    &mut work
                )
                .is_err()
        );
    }

    #[test]
    fn nullary_constructor_templates_require_the_same_fresh_read_and_optional_receiver() {
        use ril_compiler_core::{builtin_calls::NullaryConstructor, ids::ExprId};
        let mut work = WorkLimit::new(16384);
        let actual = super::super::SourceSchema::nullary_constructor(
            NullaryConstructor::None,
            ExprId(1),
            &mut work,
        )
        .unwrap();
        let mut builder = SourceBuilder::new().unwrap();
        let int = builder
            .insert(SourceNode::Scalar(SourceScalar::Int), &mut work)
            .unwrap();
        let array = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(2),
                    element: int,
                },
                &mut work,
            )
            .unwrap();
        let root = builder
            .insert(
                SourceNode::Container {
                    kind: SourceContainer::Option,
                    arguments: vec![array],
                },
                &mut work,
            )
            .unwrap();
        let types = builder.freeze(&mut work).unwrap();
        let expected =
            super::super::SourceSchema::frozen_view(&types, root, None, &mut work).unwrap();
        let fresh = Construction::Nullary {
            declaration: NullaryConstructor::None,
            source: ExprId(1),
        };
        assert!(
            expected
                .receive_schema(&actual, Some(&fresh), &mut work)
                .unwrap()
        );
        for absent in [
            None,
            Some(Construction::Opaque),
            Some(Construction::Nullary {
                declaration: NullaryConstructor::None,
                source: ExprId(2),
            }),
        ] {
            assert!(
                expected
                    .receive_schema(&actual, absent.as_ref(), &mut work)
                    .is_err()
            );
        }
        let integer =
            super::super::SourceSchema::scalar(SourceScalar::Int, None, &mut work).unwrap();
        assert!(
            !integer
                .receive_schema(&actual, Some(&fresh), &mut work)
                .unwrap()
        );
        assert!(!expected.equivalent(&actual, &mut work).unwrap());
        assert!(actual.equivalent(&actual, &mut work).unwrap());
        assert!(
            expected
                .receive_schema(&actual, Some(&fresh), &mut WorkLimit::new(0))
                .is_err()
        );
    }

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
            equivalent_inputs(&flat, &composed(3), &mut WorkLimit::new(4096)),
            Ok(true)
        );
        assert_eq!(
            equivalent_inputs(&flat, &composed(4), &mut WorkLimit::new(4096)),
            Ok(false)
        );
        assert_eq!(
            equivalent_inputs(&flat, &composed(3), &mut WorkLimit::new(0)),
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
