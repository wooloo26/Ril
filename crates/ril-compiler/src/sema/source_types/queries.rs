use super::graph::*;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceSensitivity {
    Absent { visited: usize },
    Sensitive { coordinate: SourceTypeId },
    Unknown { reason: SourceTypesError },
}

pub use ril_compiler_core::projection::TypeProjection as SourcePath;

pub(crate) struct Substitution {
    pub(crate) types: SourceTypes,
    pub(crate) root: SourceTypeId,
}

pub(crate) trait SourceTypeQueries: SourceGraph {
    fn unalias(
        &self,
        mut id: SourceTypeId,
        work: &mut WorkLimit,
    ) -> Result<SourceTypeId, SourceTypesError> {
        let mut seen = BTreeSet::new();
        loop {
            work.charge(1)?;
            if !seen.insert(id) {
                return Err(SourceTypesError::AliasCycle);
            }
            match self.get(id)? {
                SourceNode::Alias { target, .. } => id = *target,
                _ => return Ok(id),
            }
        }
    }

    fn row_terminates(
        &self,
        mut id: SourceTypeId,
        work: &mut WorkLimit,
    ) -> Result<(), SourceTypesError> {
        let mut seen = BTreeSet::new();
        loop {
            id = self.unalias(id, work)?;
            if !seen.insert(id) {
                return Err(SourceTypesError::RowCycle);
            }
            match self.get(id)? {
                SourceNode::Record { row: Some(row), .. } => id = *row,
                SourceNode::Record { row: None, .. } => return Ok(()),
                _ => return Err(SourceTypesError::Unresolved),
            }
        }
    }

    /// Finite reachability proves absence only after every reachable component
    /// has been checked. Backedges through real fields terminate the walk;
    /// unknown binders and unresolved row equations never become scalar leaves.
    fn sensitivity(&self, root: SourceTypeId, work: &mut WorkLimit) -> SourceSensitivity {
        let result = (|| {
            let mut pending = vec![root];
            let mut seen = BTreeSet::new();
            let mut unknown = None;
            while let Some(id) = pending.pop() {
                if !seen.insert(id) {
                    continue;
                }
                let node = self.get(id)?;
                node.charge(work)?;
                match node {
                    SourceNode::Array { .. }
                    | SourceNode::Callable { .. }
                    | SourceNode::GenericBuiltin(_) => {
                        return Ok(SourceSensitivity::Sensitive { coordinate: id });
                    }
                    SourceNode::Nominal(declaration) => {
                        if declaration.has_coordinates(work)? {
                            return Ok(SourceSensitivity::Sensitive { coordinate: id });
                        }
                    }
                    SourceNode::Binder(_)
                    | SourceNode::KeyProjection { .. }
                    | SourceNode::OpaqueName { .. }
                    | SourceNode::StaticValue(_)
                    | SourceNode::OpaqueComputation(_)
                    | SourceNode::Unresolved { .. } => unknown = Some(SourceTypesError::Unresolved),
                    SourceNode::Alias { .. } => {
                        if let Err(error) = self.unalias(id, work) {
                            unknown = Some(error);
                        }
                    }
                    SourceNode::Record { row: Some(row), .. } => {
                        if let Err(error) = self.row_terminates(*row, work) {
                            unknown = Some(error);
                        }
                    }
                    _ => {}
                }
                pending.extend(node.children());
            }
            Ok(match unknown {
                Some(reason) => SourceSensitivity::Unknown { reason },
                None => SourceSensitivity::Absent {
                    visited: seen.len(),
                },
            })
        })();
        result.unwrap_or_else(|reason| SourceSensitivity::Unknown { reason })
    }

    fn project(
        &self,
        mut id: SourceTypeId,
        path: &[SourcePath],
        work: &mut WorkLimit,
    ) -> Result<SourceTypeId, SourceTypesError> {
        for step in path {
            work.charge(1)?;
            let mut wrappers = BTreeSet::new();
            loop {
                id = self.unalias(id, work)?;
                if !wrappers.insert(id) {
                    return Err(SourceTypesError::AliasCycle);
                }
                if let SourceNode::Container {
                    kind: SourceContainer::Immutable,
                    arguments,
                } = self.get(id)?
                {
                    id = arguments[0];
                } else {
                    break;
                }
            }
            let node = self.get(id)?;
            node.charge(work)?;
            id = match (node, step) {
                (SourceNode::Record { .. }, SourcePath::Field(label)) => {
                    work.text(label)?;
                    self.field(id, label, work)?
                }
                (SourceNode::Tuple(items), SourcePath::Tuple(index)) => *items
                    .get(*index as usize)
                    .ok_or(SourceTypesError::MissingProjection)?,
                (SourceNode::Array { element, .. }, SourcePath::Element) => *element,
                (SourceNode::Map { key, .. }, SourcePath::MapKey) => *key,
                (SourceNode::Callable { parameters, .. }, SourcePath::CallableParameter(index)) => {
                    parameters
                        .get(*index as usize)
                        .ok_or(SourceTypesError::MissingProjection)?
                        .1
                }
                (SourceNode::Callable { result, .. }, SourcePath::CallableResult) => *result,
                (SourceNode::Map { value, .. }, SourcePath::MapValue | SourcePath::Element) => {
                    *value
                }
                (
                    SourceNode::Container {
                        kind: SourceContainer::Option,
                        arguments,
                    },
                    SourcePath::OptionalPayload,
                ) => arguments[0],
                (
                    SourceNode::Container {
                        kind: SourceContainer::Result,
                        arguments,
                    },
                    SourcePath::ResultSuccess,
                ) => arguments[0],
                (
                    SourceNode::Container {
                        kind: SourceContainer::Result,
                        arguments,
                    },
                    SourcePath::ResultError,
                ) => arguments[1],
                (
                    SourceNode::Container {
                        kind:
                            SourceContainer::Set
                            | SourceContainer::Range
                            | SourceContainer::Heap
                            | SourceContainer::Deque,
                        arguments,
                    },
                    SourcePath::Element,
                ) => arguments[0],
                (
                    SourceNode::Binder(_)
                    | SourceNode::OpaqueName { .. }
                    | SourceNode::OpaqueComputation(_)
                    | SourceNode::Unresolved { .. },
                    _,
                ) => return Err(SourceTypesError::Unresolved),
                _ => return Err(SourceTypesError::MissingProjection),
            };
        }
        self.get(id)?;
        Ok(id)
    }

    fn field(
        &self,
        mut id: SourceTypeId,
        label: &str,
        work: &mut WorkLimit,
    ) -> Result<SourceTypeId, SourceTypesError> {
        let mut seen = BTreeSet::new();
        loop {
            id = self.unalias(id, work)?;
            if !seen.insert(id) {
                return Err(SourceTypesError::RowCycle);
            }
            match self.get(id)? {
                SourceNode::Record { fields, row } => {
                    for field in fields {
                        work.charge(1)?;
                        work.text(&field.label)?;
                        if field.label == label {
                            return Ok(field.value);
                        }
                    }
                    id = row.ok_or(SourceTypesError::MissingProjection)?;
                }
                SourceNode::Binder(_)
                | SourceNode::OpaqueName { .. }
                | SourceNode::OpaqueComputation(_)
                | SourceNode::Unresolved { .. } => return Err(SourceTypesError::Unresolved),
                _ => return Err(SourceTypesError::MissingProjection),
            }
        }
    }

    fn reachable(
        &self,
        roots: impl IntoIterator<Item = SourceTypeId>,
        work: &mut WorkLimit,
    ) -> Result<BTreeSet<SourceTypeId>, SourceTypesError> {
        let mut pending = Vec::new();
        for root in roots {
            work.charge(1)?;
            pending.push(root);
        }
        let mut seen = BTreeSet::new();
        while let Some(id) = pending.pop() {
            if seen.contains(&id) {
                continue;
            }
            let node = self.get(id)?;
            node.charge(work)?;
            seen.insert(id);
            pending.extend(node.children());
        }
        Ok(seen)
    }

    /// Copy only the selected reachable graph, preserving finite declaration
    /// cycles and sharing. No legacy syntax or erased runtime shape is read.
    fn copy_into(
        &self,
        roots: impl IntoIterator<Item = SourceTypeId>,
        builder: &mut SourceBuilder,
        work: &mut WorkLimit,
    ) -> Result<BTreeMap<SourceTypeId, SourceTypeId>, SourceTypesError> {
        let reachable = self.reachable(roots, work)?;
        let mut mapping = BTreeMap::new();
        for id in &reachable {
            mapping.insert(*id, builder.reserve(work)?);
        }
        for id in reachable {
            let node = self.get(id)?;
            node.charge(work)?;
            let node = node.map_children(|child| {
                mapping
                    .get(&child)
                    .copied()
                    .ok_or(SourceTypesError::MissingNode)
            })?;
            builder.define(mapping[&id], node, work)?;
        }
        Ok(mapping)
    }

    /// Replacement operates on complete source nodes, never semantic Ty. A
    /// circular binder equation is rejected, while existing declaration cycles
    /// and sharing are copied with their original finite graph structure.
    fn substitute(
        &self,
        root: SourceTypeId,
        selections: &BTreeMap<String, SourceTypeId>,
        work: &mut WorkLimit,
    ) -> Result<Substitution, SourceTypesError> {
        let mut selected = BTreeMap::new();
        let mut needed = VecDeque::new();
        for id in self.reachable([root], work)? {
            if let SourceNode::Binder(identity) = self.get(id)? {
                needed.push_back(identity.clone());
            }
        }
        let mut visited = BTreeSet::new();
        while let Some(identity) = needed.pop_front() {
            if !visited.insert(identity.clone()) {
                continue;
            }
            let Some(target) = selections.get(&identity) else {
                continue;
            };
            work.charge(1)?;
            work.text(&identity)?;
            if matches!(self.get(*target)?, SourceNode::Binder(actual) if *actual == identity) {
                continue;
            }
            for id in self.reachable([*target], work)? {
                if let SourceNode::Binder(dependency) = self.get(id)? {
                    needed.push_back(dependency.clone());
                }
            }
            selected.insert(identity, *target);
        }
        let mut dependencies = BTreeMap::new();
        let mut reverse: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for (identity, target) in &selected {
            let mut required = BTreeSet::new();
            for id in self.reachable([*target], work)? {
                if let SourceNode::Binder(dependency) = self.get(id)?
                    && selected.contains_key(dependency)
                {
                    required.insert(dependency.clone());
                }
            }
            for dependency in &required {
                reverse
                    .entry(dependency.clone())
                    .or_default()
                    .push(identity.clone());
            }
            dependencies.insert(identity.clone(), required.len());
        }
        let mut ready: VecDeque<_> = dependencies
            .iter()
            .filter(|(_, count)| **count == 0)
            .map(|(name, _)| name.clone())
            .collect();
        let mut complete = 0;
        while let Some(name) = ready.pop_front() {
            work.charge(1)?;
            complete += 1;
            for dependent in reverse.get(&name).into_iter().flatten() {
                work.charge(1)?;
                let count = dependencies
                    .get_mut(dependent)
                    .ok_or(SourceTypesError::CyclicSubstitution)?;
                *count -= 1;
                if *count == 0 {
                    ready.push_back(dependent.clone());
                }
            }
        }
        if complete != dependencies.len() {
            return Err(SourceTypesError::CyclicSubstitution);
        }
        let reachable =
            self.reachable([root].into_iter().chain(selected.values().copied()), work)?;
        let mut builder = SourceBuilder::new()?;
        let mut mapping = BTreeMap::new();
        for id in &reachable {
            mapping.insert(*id, builder.reserve(work)?);
        }
        for id in &reachable {
            let node = self.get(*id)?;
            node.charge(work)?;
            let output = match node {
                SourceNode::Binder(identity) if selected.contains_key(identity) => {
                    SourceNode::Alias {
                        declaration: format!("substitution:{identity}"),
                        target: mapping[&selected[identity]],
                    }
                }
                _ => node.map_children(|child| {
                    mapping
                        .get(&child)
                        .copied()
                        .ok_or(SourceTypesError::MissingNode)
                })?,
            };
            builder.define(mapping[id], output, work)?;
        }
        Ok(Substitution {
            root: mapping[&root],
            types: builder.freeze(work)?,
        })
    }
}

impl<T: SourceGraph> SourceTypeQueries for T {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recursive_scalar_fields_have_a_finite_absence_proof() {
        let mut work = WorkLimit::new(1000);
        let mut builder = SourceBuilder::new().unwrap();
        let root = builder.reserve(&mut work).unwrap();
        let scalar = builder
            .insert(SourceNode::Scalar(SourceScalar::Int), &mut work)
            .unwrap();
        let next = builder
            .insert(
                SourceNode::Container {
                    kind: SourceContainer::Option,
                    arguments: vec![root],
                },
                &mut work,
            )
            .unwrap();
        builder
            .define(
                root,
                SourceNode::Record {
                    fields: vec![
                        SourceField {
                            label: "value".into(),
                            mutable: true,
                            value: scalar,
                        },
                        SourceField {
                            label: "next".into(),
                            mutable: true,
                            value: next,
                        },
                    ],
                    row: None,
                },
                &mut work,
            )
            .unwrap();
        let types = builder.freeze(&mut work).unwrap();
        assert!(matches!(
            types.sensitivity(root, &mut WorkLimit::new(100)),
            SourceSensitivity::Absent { visited: 3 }
        ));
        let projected = types
            .project(
                root,
                &[
                    SourcePath::Field("next".into()),
                    SourcePath::OptionalPayload,
                    SourcePath::Field("value".into()),
                ],
                &mut WorkLimit::new(100),
            )
            .unwrap();
        assert_eq!(projected, scalar);
    }

    #[test]
    fn unknown_binders_alias_cycles_and_row_cycles_never_prove_absence() {
        let mut work = WorkLimit::new(1000);
        let mut builder = SourceBuilder::new().unwrap();
        let binder = builder
            .insert(SourceNode::Binder("owner:T".into()), &mut work)
            .unwrap();
        let alias = builder.reserve(&mut work).unwrap();
        builder
            .define(
                alias,
                SourceNode::Alias {
                    declaration: "A".into(),
                    target: alias,
                },
                &mut work,
            )
            .unwrap();
        let row = builder.reserve(&mut work).unwrap();
        builder
            .define(
                row,
                SourceNode::Record {
                    fields: vec![],
                    row: Some(row),
                },
                &mut work,
            )
            .unwrap();
        let types = builder.freeze(&mut work).unwrap();
        for id in [binder, alias, row] {
            assert!(matches!(
                types.sensitivity(id, &mut WorkLimit::new(100)),
                SourceSensitivity::Unknown { .. }
            ));
        }
        assert!(matches!(
            types.sensitivity(binder, &mut WorkLimit::new(0)),
            SourceSensitivity::Unknown {
                reason: SourceTypesError::BudgetExceeded
            }
        ));
    }

    #[test]
    fn shared_substitution_keeps_dimensions_and_rejects_circular_equations() {
        let mut work = WorkLimit::new(1000);
        let mut builder = SourceBuilder::new().unwrap();
        let binder = builder
            .insert(SourceNode::Binder("owner:T".into()), &mut work)
            .unwrap();
        let fixed = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(2),
                    element: binder,
                },
                &mut work,
            )
            .unwrap();
        let scalar = builder
            .insert(SourceNode::Scalar(SourceScalar::Int), &mut work)
            .unwrap();
        let pair = builder
            .insert(SourceNode::Tuple(vec![fixed, fixed]), &mut work)
            .unwrap();
        let types = builder.freeze(&mut work).unwrap();
        let selected = types
            .substitute(
                pair,
                &[("owner:T".into(), scalar)].into(),
                &mut WorkLimit::new(1000),
            )
            .unwrap();
        let first = selected
            .types
            .project(
                selected.root,
                &[SourcePath::Tuple(0)],
                &mut WorkLimit::new(100),
            )
            .unwrap();
        let second = selected
            .types
            .project(
                selected.root,
                &[SourcePath::Tuple(1)],
                &mut WorkLimit::new(100),
            )
            .unwrap();
        assert_eq!(first, second);
        assert!(matches!(
            selected.types.get(first),
            Ok(SourceNode::Array {
                length: SourceLength::Fixed(2),
                ..
            })
        ));
        assert!(matches!(
            types.substitute(
                pair,
                &[("owner:T".into(), fixed)].into(),
                &mut WorkLimit::new(1000)
            ),
            Err(SourceTypesError::CyclicSubstitution)
        ));
        assert!(matches!(
            selected.types.get(pair),
            Err(SourceTypesError::ForeignIdentity)
        ));
    }
}
