//! Graph-only construction and observation. New roots are frozen atomically;
//! repeated children from one source arena retain one shared copy mapping.
use super::*;
use crate::sema::context::FrozenEnvironment;
use crate::sema::{copy_contract::CopyMode, source_reception::Construction};
use ril_syntax::ast::ParameterMode;
use std::collections::{BTreeMap, BTreeSet};

type CallableParts = (Vec<(ParameterMode, SourceSchema)>, SourceSchema);
type RecordParts = (Vec<(String, bool, SourceSchema)>, Option<SourceSchema>);

fn annotation_environment(
    annotations: &[String],
    work: &mut WorkLimit,
) -> Result<bool, SourceTypesError> {
    work.charge(annotations.len())?;
    let mut required = false;
    for annotation in annotations {
        work.text(annotation)?;
        required |= !matches!(
            annotation.trim(),
            "@{}" | "&{}" | "&mut" | "&^mut" | "&closure" | "&capture"
        );
    }
    Ok(required)
}

fn import_parts<'a>(
    parts: impl IntoIterator<Item = &'a SourceSchema>,
    builder: &mut SourceBuilder,
    work: &mut WorkLimit,
) -> Result<Vec<SourceTypeId>, SourceTypesError> {
    let parts = parts.into_iter();
    let initial = parts.size_hint().0;
    work.charge(
        initial
            .checked_add(1)
            .ok_or(SourceTypesError::BudgetExceeded)?,
    )?;
    let mut roots = Vec::new();
    roots
        .try_reserve_exact(initial)
        .map_err(|_| SourceTypesError::BudgetExceeded)?;
    for part in parts {
        // One writer can publish several immutable prefixes. Equal arena IDs
        // do not make a later root visible in the first part's snapshot.
        // The builder's full-ID import memo already preserves shared edges.
        work.charge(2)?;
        let root = part.copy_into(builder, work)?;
        if roots.len() == roots.capacity() {
            let additional = roots.capacity().max(4);
            work.charge(
                roots
                    .len()
                    .checked_add(additional)
                    .ok_or(SourceTypesError::BudgetExceeded)?,
            )?;
            roots
                .try_reserve_exact(additional)
                .map_err(|_| SourceTypesError::BudgetExceeded)?;
        }
        roots.push(root);
    }
    Ok(roots)
}

fn freeze(
    builder: SourceBuilder,
    root: SourceTypeId,
    original: Option<TypeExprId>,
    work: &mut WorkLimit,
) -> Result<SourceSchema, SourceTypesError> {
    Ok(SourceSchema {
        types: builder.freeze(work)?,
        root,
        original,
    })
}

impl SourceSchema {
    /// Only actual transparent graph edges expose a scalar representation.
    /// Nominal or unresolved spelling is never interpreted as a scalar name.
    pub(crate) fn scalar_representation(
        &self,
        work: &mut WorkLimit,
    ) -> Result<Option<SourceScalar>, SourceTypesError> {
        super::super::reception::complete(&self.types, self.root, work)?;
        let root = self.read_root(work)?;
        Ok(match self.types.get(root)? {
            SourceNode::Scalar(scalar) => Some(*scalar),
            SourceNode::Binder(_)
            | SourceNode::KeyProjection { .. }
            | SourceNode::OpaqueName { .. }
            | SourceNode::StaticValue(_)
            | SourceNode::OpaqueComputation(_)
            | SourceNode::Unresolved { .. } => return Err(SourceTypesError::Unresolved),
            _ => None,
        })
    }

    /// Read one original root UID. Immutable qualification is a real shell and
    /// is not discarded when deciding whether this is a bare binder receiver.
    pub(crate) fn bare_binder_identity(
        &self,
        work: &mut WorkLimit,
    ) -> Result<Option<String>, SourceTypesError> {
        let root = self.types.unalias(self.root, work)?;
        let node = self.types.get(root)?;
        node.charge(work)?;
        Ok(match node {
            SourceNode::Binder(identity) => Some(identity.clone()),
            _ => None,
        })
    }

    /// Select an already present UID node, preserving its actual arena and
    /// interpretation. Absence is not a theorem about an unresolved type.
    pub(crate) fn binder_view(
        &self,
        identity: &str,
        work: &mut WorkLimit,
    ) -> Result<Option<Self>, SourceTypesError> {
        work.text(identity)?;
        let mut selected = None;
        for id in self.types.reachable([self.root], work)? {
            work.charge(1)?;
            if matches!(self.types.get(id)?, SourceNode::Binder(actual) if actual == identity)
                && selected.is_none()
            {
                selected = Some(id);
            }
        }
        selected
            .map(|root| Self::frozen_view(&self.types, root, self.original, work))
            .transpose()
    }

    /// Topology only: an actual backedge is different from a shared acyclic
    /// child. Complete the bounded walk even after finding a cycle so another
    /// bad edge or exhausted budget cannot be hidden behind that backedge.
    #[cfg(test)]
    pub(crate) fn has_cycles(&self, work: &mut WorkLimit) -> Result<bool, SourceTypesError> {
        work.charge(1)?;
        let mut pending = vec![(self.root, false)];
        let mut visited = BTreeSet::new();
        let mut active = BTreeSet::new();
        let mut cyclic = false;
        while let Some((id, leaving)) = pending.pop() {
            work.charge(1)?;
            if leaving {
                active.remove(&id);
                visited.insert(id);
                continue;
            }
            if active.contains(&id) {
                cyclic = true;
                continue;
            }
            if visited.contains(&id) {
                continue;
            }
            let node = self.types.get(id)?;
            node.charge(work)?;
            let children = match node {
                SourceNode::GenericBuiltin(_)
                | SourceNode::NullaryConstructor { .. }
                | SourceNode::Scalar(_)
                | SourceNode::Nominal(_)
                | SourceNode::StaticValue(_)
                | SourceNode::Binder(_) => 0,
                SourceNode::OpaqueComputation(_) | SourceNode::Unresolved { .. } => {
                    return Err(SourceTypesError::Unresolved);
                }
                SourceNode::Array { .. }
                | SourceNode::Alias { .. }
                | SourceNode::KeyProjection { .. } => 1,
                SourceNode::Map { .. } => 2,
                SourceNode::Tuple(items)
                | SourceNode::Container {
                    arguments: items, ..
                }
                | SourceNode::OpaqueName {
                    arguments: items, ..
                } => items.len(),
                SourceNode::Record { fields, row } => fields.len() + usize::from(row.is_some()),
                SourceNode::Callable {
                    parameters,
                    row_identity,
                    ..
                } => {
                    parameters.len()
                        + 1
                        + row_identity.as_ref().map_or(0, |row| row.parameters.len())
                }
            };
            work.charge(1 + children)?;
            active.insert(id);
            pending.push((id, true));
            pending.extend(
                node.children()
                    .into_iter()
                    .rev()
                    .map(|child| (child, false)),
            );
        }
        Ok(cyclic)
    }

    pub(crate) fn has_callable(&self, work: &mut WorkLimit) -> Result<bool, SourceTypesError> {
        let mut found = false;
        for id in self.types.reachable([self.root], work)? {
            work.charge(1)?;
            match self.types.get(id)? {
                SourceNode::Callable { .. } | SourceNode::GenericBuiltin(_) => found = true,
                SourceNode::Unresolved { .. } | SourceNode::OpaqueComputation(_) => {
                    return Err(SourceTypesError::Unresolved);
                }
                _ => {}
            }
        }
        Ok(found)
    }

    pub(crate) fn binder_identities(
        &self,
        work: &mut WorkLimit,
    ) -> Result<BTreeSet<String>, SourceTypesError> {
        let mut result = BTreeSet::new();
        for id in self.types.reachable([self.root], work)? {
            work.charge(1)?;
            if let SourceNode::Binder(identity) = self.types.get(id)? {
                work.text(identity)?;
                result.insert(identity.clone());
            }
        }
        Ok(result)
    }

    pub(crate) fn with_original(&self, original: Option<TypeExprId>) -> Self {
        Self {
            types: self.types.clone(),
            root: self.root,
            original,
        }
    }

    pub(crate) fn empty_context(
        &self,
        fresh: &Construction,
        work: &mut WorkLimit,
    ) -> Result<Option<bool>, SourceTypesError> {
        work.charge(1)?;
        if !matches!(fresh, Construction::Array(items) if items.is_empty())
            && !matches!(fresh, Construction::Map(items) if items.is_empty())
        {
            return Ok(None);
        }
        super::super::reception::complete(&self.types, self.root, work)?;
        let root = self.read_root(work)?;
        Ok(match (self.types.get(root)?, fresh) {
            (SourceNode::Array { length, .. }, Construction::Array(_)) => Some(matches!(
                length,
                SourceLength::Dynamic | SourceLength::Fixed(0)
            )),
            (SourceNode::Map { .. }, Construction::Map(_)) => Some(true),
            (
                SourceNode::Binder(_)
                | SourceNode::OpaqueName { .. }
                | SourceNode::KeyProjection { .. },
                _,
            ) => {
                return Err(SourceTypesError::Unresolved);
            }
            _ => None,
        })
    }

    pub(crate) fn sensitivity(&self, work: &mut WorkLimit) -> SourceSensitivity {
        self.types.sensitivity(self.root, work)
    }

    /// Closed scalar and structural coordinates do not depend on which frozen
    /// environment lends them. Rigid UIDs and lexical callable contracts do.
    pub(crate) fn requires_environment(
        &self,
        work: &mut WorkLimit,
    ) -> Result<bool, SourceTypesError> {
        self.environment_dependency(true, work)
    }

    /// A graph's resolved binders may be read from another capture only when
    /// their complete selections agree. Lexical contract names stay local.
    pub(crate) fn same_interpretation_in(
        &self,
        left: &FrozenEnvironment,
        right: &FrozenEnvironment,
        work: &mut WorkLimit,
    ) -> Result<bool, SourceTypesError> {
        work.charge(1)?;
        if left.is_poisoned() || right.is_poisoned() {
            return Ok(false);
        }
        if left.id() == right.id() {
            return Ok(true);
        }
        if self.requires_declaration_environment(work)? {
            return Ok(false);
        }
        for identity in self.binder_identities(work)? {
            if !super::super::reception::same_binder_selection(&identity, left, right, work)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// A declaration's own lexical names/rows remain interpreted there even
    /// after every generic UID has been substituted by an actual source view.
    pub(crate) fn requires_declaration_environment(
        &self,
        work: &mut WorkLimit,
    ) -> Result<bool, SourceTypesError> {
        self.environment_dependency(false, work)
    }

    pub(crate) fn contains_callable(&self, work: &mut WorkLimit) -> Result<bool, SourceTypesError> {
        for id in self.types.reachable([self.root], work)? {
            work.charge(1)?;
            if matches!(self.types.get(id)?, SourceNode::Callable { .. }) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn environment_dependency(
        &self,
        binders: bool,
        work: &mut WorkLimit,
    ) -> Result<bool, SourceTypesError> {
        let mut required = false;
        for id in self.types.reachable([self.root], work)? {
            work.charge(1)?;
            match self.types.get(id)? {
                SourceNode::Binder(_) => required |= binders,
                SourceNode::OpaqueName { declaration, .. } => required |= declaration.is_none(),
                SourceNode::KeyProjection { .. } => required = true,
                SourceNode::OpaqueComputation(_) | SourceNode::Unresolved { .. } => {
                    return Err(SourceTypesError::Unresolved);
                }
                SourceNode::Callable { annotations, .. } => {
                    required |= annotation_environment(annotations, work)?;
                }
                _ => {}
            }
        }
        Ok(required)
    }

    /// The root callable owns these contracts; parameter/result dependency is
    /// accounted for separately by the caller when it combines source views.
    pub(crate) fn callable_contract_requires_environment(
        &self,
        work: &mut WorkLimit,
    ) -> Result<bool, SourceTypesError> {
        let root = self.read_root(work)?;
        match self.types.get(root)? {
            SourceNode::Callable { annotations, .. } => annotation_environment(annotations, work),
            SourceNode::GenericBuiltin(_) => Ok(false),
            SourceNode::Binder(_)
            | SourceNode::KeyProjection { .. }
            | SourceNode::OpaqueName { .. }
            | SourceNode::OpaqueComputation(_)
            | SourceNode::Unresolved { .. } => Err(SourceTypesError::Unresolved),
            _ => Err(SourceTypesError::MissingProjection),
        }
    }

    pub(crate) fn receive_schema(
        &self,
        actual: &Self,
        fresh: Option<&Construction>,
        work: &mut WorkLimit,
    ) -> Result<bool, SourceTypesError> {
        super::super::reception::receive_from(
            &self.types,
            self.root,
            &actual.types,
            actual.root,
            fresh,
            work,
        )
    }

    /// Receiving under each operand's original lexical interpretation.
    pub(crate) fn receive_schema_in(
        &self,
        actual: &Self,
        expected_environment: &FrozenEnvironment,
        actual_environment: &FrozenEnvironment,
        fresh: Option<&Construction>,
        work: &mut WorkLimit,
    ) -> Result<bool, SourceTypesError> {
        super::super::reception::receive_from_in(
            &self.types,
            self.root,
            &actual.types,
            actual.root,
            fresh,
            Some((expected_environment, actual_environment)),
            work,
        )
    }

    /// Copy authority is checked elsewhere. This changes only the outer type
    /// qualification, preserving every recursive edge and original annotation.
    pub(crate) fn copy_view(
        &self,
        mode: CopyMode,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        work.charge(1)?;
        let root = self.types.unalias(self.root, work)?;
        let node = self.types.get(root)?;
        node.charge(work)?;
        let immutable = match node {
            SourceNode::Container {
                kind: SourceContainer::Immutable,
                arguments,
            } => {
                if arguments.len() != 1 {
                    return Err(SourceTypesError::InvalidContainer);
                }
                Some(arguments[0])
            }
            _ => None,
        };
        match (mode, immutable) {
            (CopyMode::Mutable, Some(root)) => {
                Self::frozen_view(&self.types, root, self.original, work)
            }
            (CopyMode::Immutable, None) => Self::container(
                SourceContainer::Immutable,
                std::slice::from_ref(self),
                self.original,
                work,
            ),
            _ => Ok(self.clone()),
        }
    }

    pub(crate) fn tuple(
        items: &[Self],
        original: Option<TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        work.charge(1 + items.len())?;
        let mut builder = SourceBuilder::new()?;
        let items = import_parts(items, &mut builder, work)?;
        let node = if items.is_empty() {
            SourceNode::Scalar(SourceScalar::Unit)
        } else {
            SourceNode::Tuple(items)
        };
        let root = builder.insert(node, work)?;
        freeze(builder, root, original, work)
    }

    pub(crate) fn array(
        length: SourceLength,
        element: &Self,
        original: Option<TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        work.charge(1)?;
        let mut builder = SourceBuilder::new()?;
        let parts = import_parts([element], &mut builder, work)?;
        let root = builder.insert(
            SourceNode::Array {
                length,
                element: parts[0],
            },
            work,
        )?;
        freeze(builder, root, original, work)
    }

    pub(crate) fn map(
        key: &Self,
        value: &Self,
        original: Option<TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        work.charge(1)?;
        let mut builder = SourceBuilder::new()?;
        let parts = import_parts([key, value], &mut builder, work)?;
        let root = builder.insert(
            SourceNode::Map {
                key: parts[0],
                value: parts[1],
            },
            work,
        )?;
        freeze(builder, root, original, work)
    }

    pub(crate) fn record(
        fields: &[(String, bool, Self)],
        row: Option<&Self>,
        original: Option<TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        work.charge(1 + fields.len())?;
        for (label, _, _) in fields {
            work.text(label)?;
        }
        let mut builder = SourceBuilder::new()?;
        let parts = import_parts(
            fields.iter().map(|(_, _, schema)| schema).chain(row),
            &mut builder,
            work,
        )?;
        let root = builder.insert(
            SourceNode::Record {
                fields: fields
                    .iter()
                    .zip(&parts)
                    .map(|((label, mutable, _), value)| SourceField {
                        label: label.clone(),
                        mutable: *mutable,
                        value: *value,
                    })
                    .collect(),
                row: row.map(|_| parts[fields.len()]),
            },
            work,
        )?;
        freeze(builder, root, original, work)
    }

    pub(crate) fn container(
        kind: SourceContainer,
        arguments: &[Self],
        original: Option<TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        work.charge(1 + arguments.len())?;
        let arity = if kind == SourceContainer::Result {
            2
        } else {
            1
        };
        if arguments.len() != arity {
            return Err(SourceTypesError::InvalidContainer);
        }
        let mut builder = SourceBuilder::new()?;
        let arguments = import_parts(arguments, &mut builder, work)?;
        let root = builder.insert(SourceNode::Container { kind, arguments }, work)?;
        freeze(builder, root, original, work)
    }

    pub(crate) fn callable(
        parameters: &[(ParameterMode, Self)],
        result: &Self,
        annotations: &[String],
        original: Option<TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        Self::callable_original(parameters, result, annotations, None, original, work)
    }

    /// The row reference must come from the authenticated original-header
    /// builder. Its dependency edges are ordinary graph substitution inputs.
    pub(crate) fn callable_original(
        parameters: &[(ParameterMode, Self)],
        result: &Self,
        annotations: &[String],
        row_identity: Option<&CallableRowIdentity<Self>>,
        original: Option<TypeExprId>,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        work.charge(
            1 + parameters.len()
                + annotations.len()
                + row_identity.map_or(0, |row| row.parameters.len() + 1),
        )?;
        for annotation in annotations {
            work.text(annotation)?;
        }
        let mut builder = SourceBuilder::new()?;
        let parts = import_parts(
            parameters
                .iter()
                .map(|(_, schema)| schema)
                .chain([result])
                .chain(
                    row_identity
                        .into_iter()
                        .flat_map(|row| row.parameters.iter().map(|(_, schema)| schema)),
                ),
            &mut builder,
            work,
        )?;
        let root = builder.insert(
            SourceNode::Callable {
                parameters: parameters
                    .iter()
                    .zip(&parts)
                    .map(|((mode, _), value)| (*mode, *value))
                    .collect(),
                result: parts[parameters.len()],
                annotations: annotations.to_vec(),
                row_identity: row_identity.map(|row| CallableRowIdentity {
                    origin: row.origin,
                    parameters: row
                        .parameters
                        .iter()
                        .zip(&parts[parameters.len() + 1..])
                        .map(|((id, _), root)| (*id, *root))
                        .collect(),
                }),
            },
            work,
        )?;
        freeze(builder, root, original, work)
    }

    /// Resolve only reachable selections. Unknown unused inputs neither replace
    /// a binder nor force their unrelated graphs into this resulting schema.
    pub(crate) fn substitute(
        &self,
        selected: &BTreeMap<String, Self>,
        work: &mut WorkLimit,
    ) -> Result<Self, SourceTypesError> {
        work.charge(1)?;
        let mut parts = vec![self];
        let mut pending = vec![self];
        let mut seen = BTreeSet::new();
        let mut names = Vec::new();
        while let Some(schema) = pending.pop() {
            work.charge(1)?;
            for id in schema.types.reachable([schema.root], work)? {
                if let SourceNode::Binder(identity) = schema.types.get(id)? {
                    work.text(identity)?;
                    work.charge(1)?;
                    if !seen.insert(identity.clone()) {
                        continue;
                    }
                    if let Some(replacement) = selected.get(identity) {
                        work.charge(3)?;
                        parts.push(replacement);
                        pending.push(replacement);
                        names.push(identity.clone());
                    }
                }
            }
        }
        let mut builder = SourceBuilder::new()?;
        let roots = import_parts(parts, &mut builder, work)?;
        work.charge(names.len())?;
        let replacements = names
            .into_iter()
            .zip(roots.iter().skip(1).copied())
            .collect();
        let types = builder.freeze(work)?;
        let result = types.substitute(roots[0], &replacements, work)?;
        Ok(Self {
            types: result.types,
            root: result.root,
            original: self.original,
        })
    }

    /// A structural read can see through immutable qualification. It does not
    /// remove that qualification from any stored value or grant write access.
    fn read_root(&self, work: &mut WorkLimit) -> Result<SourceTypeId, SourceTypesError> {
        let mut root = self.root;
        let mut seen = BTreeSet::new();
        loop {
            work.charge(1)?;
            root = self.types.unalias(root, work)?;
            if !seen.insert(root) {
                return Err(SourceTypesError::AliasCycle);
            }
            let node = self.types.get(root)?;
            node.charge(work)?;
            match node {
                SourceNode::Container {
                    kind: SourceContainer::Immutable,
                    arguments,
                } => {
                    if arguments.len() != 1 {
                        return Err(SourceTypesError::InvalidContainer);
                    }
                    root = arguments[0];
                }
                _ => return Ok(root),
            }
        }
    }

    /// Flatten only the row spine. Field views and a final rigid tail retain
    /// their exact nodes in this original arena, including recursive members.
    pub(crate) fn record_parts(
        &self,
        work: &mut WorkLimit,
    ) -> Result<Option<RecordParts>, SourceTypesError> {
        super::super::reception::complete(&self.types, self.root, work)?;
        let mut cursor = self.read_root(work)?;
        let mut seen = BTreeSet::new();
        let mut fields = BTreeMap::new();
        let tail = loop {
            work.charge(1)?;
            cursor = self.types.unalias(cursor, work)?;
            if !seen.insert(cursor) {
                return Err(SourceTypesError::RowCycle);
            }
            let node = self.types.get(cursor)?;
            node.charge(work)?;
            match node {
                SourceNode::Record { fields: next, row } => {
                    for field in next {
                        work.charge(1)?;
                        if fields
                            .insert(field.label.as_str(), (field.mutable, field.value))
                            .is_some()
                        {
                            return Err(SourceTypesError::DuplicateField);
                        }
                    }
                    let Some(row) = row else { break None };
                    cursor = *row;
                }
                SourceNode::Binder(_) if seen.len() > 1 => {
                    break Some(Self::frozen_view(&self.types, cursor, self.original, work)?);
                }
                SourceNode::Binder(_)
                | SourceNode::KeyProjection { .. }
                | SourceNode::OpaqueName { .. }
                | SourceNode::StaticValue(_)
                | SourceNode::OpaqueComputation(_)
                | SourceNode::Unresolved { .. } => return Err(SourceTypesError::Unresolved),
                _ if seen.len() == 1 => return Ok(None),
                _ => return Err(SourceTypesError::Unresolved),
            }
        };
        work.charge(fields.len())?;
        let fields = fields
            .into_iter()
            .map(|(label, (mutable, root))| {
                work.text(label)?;
                Ok((
                    label.to_owned(),
                    mutable,
                    Self::frozen_view(&self.types, root, self.original, work)?,
                ))
            })
            .collect::<Result<_, SourceTypesError>>()?;
        Ok(Some((fields, tail)))
    }

    pub(crate) fn callable_parts(
        &self,
        work: &mut WorkLimit,
    ) -> Result<Option<CallableParts>, SourceTypesError> {
        let root = self.read_root(work)?;
        match self.types.get(root)? {
            SourceNode::Callable {
                parameters, result, ..
            } => {
                work.charge(parameters.len())?;
                let parameters = parameters
                    .iter()
                    .map(|(mode, root)| {
                        Self::frozen_view(&self.types, *root, self.original, work)
                            .map(|schema| (*mode, schema))
                    })
                    .collect::<Result<_, _>>()?;
                Ok(Some((
                    parameters,
                    Self::frozen_view(&self.types, *result, self.original, work)?,
                )))
            }
            SourceNode::Binder(_)
            | SourceNode::KeyProjection { .. }
            | SourceNode::OpaqueName { .. }
            | SourceNode::OpaqueComputation(_)
            | SourceNode::Unresolved { .. } => Err(SourceTypesError::Unresolved),
            _ => Ok(None),
        }
    }

    pub(crate) fn tuple_parts(
        &self,
        work: &mut WorkLimit,
    ) -> Result<Option<Vec<Self>>, SourceTypesError> {
        let root = self.read_root(work)?;
        match self.types.get(root)? {
            SourceNode::Scalar(SourceScalar::Unit) => Ok(Some(Vec::new())),
            SourceNode::Tuple(items) => {
                work.charge(items.len())?;
                items
                    .iter()
                    .map(|root| Self::frozen_view(&self.types, *root, self.original, work))
                    .collect::<Result<_, _>>()
                    .map(Some)
            }
            SourceNode::Binder(_)
            | SourceNode::KeyProjection { .. }
            | SourceNode::OpaqueName { .. }
            | SourceNode::OpaqueComputation(_)
            | SourceNode::Unresolved { .. } => Err(SourceTypesError::Unresolved),
            _ => Ok(None),
        }
    }

    pub(crate) fn array_parts(
        &self,
        work: &mut WorkLimit,
    ) -> Result<Option<(SourceLength, Self)>, SourceTypesError> {
        let root = self.read_root(work)?;
        match self.types.get(root)? {
            SourceNode::Array { length, element } => Ok(Some((
                *length,
                Self::frozen_view(&self.types, *element, self.original, work)?,
            ))),
            SourceNode::Binder(_)
            | SourceNode::KeyProjection { .. }
            | SourceNode::OpaqueName { .. }
            | SourceNode::OpaqueComputation(_)
            | SourceNode::Unresolved { .. } => Err(SourceTypesError::Unresolved),
            _ => Ok(None),
        }
    }

    pub(crate) fn callable_parameters(
        &self,
        work: &mut WorkLimit,
    ) -> Result<Vec<(ParameterMode, Self)>, SourceTypesError> {
        self.callable_parts(work)?
            .map(|(parameters, _)| parameters)
            .ok_or(SourceTypesError::MissingProjection)
    }

    pub(crate) fn callable_annotations(
        &self,
        work: &mut WorkLimit,
    ) -> Result<Option<Vec<String>>, SourceTypesError> {
        let root = self.read_root(work)?;
        match self.types.get(root)? {
            SourceNode::Callable { annotations, .. } => Ok(Some(annotations.clone())),
            SourceNode::Binder(_)
            | SourceNode::KeyProjection { .. }
            | SourceNode::OpaqueName { .. }
            | SourceNode::OpaqueComputation(_)
            | SourceNode::Unresolved { .. } => Err(SourceTypesError::Unresolved),
            _ => Ok(None),
        }
    }

    /// Exact opaque name/arity only. This query supplies no declaration or
    /// standard nominal identity proof; that proof belongs to the real caller.
    pub(crate) fn opaque_arguments(
        &self,
        expected: &str,
        arity: usize,
        work: &mut WorkLimit,
    ) -> Result<Option<Vec<Self>>, SourceTypesError> {
        work.text(expected)?;
        let root = self.read_root(work)?;
        match self.types.get(root)? {
            SourceNode::OpaqueName {
                name, arguments, ..
            } if name == expected => {
                if arguments.len() != arity {
                    return Err(SourceTypesError::InvalidContainer);
                }
                work.charge(arguments.len())?;
                arguments
                    .iter()
                    .map(|root| Self::frozen_view(&self.types, *root, self.original, work))
                    .collect::<Result<_, _>>()
                    .map(Some)
            }
            SourceNode::Binder(_)
            | SourceNode::KeyProjection { .. }
            | SourceNode::OpaqueComputation(_)
            | SourceNode::Unresolved { .. } => Err(SourceTypesError::Unresolved),
            _ => Ok(None),
        }
    }

    pub(crate) fn record_field(
        &self,
        expected: &str,
        work: &mut WorkLimit,
    ) -> Result<Option<(bool, Self)>, SourceTypesError> {
        work.text(expected)?;
        let mut cursor = self.read_root(work)?;
        let mut seen = BTreeSet::new();
        let mut labels = BTreeSet::new();
        let mut selected = None;
        loop {
            work.charge(1)?;
            cursor = self.types.unalias(cursor, work)?;
            if !seen.insert(cursor) {
                return Err(SourceTypesError::RowCycle);
            }
            let node = self.types.get(cursor)?;
            node.charge(work)?;
            let SourceNode::Record { fields, row } = node else {
                return match node {
                    SourceNode::Binder(_) | SourceNode::OpaqueName { .. } => {
                        selected.ok_or(SourceTypesError::Unresolved).map(Some)
                    }
                    SourceNode::KeyProjection { .. }
                    | SourceNode::OpaqueComputation(_)
                    | SourceNode::Unresolved { .. } => Err(SourceTypesError::Unresolved),
                    _ if seen.len() == 1 => Ok(None),
                    _ => Err(SourceTypesError::Unresolved),
                };
            };
            for field in fields {
                work.charge(1)?;
                if !labels.insert(field.label.as_str()) {
                    return Err(SourceTypesError::DuplicateField);
                }
                if field.label == expected {
                    selected = Some((
                        field.mutable,
                        Self::frozen_view(&self.types, field.value, self.original, work)?,
                    ));
                }
            }
            let Some(row) = row else { return Ok(selected) };
            cursor = *row;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::effect_identity::{ArgumentKey, StaticBinderSort};

    fn scalar(kind: SourceScalar) -> SourceSchema {
        let mut work = WorkLimit::new(128);
        let mut builder = SourceBuilder::new().unwrap();
        let root = builder.insert(SourceNode::Scalar(kind), &mut work).unwrap();
        freeze(builder, root, Some(TypeExprId(17)), &mut work).unwrap()
    }

    fn prefix_parts() -> (SourceSchema, SourceSchema) {
        let mut writer = SourceBuilder::new().unwrap();
        let mut work = WorkLimit::new(4096);
        let recursive = writer.reserve(&mut work).unwrap();
        let scalar = writer
            .insert(SourceNode::Scalar(SourceScalar::I32), &mut work)
            .unwrap();
        let inner = writer
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(3),
                    element: scalar,
                },
                &mut work,
            )
            .unwrap();
        let empty = writer
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(0),
                    element: inner,
                },
                &mut work,
            )
            .unwrap();
        writer
            .define(
                recursive,
                SourceNode::Tuple(vec![recursive, empty]),
                &mut work,
            )
            .unwrap();
        let older = SourceSchema {
            types: writer.snapshot(&mut work).unwrap(),
            root: recursive,
            original: Some(TypeExprId(17)),
        };
        let text = writer
            .insert(SourceNode::Scalar(SourceScalar::Str), &mut work)
            .unwrap();
        let later = writer
            .insert(
                SourceNode::Tuple(vec![recursive, recursive, text]),
                &mut work,
            )
            .unwrap();
        let newer = SourceSchema {
            types: writer.snapshot(&mut work).unwrap(),
            root: later,
            original: Some(TypeExprId(18)),
        };
        (older, newer)
    }

    #[test]
    fn graph_composition_keeps_each_actual_prefix_snapshot_and_shared_cycles() {
        let (older, newer) = prefix_parts();
        assert_eq!(older.root.arena, newer.root.arena);
        assert_eq!(
            older.types.get(newer.root),
            Err(SourceTypesError::MissingNode)
        );
        for reversed in [false, true] {
            let parts = if reversed {
                [newer.clone(), older.clone()]
            } else {
                [older.clone(), newer.clone()]
            };
            let combined = SourceSchema::container(
                SourceContainer::Result,
                &parts,
                None,
                &mut WorkLimit::new(4096),
            )
            .unwrap();
            let SourceNode::Container { arguments, .. } =
                combined.types.get(combined.root).unwrap()
            else {
                panic!()
            };
            let (old, new) = if reversed {
                (arguments[1], arguments[0])
            } else {
                (arguments[0], arguments[1])
            };
            let SourceNode::Tuple(old_children) = combined.types.get(old).unwrap() else {
                panic!()
            };
            assert_eq!(old_children[0], old);
            let SourceNode::Tuple(new_children) = combined.types.get(new).unwrap() else {
                panic!()
            };
            assert_eq!(&new_children[..2], &[old, old]);
            assert_eq!(
                combined.types.get(new_children[2]),
                Ok(&SourceNode::Scalar(SourceScalar::Str))
            );
            let SourceNode::Array {
                length: SourceLength::Fixed(0),
                element,
            } = combined.types.get(old_children[1]).unwrap()
            else {
                panic!()
            };
            let SourceNode::Array {
                length: SourceLength::Fixed(3),
                element,
            } = combined.types.get(*element).unwrap()
            else {
                panic!()
            };
            assert_eq!(
                combined.types.get(*element),
                Ok(&SourceNode::Scalar(SourceScalar::I32))
            );
            let old_view = SourceSchema::frozen_view(
                &combined.types,
                old,
                older.original,
                &mut WorkLimit::new(4096),
            )
            .unwrap();
            assert_eq!(
                old_view.equivalent(&older, &mut WorkLimit::new(4096)),
                Ok(true)
            );
        }
        let duplicated = SourceSchema::container(
            SourceContainer::Result,
            &[older.clone(), older],
            None,
            &mut WorkLimit::new(4096),
        )
        .unwrap();
        let SourceNode::Container { arguments, .. } =
            duplicated.types.get(duplicated.root).unwrap()
        else {
            panic!()
        };
        assert_eq!(arguments[0], arguments[1]);
    }

    #[test]
    fn graph_composition_preflights_foreign_roots_and_exact_snapshot_work() {
        let (older, newer) = prefix_parts();
        let invalid_old = SourceSchema {
            types: older.types.clone(),
            root: newer.root,
            original: None,
        };
        // The later root is already imported by the first part: a memo hit
        // must still reject its absence from the second part's own snapshot.
        assert!(matches!(
            SourceSchema::container(
                SourceContainer::Result,
                &[newer.clone(), invalid_old],
                None,
                &mut WorkLimit::new(4096)
            ),
            Err(SourceTypesError::MissingNode)
        ));
        let foreign = scalar(SourceScalar::Bool);
        let invalid_foreign = SourceSchema {
            types: older.types.clone(),
            root: foreign.root,
            original: None,
        };
        assert!(matches!(
            SourceSchema::container(
                SourceContainer::Result,
                &[foreign, invalid_foreign],
                None,
                &mut WorkLimit::new(4096)
            ),
            Err(SourceTypesError::ForeignIdentity)
        ));
        let parts = [older, newer];
        let mut work = WorkLimit::new(4096);
        SourceSchema::container(SourceContainer::Result, &parts, None, &mut work).unwrap();
        let used = 4096 - work.remaining();
        let mut exact = WorkLimit::new(used);
        SourceSchema::container(SourceContainer::Result, &parts, None, &mut exact).unwrap();
        assert_eq!(exact.remaining(), 0);
        for short in [0, used - 1] {
            assert!(matches!(
                SourceSchema::container(
                    SourceContainer::Result,
                    &parts,
                    None,
                    &mut WorkLimit::new(short)
                ),
                Err(SourceTypesError::BudgetExceeded)
            ));
        }
    }

    #[test]
    fn scalar_representation_uses_graph_edges_and_rejects_poison_cycles_and_spelling() {
        let mut work = WorkLimit::new(4096);
        let mut builder = SourceBuilder::new().unwrap();
        let leaf = builder
            .insert(SourceNode::Scalar(SourceScalar::I8), &mut work)
            .unwrap();
        let alias = builder
            .insert(
                SourceNode::Alias {
                    declaration: "Narrow".into(),
                    target: leaf,
                },
                &mut work,
            )
            .unwrap();
        let shell = builder
            .insert(
                SourceNode::Container {
                    kind: SourceContainer::Immutable,
                    arguments: vec![alias],
                },
                &mut work,
            )
            .unwrap();
        let wrapped = freeze(builder, shell, None, &mut work).unwrap();
        assert_eq!(
            wrapped.scalar_representation(&mut WorkLimit::new(4096)),
            Ok(Some(SourceScalar::I8))
        );
        assert!(matches!(
            wrapped.scalar_representation(&mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        let array = SourceSchema::array(SourceLength::Dynamic, &wrapped, None, &mut work).unwrap();
        assert_eq!(
            array.scalar_representation(&mut WorkLimit::new(4096)),
            Ok(None)
        );
        let mut builder = SourceBuilder::new().unwrap();
        let root = builder
            .insert(
                SourceNode::OpaqueName {
                    declaration: None,
                    name: "i8".into(),
                    arguments: vec![],
                },
                &mut work,
            )
            .unwrap();
        let opaque = freeze(builder, root, None, &mut work).unwrap();
        assert_eq!(
            opaque.scalar_representation(&mut WorkLimit::new(4096)),
            Err(SourceTypesError::Unresolved)
        );
        let poison =
            SourceSchema::import(&ArgumentKey::Closed("unfinished".into()), None, &mut work)
                .unwrap();
        let poisoned_array =
            SourceSchema::array(SourceLength::Dynamic, &poison, None, &mut work).unwrap();
        assert_eq!(
            poisoned_array.scalar_representation(&mut WorkLimit::new(4096)),
            Err(SourceTypesError::Unresolved)
        );
        let mut builder = SourceBuilder::new().unwrap();
        let root = builder.reserve(&mut work).unwrap();
        builder
            .define(
                root,
                SourceNode::Container {
                    kind: SourceContainer::Immutable,
                    arguments: vec![root],
                },
                &mut work,
            )
            .unwrap();
        let cyclic = freeze(builder, root, None, &mut work).unwrap();
        assert_eq!(
            cyclic.scalar_representation(&mut WorkLimit::new(4096)),
            Err(SourceTypesError::AliasCycle)
        );
        let mut builder = SourceBuilder::new().unwrap();
        let root = builder
            .insert(
                SourceNode::Nominal(super::super::super::standard_data::Nominal::ProcessError),
                &mut work,
            )
            .unwrap();
        let nominal = freeze(builder, root, None, &mut work).unwrap();
        assert_eq!(
            nominal.scalar_representation(&mut WorkLimit::new(4096)),
            Ok(None)
        );
    }

    #[test]
    fn record_parts_reject_duplicate_fields_and_circular_or_poisoned_rows() {
        let mut work = WorkLimit::new(16384);
        let inner = SourceSchema::record(
            &[("same".into(), false, scalar(SourceScalar::Int))],
            None,
            None,
            &mut work,
        )
        .unwrap();
        let duplicate = SourceSchema::record(
            &[("same".into(), true, scalar(SourceScalar::Bool))],
            Some(&inner),
            None,
            &mut work,
        )
        .unwrap();
        assert_eq!(
            duplicate.record_parts(&mut work).unwrap_err(),
            SourceTypesError::DuplicateField
        );
        assert_eq!(
            duplicate
                .record_remainder(&BTreeSet::new(), &mut work)
                .unwrap_err(),
            SourceTypesError::DuplicateField
        );
        let mut builder = SourceBuilder::new().unwrap();
        let root = builder.reserve(&mut work).unwrap();
        builder
            .define(
                root,
                SourceNode::Record {
                    fields: vec![],
                    row: Some(root),
                },
                &mut work,
            )
            .unwrap();
        let cycle = freeze(builder, root, None, &mut work).unwrap();
        assert_eq!(
            cycle.record_parts(&mut work).unwrap_err(),
            SourceTypesError::RowCycle
        );
        for poison in [
            SourceNode::OpaqueComputation("unknown row".into()),
            SourceNode::Unresolved {
                description: "missing row".into(),
                arguments: vec![],
            },
            SourceNode::OpaqueName {
                declaration: None,
                name: "unresolved nominal row".into(),
                arguments: vec![],
            },
            SourceNode::Scalar(SourceScalar::Int),
        ] {
            let mut builder = SourceBuilder::new().unwrap();
            let root = builder.insert(poison, &mut work).unwrap();
            let row = freeze(builder, root, None, &mut work).unwrap();
            let record = SourceSchema::record(&[], Some(&row), None, &mut work).unwrap();
            assert_eq!(
                record.record_parts(&mut work).unwrap_err(),
                SourceTypesError::Unresolved
            );
        }
        assert!(
            scalar(SourceScalar::Int)
                .record_parts(&mut work)
                .unwrap()
                .is_none()
        );
        assert!(matches!(
            binder("actual:Unknown").record_parts(&mut work),
            Err(SourceTypesError::Unresolved)
        ));
        let poison = SourceSchema::import(
            &ArgumentKey::Closed("unknown element".into()),
            None,
            &mut work,
        )
        .unwrap();
        let incomplete =
            SourceSchema::array(SourceLength::Dynamic, &poison, None, &mut work).unwrap();
        assert!(matches!(
            incomplete.record_parts(&mut work),
            Err(SourceTypesError::Unresolved)
        ));
    }

    #[test]
    fn record_parts_keep_recursive_members_as_original_graph_views() {
        let source = recursive(3);
        let mut work = WorkLimit::new(4096);
        let (fields, tail) = source.record_parts(&mut work).unwrap().unwrap();
        assert!(tail.is_none());
        assert_eq!(fields[0].0, "again");
        assert_eq!(fields[0].2.root_id(), source.root_id());
        assert_eq!(fields[0].2.original(), source.original());
        assert_eq!(fields[1].0, "empty");
        assert!(fields[1].1);
        let (length, inner) = fields[1].2.array_parts(&mut work).unwrap().unwrap();
        assert_eq!(length, SourceLength::Fixed(0));
        assert_eq!(
            inner.array_parts(&mut work).unwrap().unwrap().0,
            SourceLength::Fixed(3)
        );
        assert!(source.key().is_err());
        let remainder = source
            .record_remainder(&BTreeSet::from(["empty".into()]), &mut work)
            .unwrap();
        let (remaining, _) = remainder.record_parts(&mut work).unwrap().unwrap();
        assert_eq!(remaining[0].0, "again");
        assert!(remaining[0].2.equivalent(&source, &mut work).unwrap());
    }

    #[test]
    fn a_known_record_field_cannot_hide_a_poisoned_row() {
        for poison in [
            SourceNode::OpaqueComputation("unevaluated row".into()),
            SourceNode::Unresolved {
                description: "unknown row".into(),
                arguments: vec![],
            },
        ] {
            let mut work = WorkLimit::new(4096);
            let mut builder = SourceBuilder::new().unwrap();
            let root = builder.insert(poison, &mut work).unwrap();
            let row = freeze(builder, root, None, &mut work).unwrap();
            let record = SourceSchema::record(
                &[("known".into(), false, scalar(SourceScalar::Int))],
                Some(&row),
                None,
                &mut work,
            )
            .unwrap();
            assert_eq!(
                record.record_field("known", &mut work).unwrap_err(),
                SourceTypesError::Unresolved
            );
            assert_eq!(
                record.record_field("missing", &mut work).unwrap_err(),
                SourceTypesError::Unresolved
            );
        }
    }

    #[test]
    fn callable_contract_environment_excludes_parameter_and_result_dependencies() {
        let mut work = WorkLimit::new(4096);
        let opaque = SourceSchema::import(
            &ArgumentKey::Name {
                name: "OriginalNominal".into(),
                arguments: vec![],
            },
            None,
            &mut work,
        )
        .unwrap();
        let callable = SourceSchema::callable(
            &[(ParameterMode::Read, opaque.clone())],
            &opaque,
            &[],
            None,
            &mut work,
        )
        .unwrap();
        assert!(
            callable
                .requires_declaration_environment(&mut work)
                .unwrap()
        );
        assert!(
            !callable
                .callable_contract_requires_environment(&mut work)
                .unwrap()
        );
        let captured = SourceSchema::callable(
            &[],
            &scalar(SourceScalar::Unit),
            &["&{STATE}".into()],
            None,
            &mut work,
        )
        .unwrap();
        assert!(
            captured
                .callable_contract_requires_environment(&mut work)
                .unwrap()
        );
        assert_eq!(
            captured.callable_contract_requires_environment(&mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        );
    }

    fn recursive(extent: u64) -> SourceSchema {
        let mut work = WorkLimit::new(4096);
        let mut builder = SourceBuilder::new().unwrap();
        let root = builder.reserve(&mut work).unwrap();
        let integer = builder
            .insert(SourceNode::Scalar(SourceScalar::Int), &mut work)
            .unwrap();
        let inner = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(extent),
                    element: integer,
                },
                &mut work,
            )
            .unwrap();
        let empty = builder
            .insert(
                SourceNode::Array {
                    length: SourceLength::Fixed(0),
                    element: inner,
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
                            label: "again".into(),
                            mutable: false,
                            value: root,
                        },
                        SourceField {
                            label: "empty".into(),
                            mutable: true,
                            value: empty,
                        },
                    ],
                    row: None,
                },
                &mut work,
            )
            .unwrap();
        freeze(builder, root, Some(TypeExprId(29)), &mut work).unwrap()
    }

    fn binder(identity: &str) -> SourceSchema {
        SourceSchema::import(
            &ArgumentKey::Binder {
                identity: identity.into(),
                sort: StaticBinderSort::Type,
            },
            None,
            &mut WorkLimit::new(128),
        )
        .unwrap()
    }

    #[test]
    fn root_uid_queries_do_not_compare_distinct_binders_or_strip_immutable_shells() {
        let caller = binder("caller:U");
        assert_eq!(
            caller
                .bare_binder_identity(&mut WorkLimit::new(128))
                .unwrap(),
            Some("caller:U".into())
        );
        assert_eq!(
            binder("callee:T")
                .bare_binder_identity(&mut WorkLimit::new(128))
                .unwrap(),
            Some("callee:T".into())
        );
        let immutable = caller
            .copy_view(CopyMode::Immutable, &mut WorkLimit::new(4096))
            .unwrap();
        assert_eq!(
            immutable
                .bare_binder_identity(&mut WorkLimit::new(128))
                .unwrap(),
            None
        );
        let mut work = WorkLimit::new(4096);
        let mut builder = SourceBuilder::new().unwrap();
        let root = caller.copy_into(&mut builder, &mut work).unwrap();
        let alias = builder
            .insert(
                SourceNode::Alias {
                    declaration: "original-root".into(),
                    target: root,
                },
                &mut work,
            )
            .unwrap();
        let alias = freeze(builder, alias, caller.original(), &mut work).unwrap();
        assert_eq!(
            alias
                .bare_binder_identity(&mut WorkLimit::new(128))
                .unwrap(),
            Some("caller:U".into())
        );
        assert!(alias.bare_binder_identity(&mut WorkLimit::new(0)).is_err());
        let composite = SourceSchema::tuple(
            &[alias, binder("callee:T")],
            Some(TypeExprId(79)),
            &mut WorkLimit::new(4096),
        )
        .unwrap();
        let caller = composite
            .binder_view("caller:U", &mut WorkLimit::new(4096))
            .unwrap()
            .unwrap();
        assert_eq!(
            caller
                .bare_binder_identity(&mut WorkLimit::new(128))
                .unwrap(),
            Some("caller:U".into())
        );
        assert_eq!(caller.root.arena, composite.root.arena);
        assert_eq!(caller.original(), composite.original());
        assert!(
            composite
                .binder_view("unregistered:V", &mut WorkLimit::new(4096))
                .unwrap()
                .is_none()
        );
        assert!(
            composite
                .binder_view("caller:U", &mut WorkLimit::new(0))
                .is_err()
        );
    }

    #[test]
    fn topology_queries_distinguish_backedges_from_shared_diamonds_and_never_hide_errors() {
        assert!(recursive(3).has_cycles(&mut WorkLimit::new(4096)).unwrap());
        let integer = scalar(SourceScalar::Int);
        let diamond =
            SourceSchema::tuple(&[integer.clone(), integer], None, &mut WorkLimit::new(4096))
                .unwrap();
        assert!(!diamond.has_cycles(&mut WorkLimit::new(4096)).unwrap());
        assert!(recursive(3).has_cycles(&mut WorkLimit::new(0)).is_err());
        let unknown = SourceSchema::import(
            &ArgumentKey::Closed("opaque-computation".into()),
            None,
            &mut WorkLimit::new(128),
        )
        .unwrap();
        let incomplete =
            SourceSchema::tuple(&[recursive(3), unknown], None, &mut WorkLimit::new(4096)).unwrap();
        assert_eq!(
            incomplete.has_cycles(&mut WorkLimit::new(4096)),
            Err(SourceTypesError::Unresolved)
        );
    }

    #[test]
    fn graph_reception_copy_and_composition_keep_cycles_shared_roots_and_hidden_extents() {
        let input = recursive(3);
        assert_eq!(input.key(), Err(SourceTypesError::RecursiveLegacyKey));
        assert!(
            input
                .receive_schema(&recursive(3), None, &mut WorkLimit::new(4096))
                .unwrap()
        );
        assert!(
            !input
                .receive_schema(&recursive(2), None, &mut WorkLimit::new(4096))
                .unwrap()
        );
        let mutable = input
            .copy_view(CopyMode::Mutable, &mut WorkLimit::new(4096))
            .unwrap();
        assert_eq!(mutable.root, input.root);
        let immutable = input
            .copy_view(CopyMode::Immutable, &mut WorkLimit::new(4096))
            .unwrap();
        let unchanged = immutable
            .copy_view(CopyMode::Immutable, &mut WorkLimit::new(4096))
            .unwrap();
        assert_eq!(unchanged.root, immutable.root);
        let copied = immutable
            .copy_view(CopyMode::Mutable, &mut WorkLimit::new(4096))
            .unwrap();
        assert!(
            input
                .equivalent(&copied, &mut WorkLimit::new(4096))
                .unwrap()
        );
        assert_eq!(copied.original(), input.original());
        let tuple = SourceSchema::tuple(
            &[input.clone(), input.clone()],
            None,
            &mut WorkLimit::new(4096),
        )
        .unwrap();
        let SourceNode::Tuple(items) = tuple.types.get(tuple.root).unwrap() else {
            panic!()
        };
        assert_eq!(
            items[0], items[1],
            "same original arena must use one copy mapping"
        );
        let parts = tuple
            .tuple_parts(&mut WorkLimit::new(4096))
            .unwrap()
            .unwrap();
        assert_eq!(parts.len(), 2);
        assert_eq!(parts[0].root, parts[1].root);
        assert!(tuple.tuple_parts(&mut WorkLimit::new(0)).is_err());
        assert!(
            SourceSchema::tuple(
                &[input.clone(), input.clone()],
                None,
                &mut WorkLimit::new(0)
            )
            .is_err()
        );
        assert!(
            input
                .copy_view(CopyMode::Immutable, &mut WorkLimit::new(0))
                .is_err()
        );
        assert!(
            input
                .receive_schema(&input, None, &mut WorkLimit::new(0))
                .is_err()
        );
        assert!(
            input
                .equivalent(&recursive(3), &mut WorkLimit::new(4096))
                .unwrap()
        );
    }

    #[test]
    fn graph_selection_keeps_recursive_actuals_and_never_interprets_unused_unknowns() {
        let schema = SourceSchema::tuple(
            &[binder("T"), binder("T")],
            Some(TypeExprId(41)),
            &mut WorkLimit::new(4096),
        )
        .unwrap();
        let input = recursive(3);
        let unused = SourceSchema::import(
            &ArgumentKey::Closed("opaque".into()),
            None,
            &mut WorkLimit::new(128),
        )
        .unwrap();
        let selected = BTreeMap::from([("T".into(), input.clone()), ("unused".into(), unused)]);
        let result = schema
            .substitute(&selected, &mut WorkLimit::new(16384))
            .unwrap();
        assert_eq!(result.original(), schema.original());
        let first = result
            .project_steps(&[SourcePath::Tuple(0)], &mut WorkLimit::new(128))
            .unwrap();
        assert!(first.equivalent(&input, &mut WorkLimit::new(4096)).unwrap());
        let SourceNode::Tuple(items) = result.types.get(result.root).unwrap() else {
            panic!()
        };
        assert_eq!(
            result
                .types
                .unalias(items[0], &mut WorkLimit::new(128))
                .unwrap(),
            result
                .types
                .unalias(items[1], &mut WorkLimit::new(128))
                .unwrap()
        );
        assert!(
            schema
                .substitute(&selected, &mut WorkLimit::new(0))
                .is_err()
        );
        assert_eq!(
            binder("A")
                .substitute(
                    &BTreeMap::from([("A".into(), binder("B")), ("B".into(), binder("A"))]),
                    &mut WorkLimit::new(4096)
                )
                .unwrap_err(),
            SourceTypesError::CyclicSubstitution
        );
    }

    #[test]
    fn structural_queries_keep_modes_names_and_frozen_environment_dependencies() {
        let input = recursive(3);
        assert!(
            !input
                .requires_environment(&mut WorkLimit::new(4096))
                .unwrap()
        );
        assert!(
            binder("genuine:T")
                .requires_environment(&mut WorkLimit::new(128))
                .unwrap()
        );
        let callback = SourceSchema::callable(
            &[(ParameterMode::SharedMut, input.clone())],
            &scalar(SourceScalar::Unit),
            &["&{STATE}".into()],
            Some(TypeExprId(43)),
            &mut WorkLimit::new(4096),
        )
        .unwrap();
        assert!(
            callback
                .requires_environment(&mut WorkLimit::new(4096))
                .unwrap()
        );
        let (parameters, result) = callback
            .callable_parts(&mut WorkLimit::new(128))
            .unwrap()
            .unwrap();
        assert_eq!(parameters[0].0, ParameterMode::SharedMut);
        assert_eq!(result.key().unwrap(), ArgumentKey::Tuple(vec![]));
        assert_eq!(
            callback
                .callable_annotations(&mut WorkLimit::new(128))
                .unwrap()
                .unwrap(),
            ["&{STATE}"]
        );
        let record = SourceSchema::record(
            &[
                ("action".into(), false, callback),
                ("data".into(), true, input),
            ],
            None,
            None,
            &mut WorkLimit::new(8192),
        )
        .unwrap();
        assert!(
            !record
                .record_field("action", &mut WorkLimit::new(256))
                .unwrap()
                .unwrap()
                .0
        );
        assert!(
            record
                .record_field("data", &mut WorkLimit::new(256))
                .unwrap()
                .unwrap()
                .0
        );
        assert!(
            record
                .record_field("missing", &mut WorkLimit::new(256))
                .unwrap()
                .is_none()
        );
        assert!(record.record_field("data", &mut WorkLimit::new(0)).is_err());
        let name = SourceSchema::import(
            &ArgumentKey::Name {
                name: "Iter::Step".into(),
                arguments: vec![ArgumentKey::Tuple(vec![]), ArgumentKey::Tuple(vec![])],
            },
            None,
            &mut WorkLimit::new(128),
        )
        .unwrap();
        assert_eq!(
            name.opaque_arguments("Iter::Step", 2, &mut WorkLimit::new(128))
                .unwrap()
                .unwrap()
                .len(),
            2
        );
        assert!(
            name.opaque_arguments("Other::Step", 2, &mut WorkLimit::new(128))
                .unwrap()
                .is_none()
        );
        assert_eq!(
            name.opaque_arguments("Iter::Step", 1, &mut WorkLimit::new(128))
                .unwrap_err(),
            SourceTypesError::InvalidContainer
        );
    }

    #[test]
    fn scalar_numeric_projection_never_exports_the_receivers_recursive_value_graph() {
        use ril_compiler_core::builtin_calls::GenericBuiltin;
        let receiver = SourceSchema::map(
            &scalar(SourceScalar::I16),
            &recursive(3),
            None,
            &mut WorkLimit::new(4096),
        )
        .unwrap();
        assert_eq!(receiver.key(), Err(SourceTypesError::RecursiveLegacyKey));
        assert!(
            receiver
                .array_parts(&mut WorkLimit::new(4096))
                .unwrap()
                .is_none()
        );
        assert_eq!(
            super::super::super::polymorphic::numeric_parameters_schema(
                GenericBuiltin::MapSet,
                Some(&receiver),
                &mut WorkLimit::new(128)
            )
            .unwrap(),
            [None, Some(SourceScalar::I16), None]
        );
        assert!(
            super::super::super::polymorphic::numeric_parameters_schema(
                GenericBuiltin::MapSet,
                Some(&receiver),
                &mut WorkLimit::new(0)
            )
            .is_err()
        );
    }

    #[test]
    fn empty_context_requires_the_real_empty_shape_and_a_complete_bounded_target() {
        let target = SourceSchema::array(
            SourceLength::Fixed(0),
            &recursive(3),
            Some(TypeExprId(31)),
            &mut WorkLimit::new(4096),
        )
        .unwrap();
        assert_eq!(
            target.empty_context(&Construction::Array(vec![]), &mut WorkLimit::new(4096)),
            Ok(Some(true))
        );
        assert_eq!(
            target.empty_context(&Construction::Opaque, &mut WorkLimit::new(128)),
            Ok(None)
        );
        assert_eq!(
            target.empty_context(
                &Construction::Array(vec![Construction::Opaque]),
                &mut WorkLimit::new(128)
            ),
            Ok(None)
        );
        assert!(
            target
                .empty_context(&Construction::Array(vec![]), &mut WorkLimit::new(0))
                .is_err()
        );
        let nonempty = SourceSchema::array(
            SourceLength::Fixed(1),
            &recursive(3),
            None,
            &mut WorkLimit::new(4096),
        )
        .unwrap();
        assert_eq!(
            nonempty.empty_context(&Construction::Array(vec![]), &mut WorkLimit::new(4096)),
            Ok(Some(false))
        );
        let unresolved = SourceSchema::import(
            &ArgumentKey::Closed("unknown".into()),
            None,
            &mut WorkLimit::new(128),
        )
        .unwrap();
        let incomplete = SourceSchema::array(
            SourceLength::Fixed(0),
            &unresolved,
            None,
            &mut WorkLimit::new(4096),
        )
        .unwrap();
        assert_eq!(
            incomplete.empty_context(&Construction::Array(vec![]), &mut WorkLimit::new(4096)),
            Err(SourceTypesError::Unresolved)
        );
        assert_eq!(
            unresolved.requires_environment(&mut WorkLimit::new(128)),
            Err(SourceTypesError::Unresolved)
        );
        let relabeled = target.with_original(Some(TypeExprId(37)));
        assert_eq!(relabeled.root, target.root);
        assert_eq!(relabeled.original(), Some(TypeExprId(37)));
        assert_eq!(target.original(), Some(TypeExprId(31)));
    }
}
