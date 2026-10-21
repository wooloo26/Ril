use ril_syntax::ast::ParameterMode;
use std::sync::{
    Arc,
    atomic::{AtomicU64, Ordering},
};

static NEXT_ARENA: AtomicU64 = AtomicU64::new(1);

/// An ID cannot be mistaken for the same ordinal in an unrelated snapshot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceTypeId {
    pub(super) arena: u64,
    pub(super) index: u32,
}

pub(crate) use ril_ir::provenance::{SourceContainer, SourceLength, SourceScalar};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SourceField {
    pub(crate) label: String,
    pub(crate) mutable: bool,
    pub(crate) value: SourceTypeId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SourceNode {
    /// A catalog reference retains its quantified variables, full parameter
    /// correlations and mode alternatives without choosing a runtime instance.
    GenericBuiltin(ril_compiler_core::builtin_calls::GenericBuiltin),
    Scalar(SourceScalar),
    /// A closed nominal declaration in the immutable standard data catalog.
    Nominal(super::standard_data::Nominal),
    /// A genuine Type UID is complete as an identity, but its structure is
    /// unknown until an independently justified substitution selects it.
    Binder(String),
    Array {
        length: SourceLength,
        element: SourceTypeId,
    },
    Map {
        key: SourceTypeId,
        value: SourceTypeId,
    },
    Tuple(Vec<SourceTypeId>),
    Record {
        fields: Vec<SourceField>,
        row: Option<SourceTypeId>,
    },
    Callable {
        parameters: Vec<(ParameterMode, SourceTypeId)>,
        result: SourceTypeId,
        annotations: Vec<String>,
    },
    Container {
        kind: SourceContainer,
        arguments: Vec<SourceTypeId>,
    },
    /// This edge is created only by resolving the original declaration. Its
    /// finite backedge is not an unknown-type or scalar-type assertion.
    Alias {
        declaration: String,
        target: SourceTypeId,
    },
    /// Exact legacy name identity without a declaration-resolution proof.
    /// It may be transported, but can never prove coordinate absence.
    OpaqueName {
        name: String,
        arguments: Vec<SourceTypeId>,
    },
    OpaqueComputation(String),
    /// Preserve an unresolved name/computation instead of interpreting its
    /// spelling as a scalar leaf. Arguments remain reachable for diagnostics.
    Unresolved {
        description: String,
        arguments: Vec<SourceTypeId>,
    },
}

impl SourceNode {
    pub(super) fn children(&self) -> Vec<SourceTypeId> {
        match self {
            Self::GenericBuiltin(_)
            | Self::Scalar(_)
            | Self::Nominal(_)
            | Self::Binder(_)
            | Self::OpaqueComputation(_) => {
                vec![]
            }
            Self::Array { element, .. } => vec![*element],
            Self::Map { key, value } => vec![*key, *value],
            Self::Tuple(items)
            | Self::Container {
                arguments: items, ..
            }
            | Self::OpaqueName {
                arguments: items, ..
            }
            | Self::Unresolved {
                arguments: items, ..
            } => items.clone(),
            Self::Record { fields, row } => fields
                .iter()
                .map(|field| field.value)
                .chain(row.iter().copied())
                .collect(),
            Self::Callable {
                parameters, result, ..
            } => parameters
                .iter()
                .map(|(_, ty)| *ty)
                .chain([*result])
                .collect(),
            Self::Alias { target, .. } => vec![*target],
        }
    }

    pub(super) fn map_children(
        &self,
        mut map: impl FnMut(SourceTypeId) -> Result<SourceTypeId, SourceTypesError>,
    ) -> Result<Self, SourceTypesError> {
        Ok(match self {
            Self::GenericBuiltin(id) => Self::GenericBuiltin(*id),
            Self::Scalar(kind) => Self::Scalar(*kind),
            Self::Nominal(id) => Self::Nominal(*id),
            Self::Binder(identity) => Self::Binder(identity.clone()),
            Self::OpaqueComputation(key) => Self::OpaqueComputation(key.clone()),
            Self::Array { length, element } => Self::Array {
                length: *length,
                element: map(*element)?,
            },
            Self::Map { key, value } => Self::Map {
                key: map(*key)?,
                value: map(*value)?,
            },
            Self::Tuple(items) => {
                Self::Tuple(items.iter().map(|id| map(*id)).collect::<Result<_, _>>()?)
            }
            Self::Record { fields, row } => Self::Record {
                fields: fields
                    .iter()
                    .map(|field| {
                        Ok(SourceField {
                            label: field.label.clone(),
                            mutable: field.mutable,
                            value: map(field.value)?,
                        })
                    })
                    .collect::<Result<_, SourceTypesError>>()?,
                row: row.map(&mut map).transpose()?,
            },
            Self::Callable {
                parameters,
                result,
                annotations,
            } => Self::Callable {
                parameters: parameters
                    .iter()
                    .map(|(mode, id)| Ok((*mode, map(*id)?)))
                    .collect::<Result<_, SourceTypesError>>()?,
                result: map(*result)?,
                annotations: annotations.clone(),
            },
            Self::Container { kind, arguments } => Self::Container {
                kind: *kind,
                arguments: arguments
                    .iter()
                    .map(|id| map(*id))
                    .collect::<Result<_, _>>()?,
            },
            Self::Alias {
                declaration,
                target,
            } => Self::Alias {
                declaration: declaration.clone(),
                target: map(*target)?,
            },
            Self::OpaqueName { name, arguments } => Self::OpaqueName {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|id| map(*id))
                    .collect::<Result<_, _>>()?,
            },
            Self::Unresolved {
                description,
                arguments,
            } => Self::Unresolved {
                description: description.clone(),
                arguments: arguments
                    .iter()
                    .map(|id| map(*id))
                    .collect::<Result<_, _>>()?,
            },
        })
    }

    pub(super) fn charge(&self, work: &mut WorkLimit) -> Result<(), SourceTypesError> {
        work.charge(1)?;
        match self {
            Self::Binder(identity) | Self::OpaqueComputation(identity) => work.text(identity),
            Self::Record { fields, .. } => {
                for field in fields {
                    work.charge(1)?;
                    work.text(&field.label)?;
                }
                Ok(())
            }
            Self::Callable {
                parameters,
                annotations,
                ..
            } => {
                work.charge(parameters.len())?;
                for annotation in annotations {
                    work.charge(1)?;
                    work.text(annotation)?;
                }
                Ok(())
            }
            Self::Tuple(items)
            | Self::Container {
                arguments: items, ..
            } => work.charge(items.len()),
            Self::Alias { declaration, .. } => work.text(declaration),
            Self::Unresolved {
                description,
                arguments,
            } => {
                work.text(description)?;
                work.charge(arguments.len())
            }
            Self::OpaqueName { name, arguments } => {
                work.text(name)?;
                work.charge(arguments.len())
            }
            _ => Ok(()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceTypesError {
    BudgetExceeded,
    ForeignIdentity,
    MissingNode,
    AlreadyDefined,
    DuplicateField,
    InvalidContainer,
    AliasCycle,
    RowCycle,
    Unresolved,
    MissingProjection,
    CyclicSubstitution,
    RecursiveLegacyKey,
    IdentityExhausted,
}

impl std::fmt::Display for SourceTypesError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(match self {
            Self::BudgetExceeded => "source type reconstruction budget exhausted",
            Self::ForeignIdentity => "source type identity belongs to another snapshot",
            Self::MissingNode => "source type node is missing or unfinished",
            Self::AlreadyDefined => "source type node or binding is already defined",
            Self::DuplicateField => "source record fields overlap",
            Self::InvalidContainer => "source container has an invalid argument count",
            Self::AliasCycle => "source alias cycle has no resolved structure",
            Self::RowCycle => "source row cycle has no resolved remainder",
            Self::Unresolved => "source type coordinates remain unresolved",
            Self::MissingProjection => "source type has no such projection",
            Self::CyclicSubstitution => "source binder substitutions contain a cycle",
            Self::RecursiveLegacyKey => {
                "recursive source graph cannot be represented as a legacy key"
            }
            Self::IdentityExhausted => "source type identity space exhausted",
        })
    }
}

impl std::error::Error for SourceTypesError {}

#[derive(Debug, Clone)]
pub(crate) struct WorkLimit {
    remaining: usize,
}
impl WorkLimit {
    pub(crate) fn new(units: usize) -> Self {
        Self { remaining: units }
    }
    pub(crate) fn remaining(&self) -> usize {
        self.remaining
    }
    pub(crate) fn charge(&mut self, units: usize) -> Result<(), SourceTypesError> {
        self.remaining = self
            .remaining
            .checked_sub(units)
            .ok_or(SourceTypesError::BudgetExceeded)?;
        Ok(())
    }
    pub(super) fn text(&mut self, value: &str) -> Result<(), SourceTypesError> {
        self.charge(value.len().div_ceil(32))
    }
}

/// The only mutable construction phase. Reserved nodes permit finite recursive
/// declarations; no query is available until every reservation is defined.
pub(crate) struct SourceBuilder {
    arena: u64,
    nodes: Vec<Option<Arc<SourceNode>>>,
    retained: usize,
}

impl SourceBuilder {
    pub(crate) fn new() -> Result<Self, SourceTypesError> {
        let arena = NEXT_ARENA
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .map_err(|_| SourceTypesError::IdentityExhausted)?;
        Ok(Self {
            arena,
            nodes: vec![],
            retained: 0,
        })
    }
    pub(crate) fn reserve(
        &mut self,
        work: &mut WorkLimit,
    ) -> Result<SourceTypeId, SourceTypesError> {
        work.charge(1)?;
        if self.nodes.len() >= 65536 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let index =
            u32::try_from(self.nodes.len()).map_err(|_| SourceTypesError::IdentityExhausted)?;
        self.nodes.push(None);
        Ok(SourceTypeId {
            arena: self.arena,
            index,
        })
    }
    pub(crate) fn define(
        &mut self,
        id: SourceTypeId,
        mut node: SourceNode,
        work: &mut WorkLimit,
    ) -> Result<(), SourceTypesError> {
        if id.arena != self.arena {
            return Err(SourceTypesError::ForeignIdentity);
        }
        node.charge(work)?;
        let mut admission = WorkLimit::new(usize::MAX);
        node.charge(&mut admission)?;
        let cost = (usize::MAX - admission.remaining()).saturating_mul(256);
        if self.retained.saturating_add(cost) > 16 * 1024 * 1024 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        for child in node.children() {
            if child.arena != self.arena {
                return Err(SourceTypesError::ForeignIdentity);
            }
            if child.index as usize >= self.nodes.len() {
                return Err(SourceTypesError::MissingNode);
            }
        }
        if let SourceNode::Record { fields, .. } = &mut node {
            fields.sort_by(|left, right| left.label.cmp(&right.label));
            if fields.windows(2).any(|pair| pair[0].label == pair[1].label) {
                return Err(SourceTypesError::DuplicateField);
            }
        }
        if let SourceNode::Container { kind, arguments } = &node {
            let arity = if *kind == SourceContainer::Result {
                2
            } else {
                1
            };
            if arguments.len() != arity {
                return Err(SourceTypesError::InvalidContainer);
            }
        }
        let slot = self
            .nodes
            .get_mut(id.index as usize)
            .ok_or(SourceTypesError::MissingNode)?;
        if slot.is_some() {
            return Err(SourceTypesError::AlreadyDefined);
        }
        *slot = Some(Arc::new(node));
        self.retained += cost;
        Ok(())
    }
    pub(crate) fn insert(
        &mut self,
        node: SourceNode,
        work: &mut WorkLimit,
    ) -> Result<SourceTypeId, SourceTypesError> {
        let id = self.reserve(work)?;
        self.define(id, node, work)?;
        Ok(id)
    }
    pub(crate) fn freeze(self, work: &mut WorkLimit) -> Result<SourceTypes, SourceTypesError> {
        work.charge(self.nodes.len())?;
        let nodes = self
            .nodes
            .into_iter()
            .map(|node| node.ok_or(SourceTypesError::MissingNode))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(SourceTypes {
            arena: self.arena,
            nodes: nodes.into(),
        })
    }
    pub(super) fn checkpoint(&self) -> (usize, usize) {
        (self.nodes.len(), self.retained)
    }
    pub(super) fn rollback(&mut self, checkpoint: (usize, usize)) {
        self.nodes.truncate(checkpoint.0);
        self.retained = checkpoint.1;
    }
}

#[derive(Debug, Clone)]
pub(crate) struct SourceTypes {
    arena: u64,
    nodes: Arc<[Arc<SourceNode>]>,
}

impl Default for SourceTypes {
    fn default() -> Self {
        Self {
            arena: 0,
            nodes: Arc::from([]),
        }
    }
}

pub(crate) trait SourceGraph {
    fn get(&self, id: SourceTypeId) -> Result<&SourceNode, SourceTypesError>;
}

impl SourceGraph for SourceBuilder {
    fn get(&self, id: SourceTypeId) -> Result<&SourceNode, SourceTypesError> {
        if id.arena != self.arena {
            return Err(SourceTypesError::ForeignIdentity);
        }
        self.nodes
            .get(id.index as usize)
            .and_then(Option::as_deref)
            .ok_or(SourceTypesError::MissingNode)
    }
}

impl SourceGraph for SourceTypes {
    fn get(&self, id: SourceTypeId) -> Result<&SourceNode, SourceTypesError> {
        SourceTypes::get(self, id)
    }
}

impl SourceTypes {
    pub(super) fn indexed_nodes(
        &self,
    ) -> impl ExactSizeIterator<Item = (SourceTypeId, &SourceNode)> {
        self.nodes.iter().enumerate().map(|(index, node)| {
            (
                SourceTypeId {
                    arena: self.arena,
                    index: index as u32,
                },
                node.as_ref(),
            )
        })
    }

    pub(crate) fn get(&self, id: SourceTypeId) -> Result<&SourceNode, SourceTypesError> {
        if id.arena != self.arena {
            return Err(SourceTypesError::ForeignIdentity);
        }
        self.nodes
            .get(id.index as usize)
            .map(Arc::as_ref)
            .ok_or(SourceTypesError::MissingNode)
    }
}
