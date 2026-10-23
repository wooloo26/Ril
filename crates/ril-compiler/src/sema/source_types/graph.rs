use ril_compiler_core::ids::GenericParamId;
use ril_syntax::ast::ParameterMode;
use std::sync::{
    Arc,
    atomic::{AtomicU64, Ordering},
};

static NEXT_ARENA: AtomicU64 = AtomicU64::new(1);

#[path = "graph_imports.rs"]
mod imports;
#[path = "radix.rs"]
mod radix;
#[cfg(test)]
#[path = "radix_tests.rs"]
mod radix_tests;

/// An ID cannot be mistaken for the same ordinal in an unrelated snapshot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceTypeId {
    pub(super) arena: u64,
    pub(super) index: u32,
}

pub(crate) use ril_ir::provenance::CallableRowOrigin;
pub(crate) use ril_ir::provenance::KeyProjectionOrigin;
pub(crate) use ril_ir::provenance::{SourceContainer, SourceLength, SourceScalar};
pub(crate) type CallableRowIdentity<I = SourceTypeId> = ril_ir::provenance::CallableRowIdentity<I>;

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
    /// A dependent member selected by a genuine Key parameter. The Key UID is
    /// not a Type binder, and the base remains a complete original graph.
    KeyProjection {
        origin: KeyProjectionOrigin,
        parameter: GenericParamId,
        identity: String,
        base: SourceTypeId,
    },
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
        row_identity: Option<CallableRowIdentity>,
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
    /// A Const argument admitted from an independently certified normalized
    /// nominal declaration. This is a value coordinate, never a Type leaf.
    StaticValue(String),
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
            | Self::StaticValue(_)
            | Self::OpaqueComputation(_) => {
                vec![]
            }
            Self::Array { element, .. } => vec![*element],
            Self::KeyProjection { base, .. } => vec![*base],
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
                parameters,
                result,
                row_identity,
                ..
            } => parameters
                .iter()
                .map(|(_, ty)| *ty)
                .chain([*result])
                .chain(
                    row_identity
                        .iter()
                        .flat_map(|row| row.parameters.iter().map(|(_, root)| *root)),
                )
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
            Self::KeyProjection {
                origin,
                parameter,
                identity,
                base,
            } => Self::KeyProjection {
                origin: *origin,
                parameter: *parameter,
                identity: identity.clone(),
                base: map(*base)?,
            },
            Self::StaticValue(value) => Self::StaticValue(value.clone()),
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
                row_identity,
            } => Self::Callable {
                parameters: parameters
                    .iter()
                    .map(|(mode, id)| Ok((*mode, map(*id)?)))
                    .collect::<Result<_, SourceTypesError>>()?,
                result: map(*result)?,
                annotations: annotations.clone(),
                row_identity: row_identity
                    .as_ref()
                    .map(|row| {
                        Ok::<_, SourceTypesError>(CallableRowIdentity {
                            origin: row.origin,
                            parameters: row
                                .parameters
                                .iter()
                                .map(|(id, root)| Ok((*id, map(*root)?)))
                                .collect::<Result<_, SourceTypesError>>()?,
                        })
                    })
                    .transpose()?,
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
            Self::Binder(identity)
            | Self::KeyProjection { identity, .. }
            | Self::StaticValue(identity)
            | Self::OpaqueComputation(identity) => work.text(identity),
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
                row_identity,
                ..
            } => {
                work.charge(parameters.len())?;
                work.charge(
                    row_identity
                        .as_ref()
                        .map_or(0, |row| row.parameters.len() + 1),
                )?;
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
    InvalidEvidence(String),
    BudgetExceeded,
    ForeignIdentity,
    MissingNode,
    /// A packet has not run its original Source capture yet. Graph queries do
    /// not produce this obligation or treat it as a missing graph node.
    SourceNotCaptured,
    /// The packet's current view changed after birth and needs its existing
    /// receiving/selection evidence. The immutable birth Source is unchanged.
    SourceViewPending,
    AlreadyDefined,
    DuplicateField,
    InvalidContainer,
    AliasCycle,
    RowCycle,
    /// Original HIR syntax still requires its declaration's static evaluator.
    /// This is an ingress request, never an observed graph's unknown result.
    NeedsStaticElaboration,
    Unresolved,
    MissingProjection,
    CyclicSubstitution,
    RecursiveLegacyKey,
    IdentityExhausted,
    TransactionOpen,
    InvalidTransaction,
}

impl std::fmt::Display for SourceTypesError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Self::InvalidEvidence(reason) = self {
            return write!(formatter, "original Source evidence failed: {reason}");
        }
        formatter.write_str(match self {
            Self::InvalidEvidence(_) => unreachable!("evidence reason rendered above"),
            Self::BudgetExceeded => "source type reconstruction budget exhausted",
            Self::ForeignIdentity => "source type identity belongs to another snapshot",
            Self::MissingNode => "source type node is missing or unfinished",
            Self::SourceNotCaptured => "original evaluation Source has not been captured",
            Self::SourceViewPending => {
                "current evaluation Source view requires its change evidence"
            }
            Self::AlreadyDefined => "source type node or binding is already defined",
            Self::DuplicateField => "source record fields overlap",
            Self::InvalidContainer => "source container has an invalid argument count",
            Self::AliasCycle => "source alias cycle has no resolved structure",
            Self::RowCycle => "source row cycle has no resolved remainder",
            Self::NeedsStaticElaboration => {
                "source declaration requires its frozen static interpretation"
            }
            Self::Unresolved => "source type coordinates remain unresolved",
            Self::MissingProjection => "source type has no such projection",
            Self::CyclicSubstitution => "source binder substitutions contain a cycle",
            Self::RecursiveLegacyKey => {
                "recursive source graph cannot be represented as a legacy key"
            }
            Self::IdentityExhausted => "source type identity space exhausted",
            Self::TransactionOpen => "source type transaction is still open",
            Self::InvalidTransaction => "source type transaction does not belong to this builder",
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
    pub(crate) fn text(&mut self, value: &str) -> Result<(), SourceTypesError> {
        self.charge(value.len().div_ceil(32))
    }
}

/// One writer over persistent immutable nodes. Reservations admit finite
/// recursive backedges; only a complete, transaction-free state may publish.
pub(crate) struct SourceBuilder {
    arena: u64,
    nodes: radix::Nodes,
    undefined: usize,
    retained: usize,
    transaction: Option<u64>,
    next_transaction: u64,
    /// Only immutable source arenas enter this copy index. It shares structure
    /// and never certifies completeness, compatibility or lexical authority.
    imports: std::collections::BTreeMap<SourceTypeId, SourceTypeId>,
    import_order: Vec<SourceTypeId>,
}

/// Opaque single-layer transaction. No snapshot may escape between begin and
/// commit/rollback, so a discarded ordinal can never name a published node.
pub(super) struct SourceTransaction {
    arena: u64,
    token: u64,
    nodes: radix::Nodes,
    undefined: usize,
    retained: usize,
    imports: usize,
}

impl SourceBuilder {
    pub(crate) fn new() -> Result<Self, SourceTypesError> {
        let arena = NEXT_ARENA
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .map_err(|_| SourceTypesError::IdentityExhausted)?;
        Ok(Self {
            arena,
            nodes: radix::Nodes::default(),
            undefined: 0,
            retained: 0,
            transaction: None,
            next_transaction: 0,
            imports: std::collections::BTreeMap::new(),
            import_order: vec![],
        })
    }

    pub(crate) fn reserve(
        &mut self,
        work: &mut WorkLimit,
    ) -> Result<SourceTypeId, SourceTypesError> {
        work.charge(1)?;
        let index = self.nodes.reserve()?;
        self.undefined += 1;
        Ok(SourceTypeId {
            arena: self.arena,
            index: index as u32,
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
        let payload = (usize::MAX - admission.remaining()).saturating_mul(256);
        for child in node.children() {
            if child.arena != self.arena {
                return Err(SourceTypesError::ForeignIdentity);
            }
            if child.index as usize >= self.nodes.len() {
                return Err(SourceTypesError::MissingNode);
            }
        }
        if let SourceNode::Record { fields, .. } = &mut node {
            let comparisons = fields.len().checked_ilog2().unwrap_or(0) as usize + 1;
            work.charge(
                fields
                    .len()
                    .checked_mul(comparisons)
                    .ok_or(SourceTypesError::BudgetExceeded)?,
            )?;
            for field in fields.iter() {
                work.charge(
                    field
                        .label
                        .len()
                        .div_ceil(32)
                        .checked_mul(comparisons)
                        .ok_or(SourceTypesError::BudgetExceeded)?,
                )?;
            }
            fields.sort_unstable_by(|left, right| left.label.cmp(&right.label));
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
        let plan = self.nodes.prepare_define(id.index as usize, work)?;
        let retained = self
            .retained
            .checked_add(payload)
            .and_then(|cost| cost.checked_add(plan.retained_bytes()))
            .filter(|cost| *cost <= 16 * 1024 * 1024)
            .ok_or(SourceTypesError::BudgetExceeded)?;
        let undefined = self
            .undefined
            .checked_sub(1)
            .ok_or(SourceTypesError::MissingNode)?;
        self.nodes.define(id.index as usize, Arc::new(node), plan);
        self.undefined = undefined;
        self.retained = retained;
        Ok(())
    }

    pub(crate) fn insert(
        &mut self,
        node: SourceNode,
        work: &mut WorkLimit,
    ) -> Result<SourceTypeId, SourceTypesError> {
        let id = self.reserve(work)?;
        if let Err(error) = self.define(id, node, work) {
            // define preflights every fallible step before editing the tree.
            self.nodes.cancel_reservation(id.index as usize);
            self.undefined -= 1;
            return Err(error);
        }
        Ok(id)
    }

    pub(crate) fn snapshot(&self, work: &mut WorkLimit) -> Result<SourceTypes, SourceTypesError> {
        work.charge(2)?;
        if self.transaction.is_some() {
            return Err(SourceTypesError::TransactionOpen);
        }
        if self.undefined != 0 {
            return Err(SourceTypesError::MissingNode);
        }
        Ok(SourceTypes {
            arena: self.arena,
            nodes: self.nodes.clone(),
        })
    }

    pub(crate) fn freeze(self, work: &mut WorkLimit) -> Result<SourceTypes, SourceTypesError> {
        self.snapshot(work)
    }

    pub(super) fn begin_transaction(
        &mut self,
        work: &mut WorkLimit,
    ) -> Result<SourceTransaction, SourceTypesError> {
        // Includes the eventual constant commit/rollback state transition.
        work.charge(5)?;
        if self.transaction.is_some() {
            return Err(SourceTypesError::TransactionOpen);
        }
        let token = self
            .next_transaction
            .checked_add(1)
            .ok_or(SourceTypesError::IdentityExhausted)?;
        self.next_transaction = token;
        let checkpoint = SourceTransaction {
            arena: self.arena,
            token,
            nodes: self.nodes.clone(),
            undefined: self.undefined,
            retained: self.retained,
            imports: self.import_order.len(),
        };
        self.transaction = Some(token);
        Ok(checkpoint)
    }

    fn check_transaction(&self, checkpoint: &SourceTransaction) -> Result<(), SourceTypesError> {
        if checkpoint.arena != self.arena {
            return Err(SourceTypesError::ForeignIdentity);
        }
        if self.transaction != Some(checkpoint.token) {
            return Err(SourceTypesError::InvalidTransaction);
        }
        Ok(())
    }

    pub(super) fn commit_transaction(
        &mut self,
        checkpoint: SourceTransaction,
    ) -> Result<(), SourceTypesError> {
        self.check_transaction(&checkpoint)?;
        self.transaction = None;
        Ok(())
    }

    pub(super) fn rollback_transaction(
        &mut self,
        checkpoint: SourceTransaction,
    ) -> Result<(), SourceTypesError> {
        self.check_transaction(&checkpoint)?;
        // Memo insertion prepays removal; rollback never borrows fresh work.
        while self.import_order.len() > checkpoint.imports {
            if let Some(source) = self.import_order.pop() {
                self.imports.remove(&source);
            }
        }
        self.nodes = checkpoint.nodes;
        self.undefined = checkpoint.undefined;
        self.retained = checkpoint.retained;
        self.transaction = None;
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn checkpoint(&self) -> (usize, usize, usize, usize, bool) {
        (
            self.nodes.len(),
            self.undefined,
            self.retained,
            self.import_order.len(),
            self.transaction.is_some(),
        )
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct SourceTypes {
    arena: u64,
    nodes: radix::Nodes,
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
            .map(Arc::as_ref)
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
    ) -> impl ExactSizeIterator<Item = Result<(SourceTypeId, &SourceNode), SourceTypesError>> {
        (0..self.nodes.len()).map(|index| {
            let id = SourceTypeId {
                arena: self.arena,
                index: index as u32,
            };
            self.get(id).map(|node| (id, node))
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
