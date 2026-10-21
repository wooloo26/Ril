//! One bounded substitution implementation for production and replay. Legacy
//! trees are only ingress/egress; recursive sources stay in the graph arena.
use super::*;
use crate::sema::effect_identity::{ArgumentKey, StaticBinderSort};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) fn substitute_key(
    key: &ArgumentKey,
    selected: &BTreeMap<String, ArgumentKey>,
    work: &mut WorkLimit,
) -> Result<ArgumentKey, SourceTypesError> {
    let mut builder = SourceBuilder::new()?;
    let root = super::legacy::import_node(key, &mut builder, work, 0)?;
    let mut selections = BTreeMap::new();
    for (identity, key) in selected {
        work.text(identity)?;
        selections.insert(
            identity.clone(),
            super::legacy::import_node(key, &mut builder, work, 0)?,
        );
    }
    let types = builder.freeze(work)?;
    let result = types.substitute(root, &selections, work)?;
    result.types.canonical_key(result.root, work)
}

pub(crate) trait LegacySourceExport: super::graph::SourceGraph {
    fn legacy_key(
        &self,
        root: SourceTypeId,
        work: &mut WorkLimit,
    ) -> Result<ArgumentKey, SourceTypesError> {
        self.export_key(root, work, false, None)
    }
    fn canonical_key(
        &self,
        root: SourceTypeId,
        work: &mut WorkLimit,
    ) -> Result<ArgumentKey, SourceTypesError> {
        self.export_key(root, work, true, None)
    }
    fn declared_key(
        &self,
        root: SourceTypeId,
        declarations: &BTreeSet<SourceTypeId>,
        work: &mut WorkLimit,
    ) -> Result<ArgumentKey, SourceTypesError> {
        self.export_key(root, work, false, Some(declarations))
    }
    fn export_key(
        &self,
        root: SourceTypeId,
        work: &mut WorkLimit,
        flatten_rows: bool,
        declarations: Option<&BTreeSet<SourceTypeId>>,
    ) -> Result<ArgumentKey, SourceTypesError> {
        fn export<G: super::graph::SourceGraph + ?Sized>(
            types: &G,
            id: SourceTypeId,
            active: &mut BTreeSet<SourceTypeId>,
            work: &mut WorkLimit,
            depth: usize,
            flatten_rows: bool,
            declarations: Option<&BTreeSet<SourceTypeId>>,
        ) -> Result<ArgumentKey, SourceTypesError> {
            if depth >= 64 {
                return Err(SourceTypesError::BudgetExceeded);
            }
            let node = types.get(id)?;
            node.charge(work)?;
            if !active.insert(id) {
                return Err(SourceTypesError::RecursiveLegacyKey);
            }
            let mut child = |id| {
                export(
                    types,
                    id,
                    active,
                    work,
                    depth + 1,
                    flatten_rows,
                    declarations,
                )
            };
            let key = match node {
                SourceNode::GenericBuiltin(id) => ArgumentKey::GenericBuiltin(*id),
                SourceNode::Scalar(SourceScalar::Unit) => ArgumentKey::Tuple(vec![]),
                SourceNode::Scalar(kind) => ArgumentKey::Name {
                    name: scalar_name(*kind).into(),
                    arguments: vec![],
                },
                SourceNode::Nominal(id) => ArgumentKey::Name {
                    name: id.name().into(),
                    arguments: vec![],
                },
                SourceNode::Binder(identity) => ArgumentKey::Binder {
                    identity: identity.clone(),
                    sort: StaticBinderSort::Type,
                },
                SourceNode::OpaqueComputation(key) => ArgumentKey::Closed(key.clone()),
                SourceNode::Array { length, element } => ArgumentKey::Array {
                    length: match length {
                        SourceLength::Dynamic => None,
                        SourceLength::Fixed(length) => Some(format!("const(int:{length})")),
                    },
                    element: Box::new(child(*element)?),
                },
                SourceNode::Map { key, value } => ArgumentKey::Map {
                    key: Box::new(child(*key)?),
                    value: Box::new(child(*value)?),
                },
                SourceNode::Tuple(items) => ArgumentKey::Tuple(
                    items
                        .iter()
                        .map(|id| child(*id))
                        .collect::<Result<_, _>>()?,
                ),
                SourceNode::Record { fields, row } => {
                    let mut fields = fields
                        .iter()
                        .map(|field| Ok((field.label.clone(), field.mutable, child(field.value)?)))
                        .collect::<Result<Vec<_>, SourceTypesError>>()?;
                    let mut row = row.map(|id| child(id).map(Box::new)).transpose()?;
                    if flatten_rows && let Some(tail) = row.take() {
                        match *tail {
                            ArgumentKey::Record {
                                fields: extra,
                                row: rest,
                            } => {
                                for field in extra {
                                    if fields.iter().any(|old| old.0 == field.0) {
                                        return Err(SourceTypesError::DuplicateField);
                                    }
                                    fields.push(field);
                                }
                                row = rest;
                            }
                            other => row = Some(Box::new(other)),
                        }
                    }
                    fields.sort_by(|left, right| left.0.cmp(&right.0));
                    ArgumentKey::Record { fields, row }
                }
                SourceNode::Callable {
                    parameters,
                    result,
                    annotations,
                } => ArgumentKey::Callable {
                    parameters: parameters
                        .iter()
                        .map(|(mode, id)| Ok((*mode, child(*id)?)))
                        .collect::<Result<_, SourceTypesError>>()?,
                    result: Box::new(child(*result)?),
                    annotations: annotations.clone(),
                },
                SourceNode::Container { kind, arguments } => ArgumentKey::Name {
                    name: container_name(*kind).into(),
                    arguments: arguments
                        .iter()
                        .map(|id| child(*id))
                        .collect::<Result<_, _>>()?,
                },
                SourceNode::Alias { declaration, .. }
                    if declarations.is_some_and(|names| names.contains(&id)) =>
                {
                    ArgumentKey::Name {
                        name: declaration.clone(),
                        arguments: vec![],
                    }
                }
                SourceNode::Alias { target, .. } => child(*target)?,
                SourceNode::OpaqueName { name, arguments } => ArgumentKey::Name {
                    name: name.clone(),
                    arguments: arguments
                        .iter()
                        .map(|id| child(*id))
                        .collect::<Result<_, _>>()?,
                },
                SourceNode::Unresolved { .. } => return Err(SourceTypesError::Unresolved),
            };
            active.remove(&id);
            Ok(key)
        }
        export(
            self,
            root,
            &mut BTreeSet::new(),
            work,
            0,
            flatten_rows,
            declarations,
        )
    }
}

impl<T: super::graph::SourceGraph> LegacySourceExport for T {}

pub(crate) fn scalar_name(kind: SourceScalar) -> &'static str {
    use SourceScalar::*;
    match kind {
        Unit => "()",
        Bool => "bool",
        Str => "str",
        Bytes => "bytes",
        Never => "never",
        Int => "int",
        I8 => "i8",
        I16 => "i16",
        I32 => "i32",
        I64 => "i64",
        I128 => "i128",
        Isize => "isize",
        U8 => "u8",
        U16 => "u16",
        U32 => "u32",
        U64 => "u64",
        U128 => "u128",
        Usize => "usize",
        BigInt => "bigint",
        F32 => "f32",
        F64 => "f64",
        Intrinsic(identity) => identity.name(),
    }
}

fn container_name(kind: SourceContainer) -> &'static str {
    match kind {
        SourceContainer::Immutable => "Immut",
        SourceContainer::Option => "Option",
        SourceContainer::Result => "Result",
        SourceContainer::Set => "Set",
        SourceContainer::Range => "Range",
        SourceContainer::Heap => "Heap::Heap",
        SourceContainer::Deque => "Deque::Deque",
    }
}
