//! Transitional ingress for existing immutable ArgumentKey facts. This adapter
//! preserves original child references; it does not resolve an alias by name or
//! infer dimensions from a collection's runtime contents.
use super::*;
use crate::sema::{effect_identity::ArgumentKey, facts::Slot};
use std::collections::BTreeMap;

pub(super) struct Imported<'a> {
    pub(super) types: SourceTypes,
    pub(super) root: SourceTypeId,
    originals: BTreeMap<SourceTypeId, &'a ArgumentKey>,
}

pub(super) fn scalar(name: &str) -> Option<SourceScalar> {
    use SourceScalar::*;
    Some(match name.strip_prefix("Prelude::").unwrap_or(name) {
        "bool" => Bool,
        "str" => Str,
        "bytes" => Bytes,
        "never" => Never,
        "int" => Int,
        "i8" => I8,
        "i16" => I16,
        "i32" => I32,
        "i64" => I64,
        "i128" => I128,
        "isize" => Isize,
        "u8" => U8,
        "u16" => U16,
        "u32" => U32,
        "u64" => U64,
        "u128" => U128,
        "usize" => Usize,
        "bigint" => BigInt,
        "f32" => F32,
        "f64" => F64,
        _ => return None,
    })
}

pub(super) fn container(name: &str) -> Option<SourceContainer> {
    use SourceContainer::*;
    Some(match name.strip_prefix("Prelude::").unwrap_or(name) {
        "Immut" => Immutable,
        "Option" => Option,
        "Result" => Result,
        "Set" => Set,
        "Range" => Range,
        "Heap::Heap" => Heap,
        "Deque::Deque" => Deque,
        _ => return None,
    })
}

pub(super) fn import_node<'a>(
    key: &'a ArgumentKey,
    builder: &mut SourceBuilder,
    originals: &mut BTreeMap<SourceTypeId, &'a ArgumentKey>,
    work: &mut WorkLimit,
    depth: usize,
) -> Result<SourceTypeId, SourceTypesError> {
    work.charge(1)?;
    if depth >= 64 {
        return Err(SourceTypesError::BudgetExceeded);
    }
    let mut child = |key| import_node(key, builder, originals, work, depth + 1);
    let shape = match key {
        ArgumentKey::Closed(key) => {
            work.text(key)?;
            SourceNode::OpaqueComputation(key.clone())
        }
        ArgumentKey::Binder { identity, .. } => {
            work.text(identity)?;
            SourceNode::Binder(identity.clone())
        }
        ArgumentKey::Name { name, arguments } => {
            let arguments = arguments
                .iter()
                .map(&mut child)
                .collect::<Result<Vec<_>, _>>()?;
            work.text(name)?;
            if arguments.is_empty()
                && let Some(kind) = scalar(name)
            {
                SourceNode::Scalar(kind)
            } else if let Some(kind) = container(name) {
                SourceNode::Container { kind, arguments }
            } else {
                SourceNode::OpaqueName {
                    name: name.clone(),
                    arguments,
                }
            }
        }
        ArgumentKey::Array { length, element } => {
            let element = child(element)?;
            let length = match length {
                None => SourceLength::Dynamic,
                Some(text) => {
                    work.text(text)?;
                    SourceLength::Fixed(
                        text.strip_prefix("const(int:")
                            .and_then(|text| text.strip_suffix(')'))
                            .and_then(|text| text.parse::<u64>().ok())
                            .ok_or(SourceTypesError::Unresolved)?,
                    )
                }
            };
            SourceNode::Array { length, element }
        }
        ArgumentKey::Map { key, value } => SourceNode::Map {
            key: child(key)?,
            value: child(value)?,
        },
        ArgumentKey::Tuple(items) if items.is_empty() => SourceNode::Scalar(SourceScalar::Unit),
        ArgumentKey::Tuple(items) => {
            SourceNode::Tuple(items.iter().map(&mut child).collect::<Result<_, _>>()?)
        }
        ArgumentKey::Record { fields, row } => {
            let fields = fields
                .iter()
                .map(|(label, mutable, key)| {
                    let value = import_node(key, builder, originals, work, depth + 1)?;
                    work.text(label)?;
                    Ok(SourceField {
                        label: label.clone(),
                        mutable: *mutable,
                        value,
                    })
                })
                .collect::<Result<_, SourceTypesError>>()?;
            let row = row
                .as_deref()
                .map(|key| import_node(key, builder, originals, work, depth + 1))
                .transpose()?;
            SourceNode::Record { fields, row }
        }
        ArgumentKey::Callable {
            parameters,
            result,
            annotations,
        } => {
            let parameters = parameters
                .iter()
                .map(|(mode, key)| child(key).map(|key| (*mode, key)))
                .collect::<Result<_, _>>()?;
            let result = child(result)?;
            for annotation in annotations {
                work.text(annotation)?;
            }
            SourceNode::Callable {
                parameters,
                result,
                annotations: annotations.clone(),
            }
        }
    };
    let id = builder.insert(shape, work)?;
    originals.insert(id, key);
    Ok(id)
}

pub(super) fn import<'a>(
    key: &'a ArgumentKey,
    work: &mut WorkLimit,
) -> Result<Imported<'a>, SourceTypesError> {
    let mut builder = SourceBuilder::new()?;
    let mut originals = BTreeMap::new();
    let root = import_node(key, &mut builder, &mut originals, work, 0)?;
    Ok(Imported {
        types: builder.freeze(work)?,
        root,
        originals,
    })
}

impl SourceBuilder {
    pub(crate) fn import_key(
        &mut self,
        key: &ArgumentKey,
        work: &mut WorkLimit,
    ) -> Result<SourceTypeId, SourceTypesError> {
        let checkpoint = self.checkpoint();
        let result = import_node(key, self, &mut BTreeMap::new(), work, 0);
        if result.is_err() {
            self.rollback(checkpoint);
        }
        result
    }
}

pub(crate) fn key_sensitivity(key: &ArgumentKey, work: &mut WorkLimit) -> SourceSensitivity {
    match import(key, work) {
        Ok(imported) => imported.types.sensitivity(imported.root, work),
        Err(reason) => SourceSensitivity::Unknown { reason },
    }
}

pub(crate) fn key_is_coordinate_free(key: &ArgumentKey) -> bool {
    matches!(
        key_sensitivity(key, &mut WorkLimit::new(4096)),
        SourceSensitivity::Absent { .. }
    )
}

pub(crate) fn project_key<'a>(
    key: &'a ArgumentKey,
    path: &[Slot],
    work: &mut WorkLimit,
) -> Result<&'a ArgumentKey, SourceTypesError> {
    let imported = import(key, work)?;
    let mut steps = Vec::new();
    for step in path {
        work.charge(1)?;
        steps.push(match step {
            Slot::Field(label) => {
                work.text(label)?;
                SourcePath::Field(label.clone())
            }
            Slot::Tuple(index) => SourcePath::Tuple(*index),
            Slot::Index(_) | Slot::AnyIndex => SourcePath::Element,
            _ => return Err(SourceTypesError::MissingProjection),
        });
    }
    let id = imported.types.project(imported.root, &steps, work)?;
    imported
        .originals
        .get(&id)
        .copied()
        .ok_or(SourceTypesError::MissingNode)
}
