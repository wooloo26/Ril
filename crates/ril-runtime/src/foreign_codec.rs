//! Typed value graphs at the isolated host boundary. No address, resource or
//! callable is accepted as ordinary data. Traversal is iterative and preserves
//! sharing/cycles; opaque type envelopes are erased back to their representation.
use crate::{
    heap::{Handle, Object},
    map::OrderedMap,
    value::{Result, Runtime, RuntimeError},
};
use ril_runtime_api::foreign::{
    Field, Graph, Node, NodeId, Signature, StaticArgument, StaticArgumentValue, StaticValue,
    TypeNode, TypeRef,
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
#[cfg(test)]
#[path = "foreign_codec_tests.rs"]
mod tests;

fn invalid(message: impl std::fmt::Display) -> RuntimeError {
    RuntimeError::panic(format!(
        "external value violates its declaration: {message}"
    ))
}
fn shape(signature: &Signature, mut ty: TypeRef) -> Result<(TypeRef, &TypeNode)> {
    let mut seen = BTreeSet::new();
    loop {
        if !seen.insert(ty) {
            return Err(RuntimeError::internal(
                "unproductive external type qualifier cycle",
            ));
        }
        let node = signature
            .arena
            .get(ty as usize)
            .ok_or_else(|| RuntimeError::internal("external type reference is out of bounds"))?;
        if let TypeNode::Immutable(inner) = node {
            ty = *inner;
        } else {
            return Ok((ty, node));
        }
    }
}

pub(crate) fn validate_signature(signature: &Signature) -> Result<()> {
    let valid = |ty: TypeRef| (ty as usize) < signature.arena.len();
    if !signature
        .parameters
        .iter()
        .copied()
        .chain([signature.result])
        .all(valid)
    {
        return Err(RuntimeError::internal("invalid external signature roots"));
    }
    for (id, node) in signature.arena.iter().enumerate() {
        let references = match node {
            TypeNode::Array { element, .. }
            | TypeNode::Set(element)
            | TypeNode::Range(element)
            | TypeNode::Immutable(element) => vec![*element],
            TypeNode::Map { key, value } => vec![*key, *value],
            TypeNode::Tuple(items) => items.clone(),
            TypeNode::Record(fields) => fields.values().copied().collect(),
            TypeNode::Variant(variants) => {
                let mut wire = BTreeSet::new();
                let mut runtime = BTreeSet::new();
                if variants.iter().any(|variant| {
                    variant.wire_tag.is_empty()
                        || variant.runtime_tag.is_empty()
                        || !wire.insert(&variant.wire_tag)
                        || !runtime.insert(&variant.runtime_tag)
                }) {
                    return Err(RuntimeError::internal("ambiguous external variant tags"));
                }
                variants
                    .iter()
                    .flat_map(|variant| variant.fields.iter().copied())
                    .collect()
            }
            TypeNode::Nominal { payload, .. } => vec![*payload],
            TypeNode::OpaqueData { representation, .. } => vec![*representation],
            TypeNode::Integer { bits, .. } if !matches!(bits, 8 | 16 | 32 | 64) => {
                return Err(RuntimeError::internal(
                    "unsupported external integer schema",
                ));
            }
            TypeNode::Float { bits } if !matches!(bits, 32 | 64) => {
                return Err(RuntimeError::internal("unsupported external float schema"));
            }
            TypeNode::Opaque { .. } | TypeNode::Resource { .. } => {
                return Err(RuntimeError::internal(
                    "external schema lacks a concrete ordinary representation",
                ));
            }
            _ => vec![],
        };
        if !references.into_iter().all(valid) {
            return Err(RuntimeError::internal("invalid external type edge"));
        }
        shape(signature, id as u32)?;
    }
    let mut slots = BTreeSet::new();
    for slot in &signature.callbacks {
        if !slot.path.is_empty()
            || !slots.insert(slot.argument)
            || signature
                .parameters
                .get(slot.argument as usize)
                .is_none_or(|&ty| !matches!(shape(signature, ty), Ok((_, TypeNode::Callback))))
        {
            return Err(RuntimeError::internal("invalid external callback slot"));
        }
        if !slot
            .parameters
            .iter()
            .copied()
            .chain([slot.result])
            .all(valid)
        {
            return Err(RuntimeError::internal(
                "invalid external callback signature",
            ));
        }
    }
    for (index, &ty) in signature.parameters.iter().enumerate() {
        if matches!(shape(signature, ty)?, (_, TypeNode::Callback))
            && !slots.contains(&(index as u32))
        {
            return Err(RuntimeError::internal("external callback slot is missing"));
        }
    }
    Ok(())
}

pub(crate) fn validate_static_arguments(
    signature: &Signature,
    arguments: &[StaticArgument],
) -> Result<()> {
    let mut names = BTreeSet::new();
    for argument in arguments {
        if argument.name.is_empty() || !names.insert(&argument.name) {
            return Err(RuntimeError::internal(
                "invalid external static parameter name",
            ));
        }
        match &argument.value {
            StaticArgumentValue::Type { identity, schema } => {
                if identity.is_empty()
                    || schema.is_some_and(|ty| ty as usize >= signature.arena.len())
                {
                    return Err(RuntimeError::internal(
                        "invalid external static type argument",
                    ));
                }
            }
            StaticArgumentValue::Value { identity, value } => {
                if identity.is_empty() {
                    return Err(RuntimeError::internal(
                        "missing external static value identity",
                    ));
                }
                let node = match value {
                    StaticValue::Unit => Node::Unit,
                    StaticValue::Bool(value) => Node::Bool(*value),
                    StaticValue::Integer {
                        decimal,
                        bits,
                        signed,
                    } => Node::Integer {
                        decimal: decimal.clone(),
                        bits: *bits,
                        signed: *signed,
                    },
                    StaticValue::BigInteger(value) => Node::BigInteger(value.clone()),
                    StaticValue::Float { bits, raw } => Node::Float {
                        bits: *bits,
                        raw: *raw,
                    },
                    StaticValue::String(value) => Node::String(value.clone()),
                    StaticValue::Bytes(value) => Node::Bytes(value.clone()),
                };
                Graph {
                    nodes: vec![node],
                    roots: vec![0],
                }
                .validate()
                .map_err(|error| {
                    RuntimeError::internal(format!("invalid external static value: {error}"))
                })?;
            }
            StaticArgumentValue::Effects { identities }
            | StaticArgumentValue::Capabilities { identities } => {
                let mut unique = BTreeSet::new();
                if identities
                    .iter()
                    .any(|identity| identity.is_empty() || !unique.insert(identity))
                {
                    return Err(RuntimeError::internal(
                        "invalid external static row argument",
                    ));
                }
            }
        }
    }
    Ok(())
}

#[derive(Default)]
struct Checked {
    nodes: BTreeSet<NodeId>,
    aliases: BTreeMap<NodeId, NodeId>,
    tags: BTreeMap<NodeId, String>,
}
fn checked(signature: &Signature, graph: &Graph, types: &[TypeRef]) -> Result<Checked> {
    graph.validate().map_err(invalid)?;
    if graph.roots.len() != types.len() {
        return Err(invalid("wrong argument or return arity"));
    }
    let mut seen = BTreeSet::new();
    let mut pending: Vec<_> = graph
        .roots
        .iter()
        .copied()
        .zip(types.iter().copied())
        .collect();
    let mut checked = Checked::default();
    while let Some((id, ty)) = pending.pop() {
        let (ty, expected) = shape(signature, ty)?;
        if !seen.insert((id, ty)) {
            continue;
        }
        checked.nodes.insert(id);
        let node = &graph.nodes[id as usize];
        let mut tag = None;
        match (node, expected) {
            (Node::Unit, TypeNode::Unit)
            | (Node::Bool(_), TypeNode::Bool)
            | (Node::String(_), TypeNode::String)
            | (Node::Bytes(_), TypeNode::Bytes)
            | (Node::BigInteger(_), TypeNode::BigInteger) => {}
            (Node::Integer { bits, signed, .. }, TypeNode::Integer { bits: b, signed: s })
                if bits == b && signed == s => {}
            (Node::Float { bits, .. }, TypeNode::Float { bits: b }) if bits == b => {}
            (Node::Array(items), TypeNode::Array { element, length })
                if length.is_none_or(|length| length == items.len() as u64) =>
            {
                pending.extend(items.iter().map(|&id| (id, *element)))
            }
            (Node::Tuple(items), TypeNode::Tuple(expected)) if items.len() == expected.len() => {
                pending.extend(items.iter().copied().zip(expected.iter().copied()))
            }
            (Node::Record(fields), TypeNode::Record(expected))
                if fields.len() == expected.len() =>
            {
                for field in fields {
                    pending.push((
                        field.node,
                        *expected
                            .get(&field.name)
                            .ok_or_else(|| invalid("unknown record field"))?,
                    ));
                }
            }
            (Node::Map(entries), TypeNode::Map { key, value }) => {
                for &(k, v) in entries {
                    pending.extend([(k, *key), (v, *value)]);
                }
            }
            (Node::Set(items), TypeNode::Set(element)) => {
                pending.extend(items.iter().map(|&id| (id, *element)))
            }
            (Node::Range { lower, upper, .. }, TypeNode::Range(element)) => {
                pending.extend(lower.iter().chain(upper).map(|&id| (id, *element)))
            }
            (Node::Variant { tag: wire, fields }, TypeNode::Variant(variants)) => {
                let variant = variants
                    .iter()
                    .find(|variant| {
                        &variant.wire_tag == wire && variant.fields.len() == fields.len()
                    })
                    .ok_or_else(|| invalid("unknown variant or payload arity"))?;
                tag = Some(&variant.runtime_tag);
                pending.extend(fields.iter().copied().zip(variant.fields.iter().copied()));
            }
            (
                Node::Nominal { tag: wire, payload },
                TypeNode::Nominal {
                    wire_tag,
                    runtime_tag,
                    payload: expected,
                },
            ) if wire == wire_tag => {
                tag = Some(runtime_tag);
                pending.push((*payload, *expected));
            }
            (
                Node::Nominal { tag: wire, payload },
                TypeNode::OpaqueData {
                    wire_tag,
                    representation,
                    ..
                },
            ) if wire == wire_tag => {
                if checked.tags.contains_key(&id) {
                    return Err(invalid(
                        "one node has incompatible nominal and opaque views",
                    ));
                }
                checked.aliases.insert(id, *payload);
                pending.push((*payload, *representation));
            }
            _ => {
                return Err(invalid(format!(
                    "node {id} does not match declared type {ty}"
                )));
            }
        }
        if let Some(tag) = tag {
            if checked.aliases.contains_key(&id)
                || checked
                    .tags
                    .get(&id)
                    .is_some_and(|previous| previous != tag)
            {
                return Err(invalid("incompatible type identities share one node"));
            }
            checked.tags.insert(id, tag.clone());
        }
    }
    Ok(checked)
}
fn canonical_nodes(checked: &Checked) -> Result<BTreeMap<NodeId, NodeId>> {
    let mut canonical = BTreeMap::new();
    for &start in &checked.nodes {
        if canonical.contains_key(&start) {
            continue;
        }
        let mut path = Vec::new();
        let mut visiting = BTreeSet::new();
        let mut cursor = start;
        let destination = loop {
            if let Some(&resolved) = canonical.get(&cursor) {
                break resolved;
            }
            if !checked.nodes.contains(&cursor) {
                return Err(invalid(
                    "opaque representation is outside the checked graph",
                ));
            }
            if !visiting.insert(cursor) {
                return Err(invalid("opaque envelope cycle contains no representation"));
            }
            path.push(cursor);
            if let Some(&next) = checked.aliases.get(&cursor) {
                cursor = next;
            } else {
                break cursor;
            }
        };
        // Every envelope is resolved once. Re-walking the entire chain for
        // each node/edge would make a flat wire graph quadratic to decode.
        canonical.extend(path.into_iter().map(|node| (node, destination)));
    }
    Ok(canonical)
}

pub(crate) fn decode(
    runtime: &mut Runtime,
    signature: &Signature,
    graph: &Graph,
    types: &[TypeRef],
) -> Result<Vec<Handle>> {
    let checked = checked(signature, graph, types)?;
    // Reject unproductive representation cycles before allocating any managed
    // placeholders, even when an earlier graph root is independently valid.
    let canonical = canonical_nodes(&checked)?;
    let mut handles = BTreeMap::new();
    for &id in &checked.nodes {
        if let std::collections::btree_map::Entry::Vacant(entry) = handles.entry(canonical[&id]) {
            entry.insert(runtime.unit()?);
        }
    }
    let handle = |id| -> Result<Handle> { Ok(handles[&canonical[&id]]) };
    for (&id, &destination) in &handles {
        let object = match &graph.nodes[id as usize] {
            Node::Unit => Object::Unit,
            Node::Bool(value) => Object::Bool(*value),
            Node::Integer {
                decimal,
                bits,
                signed,
            } => Object::Integer {
                value: if *signed {
                    decimal.parse::<i128>().map_err(invalid)?
                } else {
                    i128::try_from(decimal.parse::<u128>().map_err(invalid)?).map_err(invalid)?
                },
                bits: *bits,
                signed: *signed,
            },
            Node::BigInteger(decimal) => Object::BigInteger(decimal.parse().map_err(invalid)?),
            Node::Float { raw, bits } => {
                let number = if *bits == 32 {
                    f64::from(f32::from_bits(*raw as u32))
                } else {
                    f64::from_bits(*raw)
                };
                let value = runtime.float(number, *bits)?;
                runtime.heap.get(value)?.clone()
            }
            Node::String(value) => Object::String(value.clone()),
            Node::Bytes(value) => Object::Bytes(value.clone().into()),
            Node::Array(items) => {
                Object::Array(items.iter().copied().map(&handle).collect::<Result<_>>()?)
            }
            Node::Tuple(items) => {
                Object::Tuple(items.iter().copied().map(&handle).collect::<Result<_>>()?)
            }
            Node::Record(fields) => Object::Record(
                fields
                    .iter()
                    .map(|field| Ok((field.name.clone(), handle(field.node)?)))
                    .collect::<Result<_>>()?,
            ),
            Node::Variant { fields, .. } => Object::Variant {
                tag: checked.tags[&id].clone(),
                fields: fields.iter().copied().map(&handle).collect::<Result<_>>()?,
            },
            Node::Nominal { payload, .. } => Object::Nominal {
                tag: checked.tags[&id].clone(),
                payload: handle(*payload)?,
            },
            Node::Range {
                lower,
                upper,
                inclusive,
            } => Object::Range {
                lower: lower.map(handle).transpose()?,
                upper: upper.map(handle).transpose()?,
                inclusive: *inclusive,
            },
            Node::Map(_) => Object::Map(OrderedMap::default()),
            Node::Set(_) => Object::Set(OrderedMap::default()),
            Node::Opaque { .. } => {
                return Err(invalid(
                    "uninterpreted opaque data has no representation contract",
                ));
            }
        };
        *runtime.heap.get_mut(destination)? = object;
    }
    // All key representations are now materialized, including nominal payloads.
    for (&id, &destination) in &handles {
        let entries: Vec<_> = match &graph.nodes[id as usize] {
            Node::Map(entries) => entries.clone(),
            Node::Set(items) => items.iter().map(|&id| (id, id)).collect(),
            _ => continue,
        };
        let mut map = OrderedMap::default();
        for (key, value) in entries {
            let key = handle(key)?;
            let identity = runtime.key(key).map_err(|error| invalid(error.message))?;
            if map.contains(&identity) {
                return Err(invalid("duplicate map or set key"));
            }
            map.set(identity, key, handle(value)?);
        }
        *runtime.heap.get_mut(destination)? = if matches!(graph.nodes[id as usize], Node::Set(_)) {
            Object::Set(map)
        } else {
            Object::Map(map)
        };
    }
    graph.roots.iter().copied().map(handle).collect()
}

pub(crate) fn encode(
    runtime: &Runtime,
    signature: &Signature,
    values: &[(Handle, TypeRef)],
) -> Result<Graph> {
    let mut encoder = Encoder {
        runtime,
        signature,
        graph: Graph {
            nodes: vec![],
            roots: vec![],
        },
        identities: BTreeMap::new(),
        pending: VecDeque::new(),
    };
    for &(value, ty) in values {
        let root = encoder.intern(value, ty)?;
        encoder.graph.roots.push(root);
    }
    while let Some((id, value, ty)) = encoder.pending.pop_front() {
        let node = encoder.node(value, ty)?;
        encoder.graph.nodes[id as usize] = node;
    }
    checked(
        signature,
        &encoder.graph,
        &values.iter().map(|(_, ty)| *ty).collect::<Vec<_>>(),
    )?;
    Ok(encoder.graph)
}
struct Encoder<'a> {
    runtime: &'a Runtime,
    signature: &'a Signature,
    graph: Graph,
    identities: BTreeMap<(Handle, Option<String>), NodeId>,
    pending: VecDeque<(NodeId, Handle, TypeRef)>,
}
impl Encoder<'_> {
    fn intern(&mut self, value: Handle, ty: TypeRef) -> Result<NodeId> {
        let (ty, expected) = shape(self.signature, ty)?;
        let view = match expected {
            TypeNode::OpaqueData { wire_tag, .. } => Some(wire_tag.clone()),
            _ => None,
        };
        if let Some(&id) = self.identities.get(&(value, view.clone())) {
            return Ok(id);
        }
        let id = u32::try_from(self.graph.nodes.len())
            .map_err(|_| invalid("graph exceeds node identity domain"))?;
        self.identities.insert((value, view), id);
        self.graph.nodes.push(Node::Unit);
        self.pending.push_back((id, value, ty));
        Ok(id)
    }
    fn node(&mut self, value: Handle, ty: TypeRef) -> Result<Node> {
        let (_, expected) = shape(self.signature, ty)?;
        if let TypeNode::OpaqueData {
            wire_tag,
            representation,
            ..
        } = expected
        {
            return Ok(Node::Nominal {
                tag: wire_tag.clone(),
                payload: self.intern(value, *representation)?,
            });
        }
        Ok(match (self.runtime.heap.get(value)?.clone(), expected) {
            (Object::Unit, TypeNode::Unit) => Node::Unit,
            (Object::Bool(value), TypeNode::Bool) => Node::Bool(value),
            (
                Object::Integer {
                    value,
                    bits,
                    signed,
                },
                TypeNode::Integer { .. },
            ) => Node::Integer {
                decimal: if signed {
                    value.to_string()
                } else {
                    (value as u128).to_string()
                },
                bits,
                signed,
            },
            (Object::BigInteger(value), TypeNode::BigInteger) => {
                Node::BigInteger(value.to_string())
            }
            (Object::Float { value, bits }, TypeNode::Float { .. }) => Node::Float {
                bits,
                raw: if bits == 32 {
                    u64::from((value as f32).to_bits())
                } else {
                    value.to_bits()
                },
            },
            (Object::String(value), TypeNode::String) => Node::String(value),
            (Object::Bytes(value), TypeNode::Bytes) => Node::Bytes(value.to_vec()),
            (Object::Array(_) | Object::ArrayWindow { .. }, TypeNode::Array { element, .. }) => {
                let items = self
                    .runtime
                    .heap
                    .array_elements(value)?
                    .ok_or_else(|| invalid("array storage"))?
                    .to_vec();
                Node::Array(
                    items
                        .into_iter()
                        .map(|value| self.intern(value, *element))
                        .collect::<Result<_>>()?,
                )
            }
            (Object::Tuple(items), TypeNode::Tuple(types)) if items.len() == types.len() => {
                Node::Tuple(
                    items
                        .into_iter()
                        .zip(types)
                        .map(|(value, &ty)| self.intern(value, ty))
                        .collect::<Result<_>>()?,
                )
            }
            (Object::Record(fields), TypeNode::Record(types)) if fields.len() == types.len() => {
                Node::Record(
                    fields
                        .into_iter()
                        .map(|(name, value)| {
                            let ty = *types.get(&name).ok_or_else(|| invalid("record field"))?;
                            Ok(Field {
                                name,
                                node: self.intern(value, ty)?,
                            })
                        })
                        .collect::<Result<_>>()?,
                )
            }
            (Object::Variant { tag, fields }, TypeNode::Variant(variants)) => {
                let variant = variants
                    .iter()
                    .find(|variant| {
                        variant.runtime_tag == tag && variant.fields.len() == fields.len()
                    })
                    .ok_or_else(|| invalid("variant identity"))?;
                Node::Variant {
                    tag: variant.wire_tag.clone(),
                    fields: fields
                        .into_iter()
                        .zip(&variant.fields)
                        .map(|(value, &ty)| self.intern(value, ty))
                        .collect::<Result<_>>()?,
                }
            }
            (
                Object::Nominal { tag, payload },
                TypeNode::Nominal {
                    wire_tag,
                    runtime_tag,
                    payload: ty,
                },
            ) if &tag == runtime_tag => Node::Nominal {
                tag: wire_tag.clone(),
                payload: self.intern(payload, *ty)?,
            },
            (Object::Map(items), TypeNode::Map { key, value }) => Node::Map(
                items
                    .iter()
                    .map(|(&k, &v)| Ok((self.intern(k, *key)?, self.intern(v, *value)?)))
                    .collect::<Result<_>>()?,
            ),
            (Object::Set(items), TypeNode::Set(element)) => Node::Set(
                items
                    .iter()
                    .map(|(&key, _)| self.intern(key, *element))
                    .collect::<Result<_>>()?,
            ),
            (
                Object::Range {
                    lower,
                    upper,
                    inclusive,
                },
                TypeNode::Range(element),
            ) => Node::Range {
                lower: lower
                    .map(|value| self.intern(value, *element))
                    .transpose()?,
                upper: upper
                    .map(|value| self.intern(value, *element))
                    .transpose()?,
                inclusive,
            },
            _ => return Err(invalid("value is not ordinary data of the declared type")),
        })
    }
}
