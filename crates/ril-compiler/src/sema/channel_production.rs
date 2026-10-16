//! Bounded completeness of ordinary Result production in one frozen carrier.
//! Type absence is a structural property; it grants no copy or access rights.
use super::{
    copy_contract::CopyValueSnapshot,
    facts::{Multiplicity, NodeId, OriginKind, Slot},
    model::{ConstructorInfo, Ty, TypeArgument, Value},
};
use ril_syntax::ast::{TypeDeclaration, TypeExpr, TypeKind};
use std::collections::{BTreeMap, BTreeSet};
#[path = "channel_production_cases.rs"]
mod conditional;
pub(super) use conditional::{ProductionCase, cases};

enum Shape {
    Free,
    Result([bool; 2]),
    Option,
    Fields(Vec<Slot>),
    Array,
    Map,
    Variant,
    Unknown,
}
struct Types<'a> {
    declarations: &'a BTreeMap<String, TypeDeclaration>,
    constructors: &'a BTreeMap<String, ConstructorInfo>,
    active: BTreeSet<(String, Vec<bool>)>,
    complete: BTreeMap<(String, Vec<bool>), bool>,
    cycles: usize,
    work: usize,
}
impl Types<'_> {
    fn charge(&mut self, depth: usize) -> bool {
        if depth > 128 || self.work == 0 {
            return false;
        }
        self.work -= 1;
        true
    }
    fn free_ty(&mut self, ty: &Ty, depth: usize) -> bool {
        if !self.charge(depth) {
            return false;
        }
        match ty {
            Ty::Result(..)
            | Ty::Unknown
            | Ty::NumericHole(_)
            | Ty::Generic(_)
            | Ty::Projection { .. }
            | Ty::OpenRecord { .. }
            | Ty::Callable(..) => false,
            Ty::Optional(inner)
            | Ty::Immutable(inner)
            | Ty::Array(inner)
            | Ty::Set(inner)
            | Ty::Range(inner) => self.free_ty(inner, depth + 1),
            Ty::Map(key, value) => self.free_ty(key, depth + 1) && self.free_ty(value, depth + 1),
            Ty::Tuple(items) => items.iter().all(|item| self.free_ty(item, depth + 1)),
            Ty::Record(fields) => fields
                .values()
                .all(|(_, field)| self.free_ty(field, depth + 1)),
            Ty::Named(name) => self.free_name(name, &[], depth + 1) || ty.scalar(),
            Ty::Applied {
                constructor,
                arguments,
            } => {
                if matches!(
                    constructor.as_str(),
                    "Channel::Sender" | "Channel::Detached"
                ) {
                    return true;
                }
                let free = arguments
                    .iter()
                    .map(|argument| match argument {
                        TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. } => {
                            self.free_ty(ty, depth + 1)
                        }
                        TypeArgument::Static(_) => true,
                        TypeArgument::Symbolic(_) => false,
                    })
                    .collect::<Vec<_>>();
                self.free_name(constructor, &free, depth + 1)
            }
            _ => ty.scalar(),
        }
    }
    fn free_name(&mut self, name: &str, arguments: &[bool], depth: usize) -> bool {
        if !self.charge(depth) {
            return false;
        }
        let key = (name.to_owned(), arguments.to_vec());
        if let Some(complete) = self.complete.get(&key) {
            return *complete;
        }
        if !self.active.insert(key.clone()) {
            self.cycles = self.cycles.saturating_add(1);
            return true;
        }
        let cycles = self.cycles;
        let result = if let Some(declaration) = self.declarations.get(name) {
            if declaration.opaque || declaration.generics.len() != arguments.len() {
                false
            } else {
                let free = declaration
                    .generics
                    .iter()
                    .zip(arguments)
                    .filter_map(|(parameter, free)| free.then_some(parameter.name.clone()))
                    .collect::<BTreeSet<_>>();
                declaration
                    .value
                    .as_ref()
                    .is_none_or(|body| self.free_syntax(body, &free, depth + 1))
                    && declaration.variants.iter().all(|variant| {
                        variant
                            .payload
                            .as_ref()
                            .is_none_or(|payload| self.free_syntax(payload, &free, depth + 1))
                    })
            }
        } else {
            let constructors = self
                .constructors
                .values()
                .filter(|constructor| constructor.owner == Ty::Named(name.into()))
                .collect::<Vec<_>>();
            !constructors.is_empty()
                && constructors.into_iter().all(|constructor| {
                    !constructor.has_payload || self.free_ty(&constructor.payload, depth + 1)
                })
        };
        self.active.remove(&key);
        // A provisional coinductive backedge cannot cache an inner success:
        // an outer sibling may still contain a Result. Acyclic shared diamonds
        // are cached, keeping their absence scan linear in declaration count.
        if !result || cycles == self.cycles {
            self.complete.insert(key, result);
        }
        result
    }
    fn free_syntax(&mut self, syntax: &TypeExpr, free: &BTreeSet<String>, depth: usize) -> bool {
        if !self.charge(depth) {
            return false;
        }
        match &syntax.kind {
            TypeKind::Name { path, arguments } => {
                let name = path.join("::");
                let builtin = name.strip_prefix("Prelude::").unwrap_or(&name);
                if matches!(builtin, "Channel::Sender" | "Channel::Detached") {
                    return true;
                }
                if builtin == "Result" {
                    return false;
                }
                if arguments.is_empty() && (free.contains(&name) || primitive(builtin)) {
                    return true;
                }
                let arguments = arguments
                    .iter()
                    .map(|argument| self.free_syntax(argument, free, depth + 1))
                    .collect::<Vec<_>>();
                if matches!(builtin, "Option" | "Immut" | "Set" | "Range") {
                    return arguments.iter().all(|free| *free);
                }
                self.free_name(&name, &arguments, depth + 1)
            }
            TypeKind::Optional(inner)
            | TypeKind::Rest(inner)
            | TypeKind::Array { element: inner, .. } => self.free_syntax(inner, free, depth + 1),
            TypeKind::Map { key, value } => {
                self.free_syntax(key, free, depth + 1) && self.free_syntax(value, free, depth + 1)
            }
            TypeKind::Tuple(items) => items
                .iter()
                .all(|item| self.free_syntax(item, free, depth + 1)),
            TypeKind::Record { fields, row } => {
                row.is_none()
                    && fields
                        .iter()
                        .all(|field| self.free_syntax(&field.ty, free, depth + 1))
            }
            _ => false,
        }
    }
    fn shape_ty(&mut self, ty: &Ty, depth: usize) -> Shape {
        if !self.charge(depth) {
            return Shape::Unknown;
        }
        if self.free_ty(ty, depth + 1) {
            return Shape::Free;
        }
        match ty {
            Ty::Result(ok, error) => {
                Shape::Result([self.free_ty(error, depth + 1), self.free_ty(ok, depth + 1)])
            }
            Ty::Immutable(inner) => self.shape_ty(inner, depth + 1),
            Ty::Optional(_) => Shape::Option,
            Ty::Record(fields) => Shape::Fields(
                fields
                    .keys()
                    .map(|name| Slot::Field(name.clone()))
                    .collect(),
            ),
            Ty::Tuple(items) => Shape::Fields(
                (0..items.len())
                    .map(|index| Slot::Tuple(index as u32))
                    .collect(),
            ),
            Ty::Array(_) => Shape::Array,
            Ty::Map(key, _) if self.free_ty(key, depth + 1) => Shape::Map,
            Ty::Named(name) => self.shape_name(name, &[], depth + 1),
            Ty::Applied {
                constructor,
                arguments,
            } => {
                let free = arguments
                    .iter()
                    .map(|argument| match argument {
                        TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. } => {
                            self.free_ty(ty, depth + 1)
                        }
                        TypeArgument::Static(_) => true,
                        _ => false,
                    })
                    .collect::<Vec<_>>();
                self.shape_name(constructor, &free, depth + 1)
            }
            _ => Shape::Unknown,
        }
    }
    fn shape_name(&mut self, name: &str, arguments: &[bool], depth: usize) -> Shape {
        if !self.charge(depth) {
            return Shape::Unknown;
        }
        let Some(declaration) = self.declarations.get(name) else {
            return Shape::Variant;
        };
        if declaration.generics.len() != arguments.len() || declaration.opaque {
            return Shape::Unknown;
        }
        let free = declaration
            .generics
            .iter()
            .zip(arguments)
            .filter_map(|(parameter, free)| free.then_some(parameter.name.clone()))
            .collect();
        match &declaration.value {
            Some(body) => self.shape_syntax(body, &free, depth + 1),
            None if !declaration.variants.is_empty() => Shape::Variant,
            _ => Shape::Unknown,
        }
    }
    fn shape_syntax(&mut self, syntax: &TypeExpr, free: &BTreeSet<String>, depth: usize) -> Shape {
        if !self.charge(depth) {
            return Shape::Unknown;
        }
        match &syntax.kind {
            TypeKind::Name { path, arguments } => {
                let name = path.join("::");
                let builtin = name.strip_prefix("Prelude::").unwrap_or(&name);
                if builtin == "Result" && arguments.len() == 2 {
                    return Shape::Result([
                        self.free_syntax(&arguments[1], free, depth + 1),
                        self.free_syntax(&arguments[0], free, depth + 1),
                    ]);
                }
                if builtin == "Option" {
                    return Shape::Option;
                }
                if builtin == "Immut" && arguments.len() == 1 {
                    return self.shape_syntax(&arguments[0], free, depth + 1);
                }
                let arguments = arguments
                    .iter()
                    .map(|argument| self.free_syntax(argument, free, depth + 1))
                    .collect::<Vec<_>>();
                self.shape_name(&name, &arguments, depth + 1)
            }
            TypeKind::Optional(_) => Shape::Option,
            TypeKind::Array { .. } => Shape::Array,
            TypeKind::Map { key, .. } if self.free_syntax(key, free, depth + 1) => Shape::Map,
            TypeKind::Record { fields, row: None } => Shape::Fields(
                fields
                    .iter()
                    .map(|field| Slot::Field(field.name.clone()))
                    .collect(),
            ),
            TypeKind::Tuple(items) => Shape::Fields(
                (0..items.len())
                    .map(|index| Slot::Tuple(index as u32))
                    .collect(),
            ),
            _ => Shape::Unknown,
        }
    }
}
fn primitive(name: &str) -> bool {
    matches!(
        name,
        "bool"
            | "int"
            | "float"
            | "str"
            | "bytes"
            | "rune"
            | "never"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "f32"
            | "f64"
    )
}

pub(super) fn complete(
    snapshot: &CopyValueSnapshot,
    declarations: &BTreeMap<String, TypeDeclaration>,
    constructors: &BTreeMap<String, ConstructorInfo>,
) -> bool {
    fn visit(
        value: &Value,
        snapshot: &CopyValueSnapshot,
        types: &mut Types<'_>,
        active: &mut BTreeSet<NodeId>,
        depth: usize,
    ) -> Option<BTreeSet<u32>> {
        if !types.charge(depth) {
            return None;
        }
        let mut producers = BTreeSet::new();
        match types.shape_ty(&value.ty, depth + 1) {
            Shape::Free => return value.results.is_empty().then_some(producers),
            Shape::Result(free) => {
                if value.outer_results.is_empty() || value.outer_results != value.must_outer_results
                {
                    return None;
                }
                producers.extend(&value.outer_results);
                for success in [false, true] {
                    if value.result_tag.is_some_and(|known| known != success) {
                        continue;
                    }
                    let payload = (if success {
                        value.result_success.as_deref()
                    } else {
                        value.result_error.as_deref()
                    })
                    .or_else(|| {
                        (value.result_tag == Some(success))
                            .then_some(value.result_payload.as_deref())
                            .flatten()
                    });
                    if let Some(payload) = payload {
                        producers.extend(visit(payload, snapshot, types, active, depth + 1)?);
                    } else if !free[usize::from(success)] {
                        return None;
                    }
                }
            }
            Shape::Option => match value.option_tag {
                Some(false) => {}
                Some(true) => producers.extend(visit(
                    value.option_payload.as_deref()?,
                    snapshot,
                    types,
                    active,
                    depth + 1,
                )?),
                None => {
                    value.option_identity?;
                    producers.extend(visit(
                        value.option_payload.as_deref()?,
                        snapshot,
                        types,
                        active,
                        depth + 1,
                    )?);
                }
            },
            Shape::Variant => {
                value.variant_tag.as_ref()?;
                producers.extend(visit(
                    value.variant_payload.as_deref()?,
                    snapshot,
                    types,
                    active,
                    depth + 1,
                )?);
            }
            shape @ (Shape::Fields(_) | Shape::Array | Shape::Map) => {
                if value.origins.nodes.is_empty() {
                    return None;
                }
                for origin in &value.origins.nodes {
                    if !active.insert(*origin) {
                        return None;
                    }
                    let node = snapshot.nodes.iter().find(|node| node.origin == *origin)?;
                    if node.fact.multiplicity != Multiplicity::One {
                        return None;
                    }
                    let slots = match &shape {
                        Shape::Fields(slots) => slots.clone(),
                        Shape::Array => {
                            let length = node.length.flatten()?;
                            if length > 4096
                                || node.fields.iter().any(|(slot, _)| *slot == Slot::AnyIndex)
                            {
                                return None;
                            }
                            (0..length).map(|index| Slot::Index(index as i64)).collect()
                        }
                        Shape::Map => {
                            if !matches!(node.fact.kind, OriginKind::Fresh(_))
                                || node.fields.iter().any(|(slot, _)| *slot == Slot::AnyIndex)
                            {
                                return None;
                            }
                            let length = node
                                .fields
                                .iter()
                                .filter(|(slot, _)| matches!(slot, Slot::Index(_)))
                                .count();
                            (0..length).map(|index| Slot::Index(index as i64)).collect()
                        }
                        _ => unreachable!(),
                    };
                    for slot in slots {
                        let child = node
                            .fields
                            .iter()
                            .find_map(|(actual, child)| (*actual == slot).then_some(child))?;
                        producers.extend(visit(child, snapshot, types, active, depth + 1)?);
                    }
                    active.remove(origin);
                }
            }
            Shape::Unknown => return None,
        }
        (producers == value.results).then_some(producers)
    }
    visit(
        &snapshot.value,
        snapshot,
        &mut Types {
            declarations,
            constructors,
            active: BTreeSet::new(),
            complete: BTreeMap::new(),
            cycles: 0,
            work: 4096,
        },
        &mut BTreeSet::new(),
        0,
    )
    .is_some()
}
