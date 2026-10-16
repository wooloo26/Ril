//! One semantic object per evaluated constant identity, irrespective of spans.
use super::*;
use ril_compiler_core::ids::{ConstGraphId, ConstNodeId, ConstRef};
use ril_ir::{constants::ConstNodeKind, core::Literal as L};

impl Checker {
    /// Project solved, invariant collection types into the arena certificate.
    /// This fills type holes only; node identities and authority never change.
    pub(super) fn finish_constant_types(
        &mut self,
        pool: &crate::static_eval::constants::ConstantPool,
    ) {
        for (index, node) in pool.nodes.iter().enumerate() {
            let child = |reference: &ConstRef| {
                self.constant_values[reference.node.0 as usize]
                    .value
                    .ty
                    .clone()
            };
            let shape = match &node.kind {
                ConstNodeKind::Array(items) => {
                    Ty::Array(Box::new(items.iter().fold(Ty::Unknown, |ty, reference| {
                        join_type_holes(&ty, &child(reference))
                    })))
                }
                ConstNodeKind::Tuple(items) => Ty::Tuple(items.iter().map(child).collect()),
                ConstNodeKind::Map(items) => Ty::Map(
                    Box::new(items.iter().fold(Ty::Unknown, |ty, (key, _)| {
                        join_type_holes(&ty, &child(key))
                    })),
                    Box::new(items.iter().fold(Ty::Unknown, |ty, (_, value)| {
                        join_type_holes(&ty, &child(value))
                    })),
                ),
                ConstNodeKind::Record(fields) => Ty::Record(
                    fields
                        .iter()
                        .map(|(name, reference)| {
                            (
                                name.clone(),
                                (node.mutable_fields.contains(name), child(reference)),
                            )
                        })
                        .collect(),
                ),
                ConstNodeKind::Variant { tag, payload } => {
                    let payload = Box::new(payload.as_ref().map(child).unwrap_or(Ty::Unknown));
                    match tag.as_str() {
                        "Prelude::Ok" => Ty::Result(payload, Box::new(Ty::Unknown)),
                        "Prelude::Err" => Ty::Result(Box::new(Ty::Unknown), payload),
                        _ => Ty::Optional(payload),
                    }
                }
                ConstNodeKind::Literal(_) => self.constant_values[index].value.ty.clone(),
            };
            let value = &self.constant_values[index].value;
            let inferred = join_type_holes(&self.collection_type(value), &shape);
            let ty = join_type_holes(&value.ty, &inferred);
            self.constant_values[index].value.ty = ty;
            if let ConstNodeKind::Variant {
                payload: Some(reference),
                tag,
            } = &node.kind
            {
                let payload = Box::new(
                    self.constant_values[reference.node.0 as usize]
                        .value
                        .clone(),
                );
                match tag.as_str() {
                    "Prelude::Ok" => {
                        self.constant_values[index].value.result_payload = Some(payload.clone());
                        self.constant_values[index].value.result_success = Some(payload);
                    }
                    "Prelude::Err" => {
                        self.constant_values[index].value.result_payload = Some(payload.clone());
                        self.constant_values[index].value.result_error = Some(payload);
                    }
                    _ => self.constant_values[index].value.option_payload = Some(payload),
                }
            }
        }
    }

    pub(super) fn install_constants(&mut self, pool: &crate::static_eval::constants::ConstantPool) {
        for (index, constant) in pool.nodes.iter().enumerate() {
            let span = constant.span;
            let cause = self.cause(
                CauseKind::Source,
                span,
                "evaluated immutable constant graph",
                [],
            );
            let child = |reference: &ConstRef| {
                assert_eq!(reference.graph, ConstGraphId(0));
                assert!(
                    (reference.node.0 as usize) < index,
                    "constant arena must be topological"
                );
                self.constant_values[reference.node.0 as usize]
                    .value
                    .clone()
            };
            let (ty, children, scalar) = match &constant.kind {
                ConstNodeKind::Literal(literal) => {
                    let (ty, fact) = match literal {
                        L::Unit => (Ty::Unit, Some(Constant::Unit)),
                        L::Bool(value) => (Ty::Bool, Some(Constant::Bool(*value))),
                        L::Integer { value, .. } => (
                            Ty::Int(
                                constant
                                    .integer_type
                                    .clone()
                                    .expect("static integer type witness"),
                            ),
                            Some(Constant::Integer(*value)),
                        ),
                        L::Float { bits, .. } => (Ty::Float(format!("f{bits}")), None),
                        L::BigInteger(_) => (Ty::Int("bigint".into()), None),
                        L::String(_) => (Ty::Str, None),
                        L::Bytes(_) => (Ty::Bytes, None),
                    };
                    (ty.clone(), vec![], Some(Value::scalar(ty, fact, cause)))
                }
                ConstNodeKind::Tuple(items) | ConstNodeKind::Array(items) => {
                    let tuple = matches!(constant.kind, ConstNodeKind::Tuple(_));
                    let values: Vec<_> = items.iter().map(child).collect();
                    let ty = if tuple {
                        Ty::Tuple(values.iter().map(|value| value.ty.clone()).collect())
                    } else {
                        Ty::Array(Box::new(
                            values
                                .iter()
                                .fold(Ty::Unknown, |ty, value| join_type_holes(&ty, &value.ty)),
                        ))
                    };
                    let children = values
                        .into_iter()
                        .enumerate()
                        .map(|(i, value)| {
                            (
                                if tuple {
                                    Slot::Tuple(i as u32)
                                } else {
                                    Slot::Index(i as i64)
                                },
                                value,
                            )
                        })
                        .collect();
                    (ty, children, None)
                }
                ConstNodeKind::Map(items) => {
                    let values: Vec<_> = items
                        .iter()
                        .map(|(key, value)| (child(key), child(value)))
                        .collect();
                    let ty = Ty::Map(
                        Box::new(
                            values
                                .iter()
                                .fold(Ty::Unknown, |ty, (key, _)| join_type_holes(&ty, &key.ty)),
                        ),
                        Box::new(values.iter().fold(Ty::Unknown, |ty, (_, value)| {
                            join_type_holes(&ty, &value.ty)
                        })),
                    );
                    let mut children = Vec::new();
                    let mut keys: Option<Value> = None;
                    for (i, (key, value)) in values.into_iter().enumerate() {
                        keys = Some(if let Some(old) = keys {
                            old.join(&key, self.choice(), cause)
                        } else {
                            key
                        });
                        children.push((Slot::Index(i as i64), value));
                    }
                    if let Some(keys) = keys {
                        children.push((Slot::Field("key".into()), keys));
                    }
                    (ty, children, None)
                }
                ConstNodeKind::Record(fields) => {
                    let children: Vec<_> = fields
                        .iter()
                        .map(|(name, reference)| (Slot::Field(name.clone()), child(reference)))
                        .collect();
                    let ty = Ty::Record(
                        fields
                            .iter()
                            .map(|(name, reference)| {
                                (
                                    name.clone(),
                                    (constant.mutable_fields.contains(name), child(reference).ty),
                                )
                            })
                            .collect(),
                    );
                    (ty, children, None)
                }
                ConstNodeKind::Variant { tag, payload } => {
                    let mut value = payload
                        .as_ref()
                        .map(child)
                        .unwrap_or_else(|| Value::scalar(Ty::Unknown, None, cause));
                    if matches!(tag.as_str(), "Prelude::Ok" | "Prelude::Err") {
                        let receipt = constant.result_receipt.as_ref().expect(
                            "Result constant requires its private static inspection receipt",
                        );
                        let mut value =
                            self.checked_static_result(tag == "Prelude::Ok", value, receipt);
                        if let Some(ty) = &constant.result_type {
                            value.ty = self.ty(ty);
                        }
                        (value.ty.clone(), vec![], Some(value))
                    } else {
                        let ty = Ty::Optional(Box::new(value.ty.clone()));
                        value.option_payload = payload.map(|_| Box::new(value.clone()));
                        value.option_tag = Some(tag == "Prelude::Some");
                        value.outer_results.clear();
                        value.must_outer_results.clear();
                        value.result_payload = None;
                        value.result_success = None;
                        value.result_error = None;
                        value.result_tag = None;
                        value.ty = ty.clone();
                        value.constant = None;
                        (ty, vec![], Some(value))
                    }
                }
            };
            let mut value = if let Some(scalar) = scalar {
                scalar
            } else {
                let site = SiteId(self.next_site);
                self.next_site = self
                    .next_site
                    .checked_add(1)
                    .expect("constant site identity exhausted");
                let node = self.allocate_site(span, site, ScopeId(0));
                let mut value = Value::reference(ty.clone(), node, cause);
                self.storage_types.insert(node, ty);
                if let ConstNodeKind::Array(items) = &constant.kind {
                    self.array_lengths.insert(node, Some(items.len() as u64));
                    if constant.fixed_array_length.is_some() {
                        self.fixed_arrays.insert(node);
                    }
                }
                for (slot, child) in children {
                    value.results.extend(child.results.iter().copied());
                    value
                        .must_results
                        .extend(child.must_results.iter().copied());
                    self.store_field(node, slot, child);
                }
                value
            };
            value.permission = Permission::Read;
            value.publication = Publication::Immutable;
            value.construction = false;
            value.stable = true;
            if let ConstNodeKind::Literal(L::String(text)) = &constant.kind {
                value.static_coordinate = Some(StaticCoordinate::Label(text.clone()));
            }
            self.constant_values.push(super::super::ConstantValue {
                reference: ConstRef {
                    graph: ConstGraphId(0),
                    node: ConstNodeId(index as u32),
                },
                value,
                span,
            });
        }
        self.constant_references = pool.references.clone();
        self.constant_source_views = pool.source_views.clone();
    }
}
