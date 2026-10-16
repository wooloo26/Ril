//! Sealed evaluator output. Source syntax cannot create an arena entry.
use super::*;
use ril_compiler_core::ids::{ConstGraphId, ConstNodeId, ConstRef};
use ril_ir::{constants::ConstNodeKind, core::Literal as CoreLiteral};

#[derive(Debug, Clone, Default)]
pub(crate) struct ConstantPool {
    pub nodes: Vec<ConstantNode>,
    pub references: BTreeMap<String, ConstRef>,
    /// Type views belong to each evaluated publication, independently of the
    /// shared constant graph node. A weaker alias must not recover a stronger
    /// view merely because both publications have the same object identity.
    pub source_views: BTreeMap<String, std::sync::Arc<crate::sema::model::SourceTypeWitness>>,
    view_names: BTreeMap<(ConstRef, Option<String>), String>,
    collections: BTreeMap<u64, ConstRef>,
    fixed_collections: BTreeMap<u64, u64>,
    float_literals: BTreeMap<(bool, u64), ConstRef>,
    result_nodes: BTreeMap<results::ProducerId, ConstRef>,
}

#[derive(Debug, Clone)]
pub(crate) struct ConstantNode {
    pub kind: ConstNodeKind,
    pub span: Span,
    pub fixed_array_length: Option<u64>,
    pub integer_type: Option<String>,
    pub mutable_fields: BTreeSet<String>,
    pub result_producer: Option<results::ProducerId>,
    pub result_receipt: Option<results::Receipt>,
    pub result_type: Option<Box<TypeExpr>>,
}

impl ConstantPool {
    fn export(
        &mut self,
        value: &StaticValue,
        span: Span,
        layout: TargetLayout,
    ) -> Result<ConstRef> {
        let result_id = if let StaticValue::Result(produced) = value {
            Some(produced.id)
        } else {
            None
        };
        if let Some(reference) = result_id.and_then(|id| self.result_nodes.get(&id)).copied() {
            if let StaticValue::Result(produced) = value
                && let Some(ty) = &produced.ty
            {
                let existing = &mut self.nodes[reference.node.0 as usize].result_type;
                if let Some(old) = existing
                    && canonical_type(old) != canonical_type(ty)
                {
                    return Err(Failure::Unsupported(
                        "one static Result producer requires compatible publication type witnesses"
                            .into(),
                    ));
                }
                *existing = Some(ty.clone());
            }
            return Ok(reference);
        }
        let float_key = if let StaticValue::Float(value, narrow) = value {
            Some((*narrow, value.to_bits()))
        } else {
            None
        };
        if let Some(reference) = float_key.and_then(|key| self.float_literals.get(&key)) {
            return Ok(*reference);
        }
        if let Some(reference) = value
            .collection_id()
            .and_then(|id| self.collections.get(&id))
        {
            return Ok(*reference);
        }
        let kind = match value {
            StaticValue::Integer(value) => ConstNodeKind::Literal(CoreLiteral::Integer {
                value: *value,
                bits: layout.pointer_bits,
                signed: true,
            }),
            StaticValue::TypedInteger(value, bits, signed) => {
                ConstNodeKind::Literal(CoreLiteral::Integer {
                    value: *value,
                    bits: *bits,
                    signed: *signed,
                })
            }
            StaticValue::Float(value, narrow) => ConstNodeKind::Literal(CoreLiteral::Float {
                value: *value,
                bits: if *narrow { 32 } else { 64 },
            }),
            StaticValue::Bool(value) => ConstNodeKind::Literal(CoreLiteral::Bool(*value)),
            StaticValue::Unit => ConstNodeKind::Literal(CoreLiteral::Unit),
            StaticValue::String(value) => {
                ConstNodeKind::Literal(CoreLiteral::String(value.clone()))
            }
            StaticValue::Bytes(value) => ConstNodeKind::Literal(CoreLiteral::Bytes(value.clone())),
            StaticValue::BigInteger(value) => {
                ConstNodeKind::Literal(CoreLiteral::BigInteger(value.to_string()))
            }
            StaticValue::Array(items) | StaticValue::Tuple(items) => {
                let children = items
                    .iter()
                    .map(|child| self.export(child, span, layout))
                    .collect::<Result<_>>()?;
                if matches!(value, StaticValue::Array(_)) {
                    ConstNodeKind::Array(children)
                } else {
                    ConstNodeKind::Tuple(children)
                }
            }
            StaticValue::Map(items) => ConstNodeKind::Map(
                items
                    .iter()
                    .map(|(key, child)| {
                        Ok((
                            self.export(key, span, layout)?,
                            self.export(child, span, layout)?,
                        ))
                    })
                    .collect::<Result<_>>()?,
            ),
            // Slot modes are retained separately from the physical edges.
            StaticValue::Record(fields) => ConstNodeKind::Record(
                fields
                    .iter()
                    .map(|(name, child)| Ok((name.clone(), self.export(child, span, layout)?)))
                    .collect::<Result<_>>()?,
            ),
            StaticValue::Variant(name, values, _)
                if matches!(name.as_str(), "Prelude::Some" | "Prelude::None") =>
            {
                if (name == "Prelude::None" && !values.is_empty())
                    || (name == "Prelude::Some" && values.len() != 1)
                {
                    return Err(Failure::Unsupported("static Option payload witness".into()));
                }
                ConstNodeKind::Variant {
                    tag: name.clone(),
                    payload: values
                        .first()
                        .map(|value| self.export(value, span, layout))
                        .transpose()?,
                }
            }
            StaticValue::Result(produced) => ConstNodeKind::Variant {
                tag: if produced.success {
                    "Prelude::Ok"
                } else {
                    "Prelude::Err"
                }
                .into(),
                payload: Some(self.export(&produced.payload, span, layout)?),
            },
            StaticValue::Type(_) | StaticValue::Callable(_) | StaticValue::Variant(..) => {
                return Err(Failure::Unsupported("static constant graph requires complete ordinary-data type and qualification witnesses".into()));
            }
        };
        let reference = ConstRef {
            graph: ConstGraphId(0),
            node: ConstNodeId(u32::try_from(self.nodes.len()).map_err(|_| {
                Failure::Unsupported("static constant arena identity limit".into())
            })?),
        };
        let fixed_array_length = value
            .collection_id()
            .and_then(|id| self.fixed_collections.get(&id).copied());
        let integer_type = match value {
            StaticValue::Integer(_) => Some("int".into()),
            StaticValue::TypedInteger(_, bits, signed) => {
                Some(format!("{}{bits}", if *signed { "i" } else { "u" }))
            }
            _ => None,
        };
        self.nodes.push(ConstantNode {
            kind,
            span,
            fixed_array_length,
            integer_type,
            mutable_fields: match value {
                StaticValue::Record(record) => record.mutable_fields.clone(),
                _ => BTreeSet::new(),
            },
            result_producer: result_id,
            result_receipt: None,
            result_type: if let StaticValue::Result(produced) = value {
                produced.ty.clone()
            } else {
                None
            },
        });
        if let Some(id) = value.collection_id() {
            self.collections.insert(id, reference);
        }
        if let Some(key) = float_key {
            self.float_literals.insert(key, reference);
        }
        if let Some(id) = result_id {
            self.result_nodes.insert(id, reference);
        }
        Ok(reference)
    }
}

impl Evaluator {
    pub(super) fn seal_result_constants(&self, output: &mut Evaluation) {
        let mut pool = self.constants.borrow_mut();
        for node in &mut pool.nodes {
            if let Some(id) = node.result_producer {
                node.result_receipt = self.results.receipt(id);
                if node.result_receipt.is_none() {
                    output.failure(Failure::Unsupported("pending static Result publication requires a runtime inspection receipt".into()),node.span);
                }
            }
        }
    }
    pub(super) fn numeric_constant(&self, name: &str) -> Option<StaticValue> {
        let pool = self.constants.borrow();
        let reference = pool.references.get(name)?;
        let node = pool.nodes.get(reference.node.0 as usize)?;
        if let ConstNodeKind::Literal(CoreLiteral::Float { value, bits }) = &node.kind {
            return Some(StaticValue::Float(*value, *bits == 32));
        }
        None
    }
    /// Shape constraints belong to storage even when a later expression selects
    /// the same child through a different immutable binding.
    pub(super) fn retain_constant_shape(
        &mut self,
        value: &StaticValue,
        syntax: &TypeExpr,
    ) -> Result<()> {
        if !reference_value(value)
            && !matches!(value, StaticValue::Variant(..) | StaticValue::Result(_))
        {
            return Ok(());
        }
        let syntax = self.resolve_type(syntax, &mut vec![])?;
        self.retain_resolved_shape(value, &syntax)
    }
    /// Publication projects an already evaluated type. Traversing its members
    /// does not invoke a type function a second time or acquire another budget.
    fn retain_resolved_shape(&mut self, value: &StaticValue, syntax: &TypeExpr) -> Result<()> {
        self.charge()?;
        match (value, &syntax.kind) {
            (StaticValue::Result(produced), TypeKind::Name { path, arguments })
                if (path == &["Result"] || path == &["Prelude", "Result"])
                    && arguments.len() == 2 =>
            {
                self.retain_resolved_shape(
                    &produced.payload,
                    &arguments[usize::from(!produced.success)],
                )?;
            }
            (StaticValue::Array(items), TypeKind::Array { element, length }) => {
                if length.is_some() {
                    let mut pool = self.constants.borrow_mut();
                    pool.fixed_collections.insert(items.id, items.len() as u64);
                    if let Some(reference) = pool.collections.get(&items.id).copied() {
                        pool.nodes[reference.node.0 as usize].fixed_array_length =
                            Some(items.len() as u64);
                    }
                }
                for value in items {
                    self.retain_resolved_shape(value, element)?;
                }
            }
            (StaticValue::Tuple(items), TypeKind::Tuple(types)) => {
                for (value, ty) in items.iter().zip(types) {
                    self.retain_resolved_shape(value, ty)?;
                }
            }
            (StaticValue::Map(items), TypeKind::Map { key, value }) => {
                for (k, v) in items {
                    self.retain_resolved_shape(k, key)?;
                    self.retain_resolved_shape(v, value)?;
                }
            }
            (StaticValue::Record(items), TypeKind::Record { fields, .. }) => {
                for field in fields {
                    if let Some(value) = items.get(&field.name) {
                        self.retain_resolved_shape(value, &field.ty)?;
                    }
                }
            }
            (StaticValue::Variant(name, items, _), TypeKind::Optional(inner))
                if name == "Prelude::Some" =>
            {
                for item in items {
                    self.retain_resolved_shape(item, inner)?;
                }
            }
            (StaticValue::Variant(name, items, _), TypeKind::Name { path, arguments })
                if name == "Prelude::Some"
                    && path.last().is_some_and(|name| name == "Option")
                    && arguments.len() == 1 =>
            {
                for item in items {
                    self.retain_resolved_shape(item, &arguments[0])?;
                }
            }
            _ => {}
        }
        Ok(())
    }
    pub(super) fn materialize_graph(&self, value: &StaticValue, span: Span) -> Result<Expr> {
        let source = source_types::view(value).cloned();
        self.budget.work(
            source
                .as_ref()
                .map_or(1, |source| source.key.len() as u64 + 1),
        )?;
        let mut pool = self.constants.borrow_mut();
        let reference = pool.export(value, span, self.layout)?;
        let key = source.as_ref().map(|source| source.key.clone());
        if let Some(name) = pool.view_names.get(&(reference, key.clone())) {
            return Ok(Expr {
                kind: ExprKind::Name(name.clone()),
                span,
            });
        }
        let name = format!(
            "\0ril.const.{}.{}.{}",
            reference.graph.0,
            reference.node.0,
            pool.references.len(),
        );
        pool.references.insert(name.clone(), reference);
        if let Some(source) = source {
            pool.source_views.insert(name.clone(), source);
        }
        pool.view_names.insert((reference, key), name.clone());
        Ok(Expr {
            kind: ExprKind::Name(name),
            span,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_binary_shared_dag_exports_linearly_without_unfolding_its_paths() {
        let span = Span {
            file: ril_compiler_core::source::FileId(0),
            start: 0,
            end: 1,
        };
        let mut value = StaticValue::Integer(7);
        for id in 0..64 {
            value = StaticValue::Array(StaticCollection {
                id,
                source_type: None,
                values: std::sync::Arc::new(vec![value.clone(), value]),
            });
        }
        let mut pool = ConstantPool::default();
        assert!(!contains_type_value(&value));
        assert!(!contains_callable(&value));
        let root = pool
            .export(&value, span, TargetLayout::POINTER64)
            .unwrap_or_else(|_| panic!("ordinary DAG export"));
        // Two scalar copies, then one node for each immutable array identity.
        assert_eq!(pool.nodes.len(), 66);
        let ConstNodeKind::Array(children) = &pool.nodes[root.node.0 as usize].kind else {
            panic!()
        };
        assert_eq!(children[0], children[1]);
    }
}
