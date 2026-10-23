//! Array cardinality proofs belong to storage nodes. A summary element says
//! nothing about the number of elements, including whether the array is empty.
use super::*;

impl Checker {
    pub(super) fn preview_pattern_subject(
        &mut self,
        subject: &Value,
        packet: &EvaluatedValue,
        span: Span,
    ) -> Value {
        let mut formal =
            self.formal_value(subject.ty.clone(), u32::MAX, span, &mut BTreeSet::new());
        // An excluded tag supplies no actual payload and cannot restore a
        // stronger access view while its syntax is checked.
        formal.permission = formal.permission.meet(subject.permission);
        formal.publication = if subject.publication == Publication::Immutable {
            Publication::Immutable
        } else {
            Publication::Live
        };
        let mut lease = self.application_effect.lease_work(16384);
        let shapes = (|| {
            let source = packet.input_source(
                crate::sema::source_types_ref::SourceTypesRef::Live(
                    self.type_source.storage.live_types(),
                ),
                lease.work(),
            )?;
            let Some((schema, environment)) = source.into_known() else {
                return Ok(BTreeMap::new());
            };
            if environment.is_poisoned() {
                return Err(crate::sema::source_types::SourceTypesError::Unresolved);
            }
            crate::sema::source_shapes::assumed_array_lengths(
                &schema,
                &formal,
                &self.heap,
                &self.fields,
                lease.work(),
            )
        })();
        let returned = self.application_effect.return_work(lease);
        match shapes.and_then(|shapes| returned.map(|()| shapes)) {
            Ok(shapes) => {
                if !self.application_effect.admit(shapes.len()) {
                    self.unsupported(span, "pattern shape installation exceeded its work bound");
                    return formal;
                }
                if shapes.iter().any(|(node, length)| {
                    self.array_lengths
                        .get(node)
                        .is_some_and(|prior| prior.is_some_and(|prior| prior != *length))
                }) {
                    self.unsupported(
                        span,
                        "pattern Source shape conflicts with an existing symbolic constraint",
                    );
                    return formal;
                }
                for (node, length) in shapes {
                    self.array_lengths.insert(node, Some(length));
                    self.fixed_arrays.insert(node);
                    if length == 1 {
                        self.prove_single_formal_member(node);
                    }
                }
            }
            Err(error) => self.unsupported(
                span,
                format!("pattern preview needs its original Source shape constraints: {error}"),
            ),
        }
        formal
    }

    pub(super) fn known_array_length(&self, value: &Value) -> Option<u64> {
        let mut common = None;
        if value.origins.nodes.is_empty() {
            return None;
        }
        for node in &value.origins.nodes {
            let length = if let Some(length) = self.array_lengths.get(node) {
                (*length)?
            } else {
                if matches!(self.heap.nodes[node.0 as usize].kind, OriginKind::Older(_)) {
                    return None;
                }
                let mut indices = BTreeSet::new();
                for (parent, slot) in self.fields.keys() {
                    if parent != node {
                        continue;
                    }
                    match slot {
                        Slot::AnyIndex => return None,
                        Slot::Index(index) => {
                            indices.insert(*index);
                        }
                        _ => {}
                    }
                }
                if !indices.iter().copied().eq(0..indices.len() as i64) {
                    return None;
                }
                indices.len() as u64
            };
            if common.is_some_and(|common| common != length) {
                return None;
            }
            common = Some(length);
        }
        common
    }

    pub(super) fn array_shape(&mut self, value: &Value, syntax: &TypeExpr, _frame: &mut Frame) {
        self.array_shape_inner(value, syntax, &mut BTreeSet::new(), false);
    }
    pub(super) fn promise_array_shape(
        &mut self,
        value: &Value,
        syntax: &TypeExpr,
        _frame: &mut Frame,
    ) {
        self.array_shape_inner(value, syntax, &mut BTreeSet::new(), true);
    }

    fn array_shape_inner(
        &mut self,
        value: &Value,
        syntax: &TypeExpr,
        seen: &mut BTreeSet<(NodeId, u32, u32, u32)>,
        promise: bool,
    ) {
        if value.ty == Ty::Never {
            return;
        }
        // Immut changes authority, not physical cardinality. Recurse before
        // deduplication: synthesized wrapper and inner syntax can share a span.
        if let TypeKind::Name { path, arguments } = &syntax.kind
            && matches!(path.join("::").as_str(), "Immut" | "Prelude::Immut")
            && let [inner] = arguments.as_slice()
        {
            self.array_shape_inner(value, inner, seen, promise);
            return;
        }
        let mut any_new = value.origins.nodes.is_empty();
        for node in &value.origins.nodes {
            any_new |= seen.insert((
                *node,
                syntax.span.file.0,
                syntax.span.start,
                syntax.span.end,
            ));
        }
        if !any_new {
            return;
        }
        match &syntax.kind {
            TypeKind::Name { path, arguments } if arguments.is_empty() => {
                let name = path.join("::");
                if let Some(declaration) = self.types.get(&name).cloned() {
                    if declaration.nominal {
                        if let Some(ty) = &declaration.value
                            && contains_fixed_array(ty, &self.types, &mut BTreeSet::new())
                        {
                            if let Some(payload) = value.variant_witness(&name) {
                                self.array_shape_inner(payload, ty, seen, promise);
                            } else {
                                self.unsupported(
                                    syntax.span,
                                    "nominal fixed array representation needs its payload witness",
                                );
                            }
                        }
                    } else if !declaration.variants.is_empty() {
                        for variant in &declaration.variants {
                            let tag = format!("{name}::{}", variant.name);
                            if value
                                .variant_tag
                                .as_ref()
                                .is_some_and(|actual| actual != &tag)
                            {
                                continue;
                            }
                            let Some(ty) = &variant.payload else {
                                continue;
                            };
                            if !contains_fixed_array(ty, &self.types, &mut BTreeSet::new()) {
                                continue;
                            }
                            let payloads = if let Some(payload) = value.variant_witness(&tag) {
                                vec![payload.clone()]
                            } else {
                                self.shape_children(value, Slot::Field(format!("$variant:{tag}")))
                            };
                            if payloads.is_empty() {
                                self.unsupported(syntax.span,"sum fixed array representation needs its variant-specific witness");
                            }
                            for payload in payloads {
                                self.array_shape_inner(&payload, ty, seen, promise);
                            }
                        }
                    } else if (!declaration.opaque || declaration.span.file == syntax.span.file)
                        && let Some(ty) = &declaration.value
                    {
                        self.array_shape_inner(value, ty, seen, promise);
                    }
                }
            }
            TypeKind::Array { element, length } => {
                if let Some(length) = length {
                    let required = match length_literal(length, self.layout.pointer_bits) {
                        Ok(Some(length)) => length,
                        Ok(None) => {
                            self.unsupported(
                                length.span,
                                "fixed array length requires a verified static integer expression",
                            );
                            return;
                        }
                        Err(code) => {
                            self.error(
                                code,
                                length.span,
                                "invalid fixed array length sort or range",
                                [value.cause],
                            );
                            return;
                        }
                    };
                    match if promise {
                        Some(required)
                    } else {
                        self.known_array_length(value)
                    } {
                        Some(actual) if actual == required => {
                            for node in &value.origins.nodes {
                                self.array_lengths.insert(*node, Some(required));
                                self.fixed_arrays.insert(*node);
                                if required == 1 {
                                    self.prove_single_formal_member(*node);
                                }
                            }
                        }
                        Some(_) => self.error(
                            "E0301",
                            syntax.span,
                            "array cardinality does not satisfy its fixed type",
                            [value.cause],
                        ),
                        None => self.unsupported(
                            syntax.span,
                            "fixed array cardinality has no exact storage proof",
                        ),
                    }
                }
                let children: Vec<_> = value
                    .origins
                    .nodes
                    .iter()
                    .flat_map(|node| {
                        self.fields
                            .iter()
                            .filter_map(move |((parent, slot), value)| {
                                (*parent == *node
                                    && matches!(slot, Slot::Index(_) | Slot::AnyIndex))
                                .then_some(value.clone())
                            })
                    })
                    .collect();
                for child in children {
                    self.array_shape_inner(&child, element, seen, promise);
                }
            }
            TypeKind::Tuple(items) => {
                for (index, ty) in items.iter().enumerate() {
                    let children = self.shape_children(value, Slot::Tuple(index as u32));
                    for child in children {
                        self.array_shape_inner(&child, ty, seen, promise);
                    }
                }
            }
            TypeKind::Record { fields, .. } => {
                for field in fields {
                    let children = self.shape_children(value, Slot::Field(field.name.clone()));
                    for child in children {
                        self.array_shape_inner(&child, &field.ty, seen, promise);
                    }
                }
            }
            TypeKind::Optional(inner) => {
                if let Some(payload) = &value.option_payload {
                    self.array_shape_inner(payload, inner, seen, promise);
                } else if value.option_tag != Some(false)
                    && contains_fixed_array(inner, &self.types, &mut BTreeSet::new())
                {
                    self.unsupported(
                        syntax.span,
                        "optional fixed array payload needs a tag-specific shape proof",
                    );
                }
            }
            TypeKind::Name { path, arguments }
                if path
                    .join("::")
                    .strip_prefix("Prelude::")
                    .unwrap_or(&path.join("::"))
                    == "Option"
                    && arguments.len() == 1 =>
            {
                if let Some(payload) = &value.option_payload {
                    self.array_shape_inner(payload, &arguments[0], seen, promise);
                } else if value.option_tag != Some(false)
                    && contains_fixed_array(&arguments[0], &self.types, &mut BTreeSet::new())
                {
                    self.unsupported(
                        syntax.span,
                        "optional fixed array payload needs a tag-specific shape proof",
                    );
                }
            }
            TypeKind::Name { path, arguments }
                if path
                    .join("::")
                    .strip_prefix("Prelude::")
                    .unwrap_or(&path.join("::"))
                    == "Result"
                    && arguments.len() == 2 =>
            {
                for (index, payload) in [&value.result_success, &value.result_error]
                    .into_iter()
                    .enumerate()
                {
                    let payload = payload.as_ref().or_else(|| {
                        (value.result_tag == Some(index == 0))
                            .then_some(value.result_payload.as_ref())
                            .flatten()
                    });
                    if let Some(payload) = payload {
                        self.array_shape_inner(payload, &arguments[index], seen, promise);
                    } else if value.result_tag != Some(index == 0) && value.result_tag.is_some() {
                        continue;
                    } else if contains_fixed_array(
                        &arguments[index],
                        &self.types,
                        &mut BTreeSet::new(),
                    ) {
                        self.unsupported(
                            syntax.span,
                            "Result fixed array payload needs a tag-specific shape proof",
                        );
                    }
                }
            }
            _ => {}
        }
    }

    fn shape_children(&self, value: &Value, slot: Slot) -> Vec<Value> {
        value
            .origins
            .nodes
            .iter()
            .filter_map(|node| self.fields.get(&(*node, slot.clone())).cloned())
            .collect()
    }

    pub(super) fn invalidate_array_length(&mut self, value: &Value, span: Span) {
        self.check_window_stability(value, span);
        if value
            .origins
            .nodes
            .iter()
            .any(|node| self.fixed_arrays.contains(node))
        {
            self.error(
                "E0301",
                span,
                "array length-changing operations require dynamic []T storage; this path can reach fixed [N]T storage",
                [value.cause],
            );
        }
        for node in &value.origins.nodes {
            // A rejected operation cannot erase the fixed-storage witness and
            // allow a later alias to appear dynamically resizable.
            if !self.fixed_arrays.contains(node) {
                self.array_lengths.insert(*node, None);
            }
        }
    }
}

pub(crate) fn length_literal(
    expression: &Expr,
    pointer_bits: u8,
) -> Result<Option<u64>, &'static str> {
    match &expression.kind {
        ExprKind::Literal(Literal::Integer(text)) => {
            let text = text.replace('_', "");
            if [
                "bigint", "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64",
            ]
            .iter()
            .any(|suffix| text.ends_with(suffix))
            {
                return Err("E0323");
            }
            let raw = text.strip_suffix("int").unwrap_or(&text);
            if raw.chars().any(|character| character.is_ascii_alphabetic())
                && !raw.starts_with("0x")
                && !raw.starts_with("0X")
                && !raw.starts_with("0o")
                && !raw.starts_with("0O")
                && !raw.starts_with("0b")
                && !raw.starts_with("0B")
            {
                return Err("E0323");
            }
            let (radix, digits) = if let Some(raw) =
                raw.strip_prefix("0x").or_else(|| raw.strip_prefix("0X"))
            {
                (16, raw)
            } else if let Some(raw) = raw.strip_prefix("0o").or_else(|| raw.strip_prefix("0O")) {
                (8, raw)
            } else if let Some(raw) = raw.strip_prefix("0b").or_else(|| raw.strip_prefix("0B")) {
                (2, raw)
            } else {
                (10, raw)
            };
            let value = i128::from_str_radix(digits, radix).map_err(|_| "E0815")?;
            if value >= 1i128 << (pointer_bits - 1) {
                return Err("E0326");
            }
            u64::try_from(value).map(Some).map_err(|_| "E0815")
        }
        ExprKind::Unary { operator, operand } if operator == "-" => {
            match length_literal(operand, pointer_bits)? {
                Some(0) => Ok(Some(0)),
                Some(_) => Err("E0815"),
                None => Ok(None),
            }
        }
        ExprKind::Literal(_) => Err("E0323"),
        _ => Ok(None),
    }
}

fn contains_fixed_array(
    ty: &TypeExpr,
    types: &BTreeMap<String, TypeDeclaration>,
    seen: &mut BTreeSet<String>,
) -> bool {
    match &ty.kind {
        TypeKind::Array {
            length: Some(_), ..
        } => true,
        TypeKind::Array { element, .. } | TypeKind::Optional(element) => {
            contains_fixed_array(element, types, seen)
        }
        TypeKind::Name { path, arguments } => {
            arguments
                .iter()
                .any(|argument| contains_fixed_array(argument, types, &mut seen.clone()))
                || (seen.insert(path.join("::"))
                    && types
                        .get(&path.join("::"))
                        .and_then(|declaration| declaration.value.as_ref())
                        .is_some_and(|value| contains_fixed_array(value, types, seen)))
        }
        TypeKind::Tuple(items) => items
            .iter()
            .any(|item| contains_fixed_array(item, types, &mut seen.clone())),
        TypeKind::Record { fields, .. } => fields
            .iter()
            .any(|field| contains_fixed_array(&field.ty, types, &mut seen.clone())),
        TypeKind::Map { key, value } => {
            contains_fixed_array(key, types, &mut seen.clone())
                || contains_fixed_array(value, types, &mut seen.clone())
        }
        _ => false,
    }
}
