//! Complete, immutable source type identity; never an authority or shape proof.
use super::io_types as io;
use super::*;
use std::sync::Arc;

struct SourceSelection<'a> {
    binders: &'a BTreeSet<String>,
    schemas: &'a mut BTreeMap<String, Arc<SourceTypeWitness>>,
    span: Span,
    cause: CauseId,
}

impl Checker {
    pub(super) fn source_type_from_frozen_syntax(
        &mut self,
        syntax: &TypeExpr,
    ) -> Option<Arc<SourceTypeWitness>> {
        let key = crate::static_eval::normalized_argument_key(syntax);
        if let Some(witness) = self.source_type_intern.get(&key) {
            return Some(witness.clone());
        }
        self.intern_closed_source_syntax(syntax.clone())
    }

    pub(super) fn adapt_copy_source_type(
        &mut self,
        source: &Value,
        result: &mut Value,
        immutable: bool,
    ) {
        let Some(witness) = &source.source_type_witness else {
            result.source_type_witness = None;
            return;
        };
        match (&source.ty, immutable, &witness.syntax.kind) {
            (Ty::Immutable(_), false, TypeKind::Name { path, arguments })
                if path.join("::").trim_start_matches("Prelude::") == "Immut"
                    && arguments.len() == 1 =>
            {
                result.source_type_witness = self.source_type_from_frozen_syntax(&arguments[0])
            }
            (Ty::Immutable(_), true, _) | (_, false, _) => {
                result.source_type_witness = Some(witness.clone())
            }
            (_, true, _) => {
                result.source_type_witness = self.intern_closed_source_syntax(TypeExpr {
                    text: String::new(),
                    span: witness.syntax.span,
                    kind: TypeKind::Name {
                        path: vec!["Immut".into()],
                        arguments: vec![witness.syntax.clone()],
                    },
                })
            }
        }
    }

    pub(super) fn project_optional_source_type(&mut self, source: &Value, result: &mut Value) {
        let Some(witness) = &source.source_type_witness else {
            return;
        };
        let inner = match &witness.syntax.kind {
            TypeKind::Optional(inner) => Some(&**inner),
            TypeKind::Name { path, arguments }
                if path.join("::").trim_start_matches("Prelude::") == "Option"
                    && arguments.len() == 1 =>
            {
                Some(&arguments[0])
            }
            _ => None,
        };
        if let Some(inner) = inner {
            result.source_type_witness = self.source_type_from_frozen_syntax(inner);
        }
    }

    pub(super) fn project_result_source_type(
        &mut self,
        source: &Value,
        success: bool,
        result: &mut Value,
    ) {
        let Some(witness) = &source.source_type_witness else {
            return;
        };
        if let TypeKind::Name { path, arguments } = &witness.syntax.kind
            && path.join("::").trim_start_matches("Prelude::") == "Result"
            && arguments.len() == 2
        {
            result.source_type_witness =
                self.source_type_from_frozen_syntax(&arguments[usize::from(!success)]);
        }
    }
    pub(super) fn register_constructor_source_type(&mut self, name: &str, syntax: &TypeExpr) {
        // Preserve the genuine declaration/normalized-instance syntax even
        // when its Const or symbolic arguments are not a closed type witness.
        if crate::static_eval::effects::bounded_argument_key(syntax, &self.effect_type_binders)
            .is_some()
        {
            self.constructor_source_syntax
                .insert(name.into(), Arc::new(syntax.clone()));
        } else {
            self.constructor_source_syntax.remove(name);
        }
        if let Some(witness) = self.source_type_from_syntax(syntax) {
            self.constructor_source_types.insert(name.into(), witness);
        } else {
            self.constructor_source_types.remove(name);
        }
    }

    fn source_root_agrees(&self, value: &Value, witness: &SourceTypeWitness) -> bool {
        let actual = self.source_value_inference_type(value);
        let name = |path: &[String]| path.join("::").trim_start_matches("Prelude::").to_owned();
        match (&actual, &witness.syntax.kind) {
            (Ty::Unit, TypeKind::Tuple(items)) => items.is_empty(),
            (Ty::Array(_), TypeKind::Array { .. })
            | (Ty::Map(..), TypeKind::Map { .. })
            | (Ty::Tuple(_), TypeKind::Tuple(_))
            | (Ty::Record(_), TypeKind::Record { .. })
            | (Ty::Callable(..), TypeKind::Callable { .. })
            | (Ty::Optional(_), TypeKind::Optional(_)) => true,
            (Ty::Optional(_), TypeKind::Name { path, arguments }) => {
                name(path) == "Option" && arguments.len() == 1
            }
            (Ty::Result(..), TypeKind::Name { path, arguments }) => {
                name(path) == "Result" && arguments.len() == 2
            }
            (Ty::Immutable(_), TypeKind::Name { path, arguments }) => {
                name(path) == "Immut" && arguments.len() == 1
            }
            (Ty::Set(_), TypeKind::Name { path, arguments }) => {
                name(path) == "Set" && arguments.len() == 1
            }
            (Ty::Range(_), TypeKind::Name { path, arguments }) => {
                name(path) == "Range" && arguments.len() == 1
            }
            (
                Ty::Int(expected) | Ty::Float(expected) | Ty::Named(expected),
                TypeKind::Name { path, arguments },
            ) => name(path) == *expected && arguments.is_empty(),
            (Ty::Bool, TypeKind::Name { path, arguments }) => {
                name(path) == "bool" && arguments.is_empty()
            }
            (Ty::Str, TypeKind::Name { path, arguments }) => {
                name(path) == "str" && arguments.is_empty()
            }
            (Ty::Bytes, TypeKind::Name { path, arguments }) => {
                name(path) == "bytes" && arguments.is_empty()
            }
            (Ty::Never, TypeKind::Name { path, arguments }) => {
                name(path) == "never" && arguments.is_empty()
            }
            (
                Ty::Applied {
                    constructor,
                    arguments: expected,
                },
                TypeKind::Name { path, arguments },
            ) => name(path) == *constructor && arguments.len() == expected.len(),
            _ => false,
        }
    }

    fn source_carrier_syntax(&self, value: &Value, span: Span) -> Option<TypeExpr> {
        let payload = |actual: Option<&Value>, ty: &Ty| {
            actual
                .and_then(|value| value.source_type_witness.as_ref())
                .filter(|witness| {
                    actual.is_some_and(|value| self.source_root_agrees(value, witness))
                })
                .map(|witness| witness.syntax.clone())
                .or_else(|| erased_complete_syntax(ty, span))
        };
        let kind = match &self.source_value_inference_type(value) {
            Ty::Optional(inner) => {
                TypeKind::Optional(Box::new(payload(value.option_payload.as_deref(), inner)?))
            }
            Ty::Result(ok, error) => TypeKind::Name {
                path: vec!["Result".into()],
                arguments: vec![
                    payload(
                        value.result_success.as_deref().or_else(|| {
                            (value.result_tag == Some(true))
                                .then_some(value.result_payload.as_deref())
                                .flatten()
                        }),
                        ok,
                    )?,
                    payload(
                        value.result_error.as_deref().or_else(|| {
                            (value.result_tag == Some(false))
                                .then_some(value.result_payload.as_deref())
                                .flatten()
                        }),
                        error,
                    )?,
                ],
            },
            _ => return None,
        };
        Some(TypeExpr {
            text: String::new(),
            kind,
            span,
        })
    }

    pub(super) fn complete_carrier_source_type(&mut self, value: &mut Value, span: Span) {
        if value
            .source_type_witness
            .as_ref()
            .is_some_and(|witness| !self.source_root_agrees(value, witness))
        {
            value.source_type_witness = None;
        }
        if value.source_type_witness.is_none()
            && let Some(syntax) = self.source_carrier_syntax(value, span)
        {
            value.source_type_witness = self.intern_closed_source_syntax(syntax);
        }
    }
    pub(super) fn instantiated_source_syntax(&self, syntax: &TypeExpr) -> Option<TypeExpr> {
        fn substitute(
            checker: &Checker,
            syntax: &TypeExpr,
            depth: usize,
            work: &mut usize,
        ) -> Option<TypeExpr> {
            *work += 1;
            if depth >= 64 || *work > 4096 {
                return None;
            }
            if let Some(value) = checker.source_typeof_value(syntax) {
                return value
                    .source_type_witness
                    .as_ref()
                    .map(|witness| witness.syntax.clone());
            }
            if let TypeKind::Name { path, arguments } = &syntax.kind
                && arguments.is_empty()
                && let Some(identity) = checker.generic_context.get(&path.join("::"))
            {
                return checker
                    .generic_type_witnesses
                    .get(identity)
                    .map(|witness| witness.syntax.clone());
            }
            let mut output = syntax.clone();
            output.text.clear();
            let mut child = |syntax: &TypeExpr| substitute(checker, syntax, depth + 1, work);
            match &mut output.kind {
                TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
                    for argument in arguments {
                        *argument = child(argument)?;
                    }
                }
                TypeKind::Optional(inner) | TypeKind::Rest(inner) | TypeKind::KeyOf(inner) => {
                    **inner = child(inner)?
                }
                TypeKind::Array { element, .. } => **element = child(element)?,
                TypeKind::Map { key, value } => {
                    **key = child(key)?;
                    **value = child(value)?;
                }
                TypeKind::Record { fields, row } => {
                    for field in fields {
                        field.ty = child(&field.ty)?;
                    }
                    if let Some(row) = row {
                        **row = child(row)?;
                    }
                }
                TypeKind::Callable {
                    parameters, result, ..
                } => {
                    for parameter in parameters {
                        let ty = parameter.ty.as_ref()?;
                        parameter.ty = Some(child(ty)?);
                        if parameter.default.is_some() {
                            return None;
                        }
                    }
                    if let Some(result) = result {
                        **result = child(result)?;
                    }
                }
                _ => {}
            }
            Some(output)
        }
        substitute(self, syntax, 0, &mut 0)
    }

    pub(super) fn source_typeof_value(&self, syntax: &TypeExpr) -> Option<&Value> {
        let TypeKind::Computation(expression) = &syntax.kind else {
            return None;
        };
        let ExprKind::Unary { operator, operand } = &expression.kind else {
            return None;
        };
        if operator != "typeof" {
            return None;
        }
        let name = match &operand.kind {
            ExprKind::Name(name) => name.clone(),
            ExprKind::Path(path) => path.join("::"),
            _ => return None,
        };
        self.contract_environment
            .get(&name)
            .and_then(|binding| self.bindings.get(*binding))
            .map(|binding| &binding.value)
    }

    pub(super) fn source_type_from_syntax(
        &mut self,
        syntax: &TypeExpr,
    ) -> Option<Arc<SourceTypeWitness>> {
        let syntax = self.closed_source_syntax(syntax)?;
        self.intern_closed_source_syntax(syntax)
    }

    fn intern_closed_source_syntax(&mut self, syntax: TypeExpr) -> Option<Arc<SourceTypeWitness>> {
        let key = crate::static_eval::normalized_argument_key(&syntax);
        if let Some(existing) = self.source_type_intern.get(&key) {
            return Some(existing.clone());
        }
        let witness = SourceTypeWitness { key, syntax };
        if !witness.validate_closed()
            || !super::super::source_type_validation::resolved_names(&witness, &self.types)
        {
            return None;
        }
        // Values and retained environments share these immutable descriptors.
        // Exhausting this metadata budget leaves the existing type obligation
        // unresolved; it never falls back to a weaker array/callable identity.
        // Charge a conservative AST-node/string overhead as well as the two
        // key copies. This is a work boundary, not an exact allocator census.
        let retained_cost = witness.key.len().saturating_mul(256);
        if self.source_type_intern.len() >= 4096
            || self.source_type_bytes.saturating_add(retained_cost) > 16 * 1024 * 1024
        {
            return None;
        }
        self.source_type_bytes += retained_cost;
        let witness = Arc::new(witness);
        self.source_type_intern
            .insert(witness.key.clone(), witness.clone());
        Some(witness)
    }

    pub(super) fn closed_source_syntax(&self, syntax: &TypeExpr) -> Option<TypeExpr> {
        let syntax = self.instantiated_source_syntax(syntax)?;
        normalize_closed_source_syntax(&syntax, &self.types, self.layout)
    }
    pub(super) fn ascribe_source_type(&mut self, value: &mut Value, syntax: &TypeExpr) {
        // Identity metadata does not establish the independent storage checks.
        value.source_type_witness = self.source_type_from_syntax(syntax);
    }

    pub(super) fn source_value_inference_type(&self, value: &Value) -> Ty {
        let ty = self.collection_type(value);
        if matches!(value.ty, Ty::Immutable(_)) {
            Ty::Immutable(Box::new(ty))
        } else {
            ty
        }
    }

    /// Select complete schemas from the same actual arguments that selected
    /// each semantic binder. No graph cardinality participates in this step.
    pub(super) fn select_generic_source_types(
        &mut self,
        templates: &[Option<Ty>],
        args: &[(ParameterMode, Value, Span)],
        binders: &BTreeSet<String>,
        selected: &BTreeMap<String, Ty>,
    ) {
        let mut schemas = BTreeMap::new();
        for ((_, value, span), template) in args.iter().zip(templates) {
            let Some(template) = template else { continue };
            let mut mentioned = BTreeSet::new();
            template.generic_names(&mut mentioned);
            if mentioned.is_disjoint(binders) {
                continue;
            }
            let syntax = if value.unsuffixed_numeric {
                match template {
                    Ty::Generic(identity) => selected
                        .get(identity)
                        .and_then(|ty| erased_complete_syntax(ty, *span)),
                    _ => None,
                }
            } else {
                value
                    .source_type_witness
                    .as_ref()
                    .filter(|witness| self.source_root_agrees(value, witness))
                    .map(|witness| witness.syntax.clone())
                    .or_else(|| self.source_carrier_syntax(value, *span))
            };
            if let Some(syntax) = syntax {
                self.select_source_schema(
                    template,
                    &syntax,
                    &mut SourceSelection {
                        binders,
                        schemas: &mut schemas,
                        span: *span,
                        cause: value.cause,
                    },
                    0,
                );
            }
        }
        for (identity, ty) in selected {
            if !schemas.contains_key(identity)
                && let Some(witness) = self.closed_product_bound_identity(identity, templates)
            {
                schemas.insert(identity.clone(), witness);
            }
            if !schemas.contains_key(identity)
                && let Some(syntax) = erased_complete_syntax(
                    ty,
                    self.functions.last().map_or(
                        Span {
                            file: self.file,
                            start: 0,
                            end: 0,
                        },
                        |info| info.syntax.span,
                    ),
                )
                && let Some(witness) = self.intern_closed_source_syntax(syntax)
            {
                schemas.insert(identity.clone(), witness);
            }
            if !schemas.contains_key(identity)
                && requires_source_identity(ty)
                && !self.admit_scoped_source_identity(identity, templates)
            {
                let span = args.first().map_or(
                    Span {
                        file: self.file,
                        start: 0,
                        end: 0,
                    },
                    |(_, _, span)| *span,
                );
                self.unsupported(span, "a generic binder requires the complete source array dimensions and callable qualifications of its actual argument");
            }
        }
        self.generic_type_witnesses.extend(schemas);
    }

    fn select_source_schema(
        &mut self,
        template: &Ty,
        actual: &TypeExpr,
        selection: &mut SourceSelection<'_>,
        depth: usize,
    ) {
        if depth >= 64 {
            return;
        }
        if let Ty::Generic(identity) = template
            && selection.binders.contains(identity)
        {
            // `actual` descends from a previously frozen value schema. Its
            // nominal names must not be reinterpreted by this callee's T.
            if let Some(witness) = self.source_type_from_frozen_syntax(actual) {
                if selection
                    .schemas
                    .get(identity)
                    .is_some_and(|old| old.key != witness.key)
                {
                    self.error("E0301", selection.span, "arguments require inconsistent complete source types for a generic parameter", [selection.cause]);
                } else {
                    selection.schemas.insert(identity.clone(), witness);
                }
            }
            return;
        }
        let mut children: Vec<(&Ty, &TypeExpr)> = vec![];
        match (template, &actual.kind) {
            (Ty::Array(inner), TypeKind::Array { element, .. })
            | (Ty::Optional(inner), TypeKind::Optional(element)) => children.push((inner, element)),
            (Ty::Map(a, b), TypeKind::Map { key, value }) => {
                children.extend([(&**a, &**key), (&**b, &**value)])
            }
            (Ty::Tuple(types), TypeKind::Tuple(items)) => children.extend(types.iter().zip(items)),
            (
                Ty::Record(types) | Ty::OpenRecord { fields: types, .. },
                TypeKind::Record { fields, .. },
            ) => {
                for field in fields {
                    if let Some((_, ty)) = types.get(&field.name) {
                        children.push((ty, &field.ty));
                    }
                }
            }
            (
                Ty::Callable(types, result),
                TypeKind::Callable {
                    parameters,
                    result: actual_result,
                    ..
                },
            ) => {
                children.extend(
                    types.iter().zip(
                        parameters
                            .iter()
                            .filter_map(|parameter| parameter.ty.as_ref()),
                    ),
                );
                if let Some(actual_result) = actual_result {
                    children.push((result, actual_result));
                }
            }
            (
                Ty::Immutable(inner) | Ty::Optional(inner) | Ty::Set(inner) | Ty::Range(inner),
                TypeKind::Name { arguments, .. },
            ) if arguments.len() == 1 => children.push((inner, &arguments[0])),
            (Ty::Result(a, b), TypeKind::Name { arguments, .. }) if arguments.len() == 2 => {
                children.extend([(&**a, &arguments[0]), (&**b, &arguments[1])])
            }
            (
                Ty::Applied {
                    arguments: types, ..
                },
                TypeKind::Name { arguments, .. },
            ) => {
                for (ty, syntax) in types.iter().zip(arguments) {
                    if let TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. } = ty {
                        children.push((ty, syntax));
                    }
                }
            }
            _ => {}
        }
        for (template, actual) in children {
            self.select_source_schema(template, actual, selection, depth + 1);
        }
    }

    pub(super) fn project_source_type(&mut self, base: &Value, slot: &Slot, result: &mut Value) {
        let Some(witness) = &base.source_type_witness else {
            return;
        };
        let mut syntax = &witness.syntax;
        while let TypeKind::Name { path, arguments } = &syntax.kind {
            if path.join("::").trim_start_matches("Prelude::") == "Immut" && arguments.len() == 1 {
                syntax = &arguments[0];
            } else {
                break;
            }
        }
        let child = match (&syntax.kind, slot) {
            (TypeKind::Array { element, .. }, Slot::Index(_) | Slot::AnyIndex) => Some(&**element),
            (TypeKind::Tuple(items), Slot::Tuple(index)) => items.get(*index as usize),
            (TypeKind::Record { fields, .. }, Slot::Field(name)) => fields
                .iter()
                .find(|field| &field.name == name)
                .map(|field| &field.ty),
            (TypeKind::Map { key, .. }, Slot::Field(name)) if name == "key" => Some(&**key),
            (TypeKind::Map { value, .. }, Slot::Index(_) | Slot::AnyIndex) => Some(&**value),
            _ => None,
        };
        if let Some(child) = child {
            result.source_type_witness = self.source_type_from_frozen_syntax(child);
        }
    }

    pub(super) fn infer_expression_source_type(&mut self, value: &mut Value, expression: &Expr) {
        self.complete_carrier_source_type(value, expression.span);
        if value.source_type_witness.is_some() || value.ty == Ty::Never {
            return;
        }
        let mut named_environment = None;
        let syntax = match &expression.kind {
            ExprKind::Lambda {
                parameters,
                return_type,
                annotations,
                ..
            } => return_type.as_ref().map(|result| TypeExpr {
                text: String::new(),
                span: expression.span,
                kind: TypeKind::Callable {
                    parameters: parameters.clone(),
                    result: Some(Box::new(result.clone())),
                    annotations: annotations.clone(),
                },
            }),
            ExprKind::Array(_) => {
                let Ty::Array(element) = self.collection_type(value) else {
                    return;
                };
                let child = self
                    .source_element_syntax(value)
                    .or_else(|| erased_complete_syntax(&element, expression.span));
                child.map(|element| TypeExpr {
                    text: String::new(),
                    span: expression.span,
                    kind: TypeKind::Array {
                        length: None,
                        element: Box::new(element),
                    },
                })
            }
            ExprKind::Tuple(_) | ExprKind::Record { .. } => {
                self.source_composite_syntax(value, expression.span)
            }
            _ if value.callables.len() == 1 => match &value.callables[0] {
                Callable::Named(id) if self.functions[*id].syntax.generics.is_empty() => {
                    named_environment = Some(self.functions[*id].clone());
                    let function = &self.functions[*id].syntax;
                    let mut parameters = function.parameters.clone();
                    // Defaults belong to this callable's invocation descriptor,
                    // not to its type identity. The actual Value keeps them.
                    for parameter in &mut parameters {
                        parameter.default = None;
                    }
                    Some(TypeExpr {
                        text: String::new(),
                        span: expression.span,
                        kind: TypeKind::Callable {
                            parameters,
                            result: Some(Box::new(function.return_type.clone().unwrap_or(
                                TypeExpr {
                                    text: "()".into(),
                                    kind: TypeKind::Tuple(vec![]),
                                    span: expression.span,
                                },
                            ))),
                            annotations: function.annotations.clone(),
                        },
                    })
                }
                _ => None,
            },
            _ => erased_complete_syntax(&self.collection_type(value), expression.span),
        };
        if let Some(syntax) = syntax {
            value.source_type_witness = if let Some(function) = named_environment {
                self.named_header_source_type(&function, &syntax)
            } else {
                self.source_type_from_syntax(&syntax)
            };
        }
    }

    fn named_header_source_type(
        &mut self,
        function: &FunctionInfo,
        syntax: &TypeExpr,
    ) -> Option<Arc<SourceTypeWitness>> {
        self.source_type_in_environment(syntax, &function.typing_environment)
    }

    /// Source queries state which declaration interprets their Type and Key
    /// names. The ambient caller is restored even when normalization fails.
    pub(super) fn source_type_in_environment(
        &mut self,
        syntax: &TypeExpr,
        environment: &crate::sema::context::FrozenEnvironment,
    ) -> Option<Arc<SourceTypeWitness>> {
        self.with_typing_environment(environment, |checker| {
            checker.source_type_from_syntax(syntax)
        })
    }

    fn source_element_syntax(&self, value: &Value) -> Option<TypeExpr> {
        let children = value.origins.nodes.iter().flat_map(|node| {
            self.fields
                .iter()
                .filter_map(move |((parent, slot), child)| {
                    (*parent == *node && matches!(slot, Slot::Index(_) | Slot::AnyIndex))
                        .then_some(child)
                })
        });
        let mut common: Option<&Arc<SourceTypeWitness>> = None;
        let mut work = 4096usize;
        for child in children {
            let witness = child.source_type_witness.as_ref()?;
            work = work.checked_sub(1 + witness.key.len().div_ceil(32))?;
            if !witness.validate_closed() || !self.source_root_agrees(child, witness) {
                return None;
            }
            if common.is_some_and(|old| old.key != witness.key) {
                return None;
            }
            common = Some(witness);
        }
        common.map(|witness| witness.syntax.clone())
    }

    /// Mint the declared dynamic shell of a standard array producer. Element
    /// coordinates come from its actual stored constituents, or from a data
    /// type whose representation loses no source identity. A Ty::Array, Fn,
    /// open row or generic element cannot supply missing inner coordinates.
    pub(super) fn complete_standard_array_source(&mut self, value: &mut Value, span: Span) {
        let Ty::Array(element) = &value.ty else {
            return;
        };
        let Some(element) = self
            .source_element_syntax(value)
            .or_else(|| erased_complete_syntax(element, span))
        else {
            return;
        };
        value.source_type_witness = self.source_type_from_frozen_syntax(&TypeExpr {
            text: String::new(),
            span,
            kind: TypeKind::Array {
                length: None,
                element: Box::new(element),
            },
        });
    }

    pub(super) fn source_composite_syntax(&self, value: &Value, span: Span) -> Option<TypeExpr> {
        let child = |slot: Slot, ty: &Ty| {
            let mut common: Option<Arc<SourceTypeWitness>> = None;
            for node in &value.origins.nodes {
                let value = self.fields.get(&(*node, slot.clone()))?;
                let witness = value.source_type_witness.clone()?;
                if common.as_ref().is_some_and(|old| old.key != witness.key) {
                    return None;
                }
                common = Some(witness);
            }
            common
                .map(|witness| witness.syntax.clone())
                .or_else(|| erased_complete_syntax(ty, span))
        };
        let kind = match self.collection_type(value) {
            Ty::Tuple(items) => TypeKind::Tuple(
                items
                    .iter()
                    .enumerate()
                    .map(|(index, ty)| child(Slot::Tuple(index as u32), ty))
                    .collect::<Option<_>>()?,
            ),
            Ty::Record(fields) => TypeKind::Record {
                fields: fields
                    .iter()
                    .map(|(name, (mutable, ty))| {
                        Some(TypeField {
                            name: name.clone(),
                            mutable: *mutable,
                            ty: child(Slot::Field(name.clone()), ty)?,
                            span,
                        })
                    })
                    .collect::<Option<_>>()?,
                row: None,
            },
            _ => return None,
        };
        Some(TypeExpr {
            text: String::new(),
            kind,
            span,
        })
    }
}

fn erased_complete_syntax(ty: &Ty, span: Span) -> Option<TypeExpr> {
    if contains_erased_identity(ty) {
        return None;
    }
    super::io_types::data_type(ty, span)
}

fn contains_erased_identity(ty: &Ty) -> bool {
    match ty {
        Ty::Array(_)
        | Ty::Callable(..)
        | Ty::Applied { .. }
        | Ty::OpenRecord { .. }
        | Ty::Unknown
        | Ty::Generic(_)
        | Ty::NumericHole(_)
        | Ty::Projection { .. }
        | Ty::StaticKey(_) => true,
        Ty::Immutable(inner) | Ty::Optional(inner) | Ty::Set(inner) | Ty::Range(inner) => {
            contains_erased_identity(inner)
        }
        Ty::Map(a, b) | Ty::Result(a, b) => {
            contains_erased_identity(a) || contains_erased_identity(b)
        }
        Ty::Tuple(items) => items.iter().any(contains_erased_identity),
        Ty::Record(fields) => fields.values().any(|(_, ty)| contains_erased_identity(ty)),
        _ => false,
    }
}

fn requires_source_identity(ty: &Ty) -> bool {
    match ty {
        Ty::Array(_) | Ty::Callable(..) => true,
        Ty::Immutable(inner) | Ty::Optional(inner) | Ty::Set(inner) | Ty::Range(inner) => {
            requires_source_identity(inner)
        }
        Ty::Result(a, b) | Ty::Map(a, b) => {
            requires_source_identity(a) || requires_source_identity(b)
        }
        Ty::Tuple(items) => items.iter().any(requires_source_identity),
        Ty::Record(fields) | Ty::OpenRecord { fields, .. } => {
            fields.values().any(|(_, ty)| requires_source_identity(ty))
        }
        Ty::Applied { arguments, .. } => arguments.iter().any(|argument| match argument {
            TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. } => {
                requires_source_identity(ty)
            }
            _ => false,
        }),
        _ => false,
    }
}

pub(super) fn expand_builtin_source_syntax(
    declarations: &BTreeMap<String, TypeDeclaration>,
    syntax: &TypeExpr,
    depth: usize,
) -> Option<TypeExpr> {
    fn normalize(
        declarations: &BTreeMap<String, TypeDeclaration>,
        syntax: &TypeExpr,
        depth: usize,
        visits: &mut usize,
    ) -> Option<TypeExpr> {
        *visits += 1;
        if depth >= 128 || *visits > 4096 {
            return None;
        }
        if let TypeKind::Name { path, arguments } = &syntax.kind
            && !declarations.contains_key(&path.join("::"))
        {
            let schema = io::operation_type(syntax)
                .or_else(|| super::iter_types::schema(syntax))
                .or_else(|| {
                    if !arguments.is_empty() {
                        return None;
                    }
                    let ty = standard::file_type(&path.join("::"))?;
                    matches!(ty, Ty::Record(_))
                        .then(|| io::data_type(&ty, syntax.span))
                        .flatten()
                });
            if let Some(schema) = schema {
                crate::static_eval::effects::bounded_argument_key(&schema, &BTreeMap::new())?;
                return normalize(declarations, &schema, depth + 1, visits);
            }
        }
        let mut child = |ty: &TypeExpr| normalize(declarations, ty, depth + 1, visits);
        let kind = match &syntax.kind {
            TypeKind::Name { path, arguments } => TypeKind::Name {
                path: path.clone(),
                arguments: arguments.iter().map(&mut child).collect::<Option<_>>()?,
            },
            TypeKind::Tuple(items) => {
                TypeKind::Tuple(items.iter().map(&mut child).collect::<Option<_>>()?)
            }
            TypeKind::Optional(inner) => TypeKind::Optional(Box::new(child(inner)?)),
            TypeKind::Rest(inner) => TypeKind::Rest(Box::new(child(inner)?)),
            TypeKind::KeyOf(inner) => TypeKind::KeyOf(Box::new(child(inner)?)),
            TypeKind::Array { length, element } => TypeKind::Array {
                length: length.clone(),
                element: Box::new(child(element)?),
            },
            TypeKind::Map { key, value } => TypeKind::Map {
                key: Box::new(child(key)?),
                value: Box::new(child(value)?),
            },
            TypeKind::Record { fields, row } => TypeKind::Record {
                fields: fields
                    .iter()
                    .map(|field| {
                        Some(TypeField {
                            name: field.name.clone(),
                            mutable: field.mutable,
                            ty: child(&field.ty)?,
                            span: field.span,
                        })
                    })
                    .collect::<Option<_>>()?,
                row: match row {
                    Some(row) => Some(Box::new(child(row)?)),
                    None => None,
                },
            },
            TypeKind::Callable {
                parameters,
                result,
                annotations,
            } => TypeKind::Callable {
                parameters: parameters
                    .iter()
                    .map(|parameter| {
                        Some(Parameter {
                            pattern: parameter.pattern.clone(),
                            mode: parameter.mode,
                            ty: match &parameter.ty {
                                Some(ty) => Some(child(ty)?),
                                None => None,
                            },
                            default: parameter.default.clone(),
                            span: parameter.span,
                        })
                    })
                    .collect::<Option<_>>()?,
                result: match result {
                    Some(result) => Some(Box::new(child(result)?)),
                    None => None,
                },
                annotations: annotations.clone(),
            },
            other => other.clone(),
        };
        Some(TypeExpr {
            text: String::new(),
            kind,
            span: syntax.span,
        })
    }
    crate::static_eval::effects::bounded_argument_key(syntax, &BTreeMap::new())?;
    normalize(declarations, syntax, depth, &mut 0)
}

pub(crate) fn normalize_closed_source_syntax(
    syntax: &TypeExpr,
    declarations: &BTreeMap<String, TypeDeclaration>,
    layout: ril_compiler_core::target::TargetLayout,
) -> Option<TypeExpr> {
    // Expand transparent builtin records before deciding that every name
    // is resolved. Otherwise Explicit and Alias take different paths and
    // retain different halves of the same Reader/Io schema.
    let syntax = expand_builtin_source_syntax(declarations, syntax, 0)?;
    let candidate = SourceTypeWitness {
        key: crate::static_eval::normalized_argument_key(&syntax),
        syntax,
    };
    if !candidate.validate_closed() {
        return None;
    }
    if super::super::source_type_validation::resolved_names(&candidate, declarations) {
        return Some(candidate.syntax);
    }
    let syntax = candidate.syntax;
    let container = TypeDeclaration {
        visibility: Visibility::Private,
        is_halt: false,
        name: "\0ril.source.type".into(),
        generics: vec![],
        value: Some(syntax.clone()),
        variants: vec![],
        opaque: false,
        nominal: true,
        span: syntax.span,
    };
    let normalized =
        crate::static_eval::normalize_constructor_arguments(&container, &[], declarations, layout)
            .ok()?;
    let syntax = expand_builtin_source_syntax(
        declarations,
        normalized.payloads.get(&container.name)?.as_ref()?,
        0,
    )?;
    let witness = SourceTypeWitness {
        key: crate::static_eval::normalized_argument_key(&syntax),
        syntax,
    };
    if !witness.validate_closed() {
        return None;
    }
    if !super::super::source_type_validation::resolved_names(&witness, declarations) {
        return None;
    }
    Some(witness.syntax)
}
