//! Data-constructor identities are distinct from function declarations and tags.
//! Wrapping a payload preserves its complete graph, permissions and duties.
use super::*;
#[path = "generic_constructors.rs"]
mod generic;

impl Checker {
    pub(super) fn constructor_scalar_type(&self, ty: &Ty) -> Option<bool> {
        if matches!(ty, Ty::Optional(_) | Ty::Result(..) | Ty::Immutable(_)) {
            return Some(self.constructor_representation_scalar(ty, &mut BTreeSet::new()));
        }
        if !matches!(ty, Ty::Named(_) | Ty::Applied { .. }) {
            return None;
        }
        if !self
            .constructors
            .values()
            .any(|constructor| constructor.owner == *ty)
        {
            return None;
        }
        Some(self.constructor_representation_scalar(ty, &mut BTreeSet::new()))
    }
    fn constructor_representation_scalar(&self, ty: &Ty, seen: &mut BTreeSet<String>) -> bool {
        match ty {
            Ty::Named(_) | Ty::Applied { .. } => {
                if !seen.insert(format!("{ty:?}")) {
                    return false;
                }
                let payloads: Vec<_> = self
                    .constructors
                    .values()
                    .filter(|constructor| constructor.owner == *ty)
                    .map(|constructor| &constructor.payload)
                    .collect();
                if payloads.is_empty() {
                    let expanded = self.expanded(ty, &mut BTreeSet::new());
                    return expanded != *ty
                        && self.constructor_representation_scalar(&expanded, seen);
                }
                payloads.iter().all(|payload| {
                    self.constructor_representation_scalar(payload, &mut seen.clone())
                })
            }
            Ty::Optional(inner) | Ty::Immutable(inner) => {
                self.constructor_representation_scalar(inner, seen)
            }
            Ty::Result(ok, error) => {
                self.constructor_representation_scalar(ok, &mut seen.clone())
                    && self.constructor_representation_scalar(error, &mut seen.clone())
            }
            _ => ty.scalar(),
        }
    }
    pub(super) fn declare_constructors(&mut self, declaration: &TypeDeclaration) {
        if !declaration.nominal && declaration.variants.is_empty() {
            return;
        }
        // Reuse the type-parameter default validator before permitting a
        // constructor family whose ordinary type defaults are instantiated.
        if self.generic_constructor_contract(declaration)
            && declaration.generics.iter().all(|parameter| {
                parameter
                    .name
                    .chars()
                    .next()
                    .is_some_and(char::is_uppercase)
            })
        {
            let mut defaults = declaration.clone();
            defaults.nominal = false;
            defaults.opaque = false;
            defaults.variants.clear();
            defaults.value = Some(TypeExpr {
                hir_id: None,
                kind: TypeKind::Tuple(vec![]),
                text: "()".into(),
                span: declaration.span,
            });
            let _ = self.structural_alias_contract(&defaults);
        }
        for variant in &declaration.variants {
            let valid_result = match &variant.result {
                Some(TypeExpr {
                    kind: TypeKind::Name { path, arguments },
                    ..
                }) => {
                    path.join("::") == declaration.name
                        && arguments.len() == declaration.generics.len()
                }
                None => variant.generics.is_empty(),
                _ => false,
            };
            if !valid_result {
                self.error("E0354", variant.span, "variant result must identify its owning sum and expose variant-local parameters", []);
            }
            if !variant.generics.is_empty()
                && variant.result.as_ref().is_none_or(|result| {
                    variant.generics.iter().any(|parameter| {
                        !self.constructor_parameter_recoverable(result, &parameter.name)
                    })
                })
            {
                self.error(
                    "E0354",
                    variant.span,
                    "variant-local existential is not recoverable from its result",
                    [],
                );
            }
        }
        if !self.generic_constructor_contract(declaration) {
            self.unsupported(
                declaration.span,
                "generic nominal/sum instantiation identity and result equations",
            );
            return;
        }
        for parameter in &declaration.generics {
            if parameter
                .name
                .chars()
                .next()
                .is_some_and(char::is_lowercase)
                && let Some(bound) = &parameter.bound
            {
                // An unused const family still obeys ordinary data-sort
                // validity, including map-key eligibility.
                let _ = self.ty(bound);
            }
        }
        if declaration.nominal {
            let payload = declaration
                .value
                .as_ref()
                .map(|value| self.ty(value))
                .unwrap_or(Ty::Unit);
            self.constructors.insert(
                declaration.name.clone(),
                ConstructorInfo {
                    tag: declaration.name.clone(),
                    owner: self.constructor_template_owner(declaration),
                    payload,
                    nominal: true,
                    has_payload: declaration.value.is_some(),
                    payload_syntax: declaration.value.clone(),
                    span: declaration.span,
                },
            );
        } else if !declaration.opaque {
            for variant in &declaration.variants {
                let previous = self.type_source.environment.generic_context.clone();
                for (index, parameter) in variant.generics.iter().enumerate() {
                    self.type_source.environment.generic_context.insert(
                        parameter.name.clone(),
                        format!(
                            "{}:{}:variant:{index}:{}",
                            variant.span.file.0, variant.span.start, parameter.name
                        ),
                    );
                }
                let payload = variant
                    .payload
                    .as_ref()
                    .map(|value| self.ty(value))
                    .unwrap_or(Ty::Unit);
                let owner = variant
                    .result
                    .as_ref()
                    .map(|result| self.ty(result))
                    .unwrap_or_else(|| self.constructor_template_owner(declaration));
                self.type_source.environment.generic_context = previous;
                self.constructors.insert(
                    format!("{}::{}", declaration.name, variant.name),
                    ConstructorInfo {
                        tag: format!("{}::{}", declaration.name, variant.name),
                        owner,
                        payload,
                        nominal: false,
                        has_payload: variant.payload.is_some(),
                        payload_syntax: variant.payload.clone(),
                        span: variant.span,
                    },
                );
            }
        }
        let owners: Vec<_> = self
            .constructors
            .iter()
            .filter(|(name, constructor)| {
                *name == &constructor.tag
                    && constructor.span.file == declaration.span.file
                    && (constructor.tag == declaration.name
                        || constructor
                            .tag
                            .starts_with(&format!("{}::", declaration.name)))
            })
            .map(|(name, _)| {
                (
                    name.clone(),
                    declaration
                        .variants
                        .iter()
                        .find(|variant| format!("{}::{}", declaration.name, variant.name) == *name)
                        .and_then(|variant| variant.result.clone())
                        .unwrap_or_else(|| TypeExpr {
                            hir_id: None,
                            text: String::new(),
                            span: declaration.span,
                            kind: TypeKind::Name {
                                path: declaration.name.split("::").map(str::to_owned).collect(),
                                arguments: vec![],
                            },
                        }),
                )
            })
            .collect();
        for (name, syntax) in owners {
            if declaration.generics.is_empty()
                || matches!(&syntax.kind,TypeKind::Name {arguments,..} if !arguments.is_empty())
            {
                self.register_constructor_source_type(&name, &syntax);
            }
        }
    }
    pub(super) fn constructor_name(
        &mut self,
        name: &str,
        span: Span,
        _frame: &mut Frame,
    ) -> Option<Value> {
        let constructor = self.constructors.get(name)?.clone();
        if self.declaration_files.contains(&constructor.span.file.0) && constructor.nominal {
            self.error(
                "E0907",
                span,
                "foreign opaque nominal values cannot be directly instantiated",
                [],
            );
            return Some(self.unit(span));
        }
        let cause = self.cause(
            CauseKind::Source,
            span,
            format!("resolved data constructor {name}"),
            [],
        );
        if constructor.has_payload {
            let mut value = Value::scalar(
                Ty::Callable(vec![constructor.payload], Box::new(constructor.owner)),
                None,
                cause,
            );
            value.callables.push(Callable::Constructor(name.into()));
            Some(value)
        } else {
            let payload = self.unit(span);
            Some(self.wrap_constructor(name, &constructor, payload, span))
        }
    }
    pub(super) fn invoke_constructor(
        &mut self,
        name: &str,
        arguments: &[(ParameterMode, Value, Span)],
        span: Span,
        source_event: Option<crate::sema::copy_contract::CopyCallEventId>,
        frame: &mut Frame,
    ) -> Value {
        let Some(constructor) = self.constructors.get(name).cloned() else {
            self.unsupported(span, "constructor has no verified declaration identity");
            return self.unit(span);
        };
        let mut generics = BTreeSet::new();
        constructor.owner.generic_names(&mut generics);
        if !generics.is_empty() {
            self.unsupported(span,"constructor generic arguments need an explicit instance or checked expected-type inference");
            return Value::scalar(Ty::Unknown, None, CauseId(0));
        }
        if !constructor.has_payload {
            self.error(
                "E0353",
                span,
                "nullary constructor tags do not accept argument parentheses",
                [],
            );
            return self.unit(span);
        }
        let expected_arity = match &constructor.payload {
            Ty::Unit => 0,
            Ty::Tuple(items) => items.len(),
            _ => 1,
        };
        if arguments.len() != 1 && arguments.len() != expected_arity {
            self.error(
                "E0314",
                span,
                "constructor arguments do not match its single outer payload boundary",
                [],
            );
        }
        let source_valid =
            self.check_constructor_input_sources(name, arguments, source_event, frame);
        let mut payload = self.constructor_payload(arguments, span, frame);
        let payload_syntax = constructor.payload_syntax.clone();
        if let Some(syntax) = payload_syntax {
            self.set_contract_environment(&frame.env);
            if source_valid {
                self.ascribe_signature(&mut payload, &syntax);
                self.check_storage_shape(&payload, &syntax, frame);
            }
        }
        self.require_type(&payload, &constructor.payload, span);
        payload.ty = constructor.payload.clone();
        payload.unsuffixed_numeric = false;
        payload.literal_number = false;
        self.wrap_constructor(name, &constructor, payload, span)
    }
    fn wrap_constructor(
        &mut self,
        name: &str,
        constructor: &ConstructorInfo,
        payload: Value,
        span: Span,
    ) -> Value {
        let mut value = payload.clone();
        value.source_type_witness = self.constructor_source_types.get(name).cloned();
        value.ty = constructor.owner.clone();
        value.condition_inspections = Default::default();
        value.constant = None;
        value.static_coordinate = None;
        value.unsuffixed_numeric = false;
        value.literal_number = false;
        value.callables.clear();
        value.callable_bounds.clear();
        value.callable_returns.clear();
        value.signature = None;
        value.variant_tag = Some(constructor.tag.clone());
        value.variant_witnesses = [(constructor.tag.clone(), Box::new(payload))].into();
        value.variant_payload = None;
        value.result_tag = None;
        value.result_payload = None;
        value.result_success = None;
        value.result_error = None;
        value.option_tag = None;
        value.option_payload = None;
        value.option_identity = None;
        value.outer_results.clear();
        value.must_outer_results.clear();
        value.cause = self.cause(
            CauseKind::Source,
            span,
            "data constructor preserves payload storage and authority",
            [value.cause],
        );
        value
    }
    pub(super) fn constructor_callable_compatible(&self, value: &Value, expected: &Ty) -> bool {
        let Ty::Callable(parameters, result) = self.expanded(expected, &mut BTreeSet::new()) else {
            return false;
        };
        let payload = match parameters.as_slice() {
            [] => Ty::Unit,
            [one] => one.clone(),
            _ => Ty::Tuple(parameters),
        };
        !value.callables.is_empty()
            && value.callables.iter().all(|callable| {
                if let Callable::Constructor(name) = callable {
                    self.constructors.get(name).is_some_and(|constructor| {
                        constructor.has_payload
                            && self.compatible(&constructor.owner, &result)
                            && self.compatible(&constructor.payload, &payload)
                    })
                } else {
                    false
                }
            })
    }
    pub(super) fn nominal_inner(&mut self, value: &Value, span: Span, frame: &mut Frame) -> Value {
        let owner = match self.expanded(&value.ty, &mut BTreeSet::new()) {
            owner @ (Ty::Named(_) | Ty::Applied { .. }) => owner,
            _ => {
                self.error(
                    "E0308",
                    span,
                    "inner requires an exposed nominal wrapper",
                    [value.cause],
                );
                return self.unit(span);
            }
        };
        let Some(constructor) = self
            .constructors
            .iter()
            .find(|(_, constructor)| constructor.owner == owner && constructor.nominal)
            .map(|(identity, constructor)| (identity.clone(), constructor.clone()))
        else {
            self.error(
                "E0308",
                span,
                "opaque aliases and sum types do not expose nominal inner",
                [value.cause],
            );
            return self.unit(span);
        };
        let (identity, constructor) = constructor;
        if self.declaration_files.contains(&constructor.span.file.0) {
            self.error(
                "E0907",
                span,
                "foreign nominal representation cannot be inspected",
                [value.cause],
            );
            return self.unit(span);
        }
        self.constructor_pattern_payload(value, &identity, span, frame)
            .unwrap_or_else(|| self.unit(span))
    }
    pub(super) fn constructor_pattern_payload(
        &mut self,
        source: &Value,
        name: &str,
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        let constructor = self.constructor_pattern_info(name, source)?;
        self.require_type(source, &constructor.owner, span);
        if self.declaration_files.contains(&constructor.span.file.0) && constructor.nominal {
            self.error(
                "E0907",
                span,
                "foreign nominal representation cannot be deconstructed",
                [source.cause],
            );
            return Some(self.unit(span));
        }
        let mut payload = if let Some(payload) = source.variant_witnesses.get(&constructor.tag) {
            *payload.clone()
        } else if source.variant_tag.as_deref() == Some(&constructor.tag) {
            source
                .variant_payload
                .as_ref()
                .map(|payload| *payload.clone())
                .unwrap_or_else(|| self.unit(span))
        } else {
            let slot = Slot::Field(format!("$variant:{}", constructor.tag));
            let mut alternatives: Vec<_> = source
                .origins
                .nodes
                .iter()
                .filter_map(|node| self.fields.get(&(*node, slot.clone())).cloned())
                .collect();
            if let Some(mut payload) = alternatives.pop() {
                for next in alternatives {
                    payload = payload.join(&next, self.choice(), source.cause);
                }
                payload
            } else if !constructor.has_payload {
                self.unit(span)
            } else {
                self.unsupported(span, "sum/nominal payload has no proved storage shape");
                return Some(self.unit(span));
            }
        };
        payload.ty = constructor.payload;
        if let Some(syntax) = constructor.payload_syntax.as_ref()
            && let Some(syntax) = normalize_closed_source_syntax(syntax, &self.types, self.layout)
        {
            // The constructor's original/instantiated payload declaration,
            // rather than its erased semantic type, retains fixed dimensions
            // and callable modes for both formals and concrete wrappers.
            payload.source_type_witness = self.source_type_from_frozen_syntax(&syntax);
        }
        payload.permission = payload.permission.meet(source.permission);
        if matches!(payload.ty, Ty::Immutable(_)) {
            payload.permission = Permission::Read;
            payload.publication = Publication::Immutable;
        }
        payload.sources = source.sources.clone();
        payload.participants = source.participants.clone();
        payload.temporary |= source.temporary;
        // A publication consumes its sharing acknowledgement. Only a marker on
        // this current access path may authorize another writable alias.
        payload.marker = source.marker || (source.construction && payload.marker);
        payload.construction &= source.construction;
        if !payload.construction && payload.publication == Publication::Unpublished {
            payload.publication = source.publication;
        }
        payload.internal_aliases |= source.internal_aliases;
        payload.retention_result =
            source.retention_result || (source.construction && payload.retention_result);
        payload.through_return |= source.through_return;
        payload.scoped.extend(&source.scoped);
        self.access(source, None, Mode::Read, span, frame);
        Some(payload)
    }
    pub(super) fn constructor_formal(
        &mut self,
        ty: &Ty,
        index: u32,
        span: Span,
        seen: &mut BTreeSet<String>,
    ) -> Option<Value> {
        if !matches!(ty, Ty::Named(_) | Ty::Applied { .. }) {
            return None;
        }
        let mut constructors: Vec<_> = self
            .constructors
            .iter()
            .filter(|(_, constructor)| constructor.owner == *ty)
            .map(|(name, constructor)| (name.clone(), constructor.clone()))
            .collect();
        if constructors.is_empty() {
            constructors = self.conditional_constructor_schemas(ty).unwrap_or_default();
        }
        if constructors.is_empty() {
            return None;
        }
        if !seen.insert(format!("constructor:{ty:?}")) {
            self.unsupported(span, "recursive nominal/sum payload finite shape");
            return None;
        }
        if constructors.len() == 1 && constructors[0].1.nominal {
            let (name, constructor) = &constructors[0];
            let payload = self.formal_value(constructor.payload.clone(), index, span, seen);
            return Some(self.wrap_constructor(name, constructor, payload, span));
        }
        let cause = self.cause(
            CauseKind::Source,
            span,
            "formal sum retains each possible constructor payload shape",
            [],
        );
        let node = self
            .heap
            .symbolic(Pivot(self.heap.nodes.len() as u32), ScopeId(0), cause);
        let mut value = Value::reference(ty.clone(), node, cause);
        value.construction = false;
        value.publication = Publication::Live;
        for (index_offset, (_name, constructor)) in constructors.into_iter().enumerate() {
            let payload = self.formal_value(
                constructor.payload,
                index.wrapping_mul(31).wrapping_add(index_offset as u32 + 1),
                span,
                &mut seen.clone(),
            );
            if !payload.results.is_empty() {
                self.unsupported(
                    span,
                    "unknown sum variant requires conditional nested Result coverage",
                );
            }
            value.results.extend(&payload.results);
            value.must_results.extend(&payload.must_results);
            value.scoped.extend(&payload.scoped);
            value
                .callback_parameters
                .extend(&payload.callback_parameters);
            value.mutable_environment |= payload.mutable_environment;
            value.observer_environment |= payload.observer_environment;
            self.store_field(
                node,
                Slot::Field(format!("$variant:{}", constructor.tag)),
                payload.clone(),
            );
            value
                .variant_witnesses
                .insert(constructor.tag, Box::new(payload));
        }
        Some(value)
    }
    pub(super) fn constructor_projection(
        &mut self,
        source: &Value,
        slot: &Slot,
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        let owner = self.expanded(&source.ty, &mut BTreeSet::new());
        if !matches!(owner, Ty::Named(_) | Ty::Applied { .. }) {
            return None;
        }
        if self.foreign_opaque_type(&owner) {
            self.error(
                "E0907",
                span,
                "foreign opaque representation cannot be projected",
                [source.cause],
            );
            return Some(self.unit(span));
        }
        if !self
            .constructors
            .values()
            .any(|constructor| constructor.owner == owner)
        {
            return None;
        }
        let Some(name) = &source.variant_tag else {
            self.error(
                "E0337",
                span,
                "sum payload projection requires a proved constructor narrowing",
                [source.cause],
            );
            return Some(self.unit(span));
        };
        let constructor = self.constructor_pattern_info(name, source)?;
        if constructor.nominal || !constructor.has_payload {
            self.error(
                "E0337",
                span,
                "nominal wrappers and nullary tags expose no direct product members",
                [source.cause],
            );
            return Some(self.unit(span));
        }
        let payload = self.constructor_pattern_payload(source, name, span, frame)?;
        let shape = self.expanded(&payload.ty, &mut BTreeSet::new());
        match (&shape, slot) {
            (Ty::Tuple(_), Slot::Tuple(_)) => {
                self.record_variant_projection(
                    frame.callable_owner,
                    span,
                    super::super::VariantProjection {
                        tag: name.clone(),
                        cause: source.cause,
                        direct: false,
                    },
                );
                Some(self.project(&payload, slot.clone(), span, frame, true))
            }
            (Ty::Record(_), Slot::Field(_)) => {
                self.record_variant_projection(
                    frame.callable_owner,
                    span,
                    super::super::VariantProjection {
                        tag: name.clone(),
                        cause: source.cause,
                        direct: false,
                    },
                );
                Some(self.project(&payload, slot.clone(), span, frame, true))
            }
            (_, Slot::Tuple(0)) if !matches!(shape, Ty::Tuple(_) | Ty::Record(_)) => {
                self.record_variant_projection(
                    frame.callable_owner,
                    span,
                    super::super::VariantProjection {
                        tag: name.clone(),
                        cause: source.cause,
                        direct: true,
                    },
                );
                Some(payload)
            }
            _ => {
                self.error(
                    "E0337",
                    span,
                    "sum payload coordinate is not present in the proved constructor",
                    [source.cause],
                );
                Some(self.unit(span))
            }
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    fn check(source: &str) -> crate::sema::AnalyzeOutcome {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        crate::sema::analyze(&parsed.program, FileId(0))
    }
    #[test]
    fn constructors_have_nominal_identity_and_only_one_tuple_boundary() {
        let result = check(
            "type UserId(int)\ntype Marker\ntype Pair { Item(int, str), Empty, Ready() }\nfn example() { assert(inner(UserId(7)) == 7); assert(inner(Marker) == ()); let make: fn((int, str)) -> Pair = Pair::Item; let expanded: fn(int, str) -> Pair = Pair::Item; assert(make((1, \"a\")) == expanded(1, \"a\")); assert(Pair::Item(1, \"a\") == Pair::Item((1, \"a\"))); let empty = Pair::Empty; let ready = Pair::Ready() }",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let facts = result.program.unwrap();
        let pair = facts
            .syntax()
            .statements
            .iter()
            .find_map(|statement| match &statement.kind {
                StmtKind::Type(declaration)
                    if declaration
                        .variants
                        .iter()
                        .any(|variant| variant.name == "Ready") =>
                {
                    Some(declaration.name.clone())
                }
                _ => None,
            })
            .unwrap();
        assert!(!facts.facts().constructors[&format!("{pair}::Empty")].has_payload);
        assert!(facts.facts().constructors[&format!("{pair}::Ready")].has_payload);
        let result = check(
            "type Node { Branch((int, int), str) }\nfn example() { let value = Node::Branch(1, 2, \"a\") }",
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0314"),
            "{:?}",
            result.diagnostics
        );
    }
    #[test]
    fn nominal_inner_preserves_existing_readonly_payload_authority() {
        let result = check(
            "type Cell = { mut value: int }\ntype Box(Cell)\nfn example() { let base = Cell.{value: 1}; let wrapped = Box(base); let mut extracted = inner(wrapped); extracted.value += 1 }",
        );
        assert!(result.program.is_none());
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| matches!(diagnostic.code.as_str(), "E0520" | "E0528")),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result = check(
            "type Cell = { mut value: int }\ntype Box(Cell)\nfn example() { let wrapped = Box(Cell.{value: 1}); let _ = wrapped.value }",
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0337"),
            "{:?}",
            result.diagnostics
        );
        let result = check(
            "type Cell = { mut value: int }\ntype Box(Cell)\nfn example() { let mut cell = Cell.{value: 1}; let mut wrapped = Box(^mut cell); let mut alias = inner(wrapped); alias.value += 1; cell.value += 1 }",
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0510"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result = check(
            "type Cell = { mut value: int }\ntype Box(Cell)\nfn copy(source: Box, mut target: Cell) &mut { target.value = inner(source).value }\nfn example() { let mut cell = Cell.{value: 1}; copy(Box(^mut cell), mut cell) }",
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0524"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result = check(
            "type Cell = { mut value: int }\ntype Box(Cell)\nfn example() { let mut wrapped = Box(Cell.{value: 1}); let mut alias = inner(wrapped); alias.value += 1; let _ = inner(wrapped).value }",
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0510"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn mutable_wrapper_parameters_authorize_only_the_selected_payload_root() {
        let valid = check(
            "type Cell={mut value:int}\ntype Wrap(Cell)\nfn edit(mut wrapped:Wrap)&mut{inner(wrapped).value+=1}",
        );
        assert!(
            valid.program.is_some(),
            "{:?} {:?}",
            valid.diagnostics,
            valid.unsupported
        );
        for source in [
            "type Cell={mut value:int}\ntype Wrap({child:Cell})\nfn bad(){let cell=Cell.{value:0};let mut wrapped=Wrap(.{child:cell});inner(wrapped).child.value+=1}",
            "type Cell={mut value:int}\ntype Wrap(Immut<Cell>)\nfn bad(mut wrapped:Wrap)&mut{inner(wrapped).value+=1}",
            "type Cell={mut value:int}\ntype Wrap(Cell)\nfn bad(){let cell=Cell.{value:0};let mut wrapped=Wrap(cell);inner(wrapped).value+=1}",
        ] {
            let result = check(source);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0520"),
                "{source}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn foreign_opacity_precedes_nominal_product_projection_diagnostics() {
        let session = crate::session::Session::with_project(
            "virtual/root.ril".into(),
            vec![
                crate::session::ProjectSource {
                    path: "virtual/root.ril".into(),
                    bytes: b"use foreign\nfn example(value:Foreign::Object){let _=value.id}"
                        .to_vec(),
                },
                crate::session::ProjectSource {
                    path: "virtual/foreign.d.ril".into(),
                    bytes: b"pub type Object".to_vec(),
                },
            ],
            crate::session::CheckOptions::default(),
        )
        .unwrap();
        let crate::session::CompilationOutcome::Rejected { diagnostics } = session.check() else {
            panic!("opaque field must be rejected");
        };
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0907"),
            "{diagnostics:?}"
        );
        assert!(
            !diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0337"),
            "opacity was replaced by an ordinary product error"
        );
    }
    #[test]
    fn constructor_boundaries_keep_fixed_payload_constraints_and_projection_certificates() {
        let wrong = check("type Fixed([2]int)\nfn example() {let value=Fixed([1])}");
        assert!(
            wrong
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0301"),
            "{:?} {:?}",
            wrong.diagnostics,
            wrong.unsupported
        );
        let valid = check("type Fixed([2]int)\nfn identity(value:Fixed)->[2]int {inner(value)}");
        assert!(
            valid.program.is_some(),
            "{:?} {:?}",
            valid.diagnostics,
            valid.unsupported
        );
        let valid = check(
            "type Entry {Pair(int,str),Row({label:str}),One(int)}\nfn read()->str {let pair=Entry::Pair(1,\"pair\");let row=Entry::Row(.{label:\"row\"});assert(pair.1==\"pair\");row.label}",
        );
        assert!(
            valid.program.is_some(),
            "{:?} {:?}",
            valid.diagnostics,
            valid.unsupported
        );
        let program = valid.program.unwrap();
        let owner = program
            .syntax()
            .statements
            .iter()
            .find_map(|statement| match &statement.kind {
                StmtKind::Type(declaration)
                    if declaration
                        .variants
                        .iter()
                        .any(|variant| variant.name == "Row") =>
                {
                    Some(declaration.name.clone())
                }
                _ => None,
            })
            .unwrap();
        let pair_tag = program.facts().constructors[&format!("{owner}::Pair")]
            .tag
            .clone();
        let row_tag = program.facts().constructors[&format!("{owner}::Row")]
            .tag
            .clone();
        assert!(
            program
                .facts()
                .variant_projections
                .values()
                .any(|projection| projection.tag == pair_tag && !projection.direct)
        );
        assert!(
            program
                .facts()
                .variant_projections
                .values()
                .any(|projection| projection.tag == row_tag && !projection.direct)
        );
    }
}
