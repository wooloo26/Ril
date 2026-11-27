use std::collections::{HashMap, HashSet};

use ril_hir::DefinitionId;
use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::{
    Ast, ExprId, LiteralKind, MatchArm, Mode, Pattern, PatternId, StmtKind, Type, TypeDefinition,
    TypeId, Variant,
};

pub fn text_slice_fragment(ast: &Ast, items: &[PatternId]) -> Option<String> {
    let mut fragment = String::new();
    for &item in items {
        let Pattern::Literal(literal) = &ast.pattern(item).value else {
            return None;
        };
        let Value::Str(value) = super::literal(literal).ok()? else {
            return None;
        };
        if value.is_empty() {
            return None;
        }
        fragment.push_str(&value);
    }
    Some(fragment)
}

use super::{
    AdtKind, GenericValue, Member, Ty, Value,
    check::{Checker, Env},
    literal,
};

#[derive(Clone, Default)]
pub(super) struct MatchedValues {
    pub locals: HashMap<DefinitionId, Value>,
    pub paths: HashMap<DefinitionId, (Vec<Value>, Mode)>,
}

impl MatchedValues {
    fn bind(&mut self, id: DefinitionId, value: &Value, place: Option<&[Value]>, mode: Mode) {
        self.locals.insert(id, value.clone());
        if let Some(place) = place {
            self.paths.insert(id, (place.to_vec(), mode));
        }
    }
}

fn next_coordinate(place: Option<&[Value]>, key: impl FnOnce() -> Value) -> Option<Vec<Value>> {
    let mut path = place?.to_vec();
    path.push(key());
    Some(path)
}

impl Checker<'_> {
    pub(super) fn pattern(&mut self, env: &mut Env, id: PatternId, input: &Ty) {
        let ast = self.ast(env.file);
        let node = ast.pattern(id);
        let mut normalized = self.normalize(input);
        self.types.insert(node.span, normalized.clone());
        if !matches!(node.value, Pattern::Binding(..) | Pattern::Wildcard)
            && let Ty::Draft(representation) = normalized
        {
            normalized = *representation;
        }
        match &node.value {
            Pattern::Binding(_, name) | Pattern::Rest(Some(name)) => {
                self.define_name(name, normalized);
            }
            Pattern::Unit => {
                self.require(env, node.span, &Ty::Unit, &normalized);
            }
            Pattern::Wildcard | Pattern::Rest(None) => {}
            Pattern::Literal(syntax) => {
                let ty = self.literal_type(syntax, node.span);
                self.require(env, node.span, &ty, &normalized);
            }
            Pattern::Range {
                low,
                high,
                inclusive,
            } => {
                if low.kind != LiteralKind::Int || high.kind != LiteralKind::Int {
                    self.error(
                        Code::E0348,
                        node.span,
                        "range patterns require integer endpoints",
                    );
                } else if let (Ok(Value::Int(a)), Ok(Value::Int(b))) = (literal(low), literal(high))
                {
                    if a > b || a == b && !inclusive {
                        self.error(Code::E0348, node.span, "range pattern is empty");
                    }
                    self.require(env, node.span, &Ty::Int, &normalized);
                }
            }
            Pattern::Or(items) => {
                let mut domain: Option<HashMap<String, (bool, Mode)>> = None;
                let binders = self.hir.bindings_within(node.span);
                let mut types = HashMap::new();
                for &item in items {
                    let names = self.pattern_binding_modes(env, item);
                    if domain.as_ref().is_some_and(|expected| expected != &names) {
                        self.error(
                            Code::E0346,
                            ast.pattern(item).span,
                            "alternative patterns must bind the same names with matching modes",
                        );
                    }
                    domain = Some(names);
                    self.pattern(env, item, input);
                    for &binder in &binders {
                        let Some(ty) = self.bindings.get(&binder).cloned() else {
                            continue;
                        };
                        if let Some(prior) = types.get(&binder) {
                            self.require(env, ast.pattern(item).span, &ty, prior);
                            self.bindings.insert(binder, prior.clone());
                        } else {
                            types.insert(binder, ty);
                        }
                    }
                }
            }
            Pattern::Tuple(items) => {
                if let Ty::Tuple(components) = &normalized {
                    if items.len() != components.len() {
                        self.error(Code::E0314, node.span, "tuple pattern has the wrong arity");
                    }
                    for (&item, ty) in items.iter().zip(components) {
                        self.pattern(env, item, &ty.ty);
                    }
                } else if matches!(normalized, Ty::Unknown | Ty::Infer(_)) {
                    let shape: Vec<_> = items.iter().map(|_| Member::plain(self.fresh())).collect();
                    self.fits(env, &Ty::Tuple(shape.clone()), &normalized);
                    for (&item, ty) in items.iter().zip(shape) {
                        self.pattern(env, item, &ty.ty);
                    }
                } else {
                    self.error(Code::E0301, node.span, "tuple pattern requires a tuple");
                }
            }
            Pattern::Slice { text, elements } => {
                if *text && elements.is_empty() {
                    self.error(
                        Code::E0349,
                        node.span,
                        "empty string slice pattern is invalid",
                    );
                }
                let element = if *text {
                    self.require(env, node.span, &normalized, &Ty::Str);
                    Ty::Str
                } else if let Ty::Array(element) = &normalized {
                    element.ty.clone()
                } else if matches!(normalized, Ty::Infer(_) | Ty::Unknown) {
                    self.fresh()
                } else {
                    self.error(Code::E0301, node.span, "array pattern requires an array");
                    Ty::Unknown
                };
                let mut rest = false;
                for &item in elements {
                    if matches!(ast.pattern(item).value, Pattern::Rest(_)) {
                        if rest {
                            self.error(
                                Code::E0349,
                                ast.pattern(item).span,
                                "only one rest element is allowed",
                            );
                        }
                        rest = true;
                        self.pattern(env, item, &normalized);
                    } else if *text
                        && text_slice_fragment(ast, std::slice::from_ref(&item)).is_none()
                    {
                        self.error(
                            Code::E0349,
                            ast.pattern(item).span,
                            "string slice fragments require nonempty string literals",
                        );
                    } else {
                        self.pattern(env, item, &element);
                    }
                }
            }
            Pattern::Constructor(path, items) => {
                let resolved_ctor = self.resolve(path.span);
                if let Some(id) = resolved_ctor
                    && self.hir.definition(id).kind == ril_hir::DefinitionKind::Type
                    && (items.is_some() || !self.hir.unit_constructor(id))
                {
                    self.error(
                        Code::E0349,
                        node.span,
                        "nominal pattern requires 'Name::(...)' syntax",
                    );
                    for &item in items.iter().flatten() {
                        self.pattern(env, item, &Ty::Unknown);
                    }
                    return;
                }
                let name = resolved_ctor
                    .map(|id| self.hir.definition(id).name.value.as_str())
                    .unwrap_or_else(|| {
                        path.segments
                            .last()
                            .map_or("", |part| part.name.value.as_str())
                    });
                let payload =
                    self.pattern_payload(env, name, resolved_ctor, &normalized, node.span);
                let unit_payload =
                    payload.as_slice() == [Ty::Unit] && items.as_ref().is_some_and(Vec::is_empty);
                if !unit_payload && payload.len() != items.as_ref().map_or(0, Vec::len) {
                    self.error(
                        Code::E0314,
                        node.span,
                        "constructor pattern has the wrong payload arity",
                    );
                }
                for (&item, ty) in items.iter().flatten().zip(payload) {
                    self.pattern(env, item, &ty);
                }
            }
            Pattern::Wrap(path, items) => {
                let resolved_ctor = self.resolve(path.span);
                if let Some(id) = resolved_ctor
                    && self.hir.definition(id).kind != ril_hir::DefinitionKind::Type
                {
                    self.error(
                        Code::E0349,
                        node.span,
                        "'::(...)' pattern is only valid for nominal or opaque wrapper types",
                    );
                    for &item in items {
                        self.pattern(env, item, &Ty::Unknown);
                    }
                    return;
                }
                let name = resolved_ctor
                    .map(|id| self.hir.definition(id).name.value.as_str())
                    .unwrap_or_else(|| {
                        path.segments
                            .last()
                            .map_or("", |part| part.name.value.as_str())
                    });
                let payload =
                    self.wrap_pattern_payload(env, name, resolved_ctor, &normalized, node.span);
                let unit_payload = payload.as_slice() == [Ty::Unit] && items.is_empty();
                if !unit_payload && payload.len() != items.len() {
                    self.error(
                        Code::E0314,
                        node.span,
                        "nominal pattern has the wrong payload arity",
                    );
                }
                for (&item, ty) in items.iter().zip(payload) {
                    self.pattern(env, item, &ty);
                }
            }
            Pattern::Record { fields, rest } => {
                if let Ty::Record(known, open) = normalized {
                    let mut seen_fields = HashSet::new();
                    for field in fields {
                        if !seen_fields.insert(field.name.value.as_str()) {
                            self.error(
                                Code::E0210,
                                field.name.span,
                                "duplicate record field in pattern",
                            );
                        }
                    }
                    if !rest && !open && seen_fields.len() != known.len() {
                        self.error(
                            Code::E0307,
                            node.span,
                            "record pattern requires every field or a rest",
                        );
                    }
                    for field in fields {
                        let ty = known
                            .get(&field.name.value)
                            .map(|m| &m.ty)
                            .unwrap_or(&Ty::Unknown);
                        if ty == &Ty::Unknown && !open {
                            self.error(
                                Code::E0336,
                                field.name.span,
                                "unknown record field in pattern",
                            );
                        }
                        if let Some(pattern) = field.pattern {
                            self.pattern(env, pattern, ty);
                        } else {
                            self.define_name(&field.name, ty.clone());
                        }
                    }
                } else if normalized != Ty::Unknown {
                    self.error(Code::E0301, node.span, "record pattern requires a record");
                }
            }
            Pattern::Subset { ty, binding } => {
                let subset = self.type_expr(env, *ty);
                if !matches!(normalized, Ty::Unknown | Ty::Never)
                    && !self.sum_subset(env, &subset, &normalized)
                {
                    self.error(
                        Code::E0301,
                        node.span,
                        "subset pattern requires a sum included in the input",
                    );
                }
                if let Ty::Adt(adt) = &subset {
                    let tags = self.sum_variants(adt).into_keys().collect();
                    self.subset_tags.insert(node.span, tags);
                }
                if let Some(binding) = binding {
                    self.pattern(env, *binding, &subset);
                }
            }
            Pattern::Type(ty) => {
                self.check_type_pattern_syntax(env, *ty);
                if let Ty::TypeValue(Some(inner)) = &normalized {
                    self.match_type_pattern(env, *ty, inner);
                } else if !matches!(normalized, Ty::Unknown | Ty::TypeValue(None)) {
                    self.error(Code::E0301, node.span, "type pattern requires a type value");
                }
            }
            Pattern::TypeBinding(name) => self.define_name(name, normalized),
        }
    }

    pub(super) fn pattern_names(&self, env: &Env, id: PatternId) -> HashSet<String> {
        let ast = self.ast(env.file);
        match &ast.pattern(id).value {
            Pattern::Binding(_, name) | Pattern::Rest(Some(name)) | Pattern::TypeBinding(name) => {
                HashSet::from([name.value.clone()])
            }
            Pattern::Tuple(items)
            | Pattern::Slice {
                elements: items, ..
            }
            | Pattern::Or(items) => items
                .iter()
                .flat_map(|&item| self.pattern_names(env, item))
                .collect(),
            Pattern::Constructor(_, payload) => payload
                .iter()
                .flatten()
                .flat_map(|&item| self.pattern_names(env, item))
                .collect(),
            Pattern::Wrap(_, payload) => payload
                .iter()
                .flat_map(|&item| self.pattern_names(env, item))
                .collect(),
            Pattern::Record { fields, .. } => fields
                .iter()
                .flat_map(|field| {
                    field.pattern.map_or_else(
                        || HashSet::from([field.name.value.clone()]),
                        |id| self.pattern_names(env, id),
                    )
                })
                .collect(),
            Pattern::Subset {
                binding: Some(id), ..
            } => self.pattern_names(env, *id),
            _ => HashSet::new(),
        }
    }

    fn pattern_binding_modes(&self, env: &Env, id: PatternId) -> HashMap<String, (bool, Mode)> {
        let mut out = HashMap::new();
        self.collect_pattern_binding_modes(env, id, &mut out);
        out
    }

    fn collect_pattern_binding_modes(
        &self,
        env: &Env,
        id: PatternId,
        out: &mut HashMap<String, (bool, Mode)>,
    ) {
        let ast = self.ast(env.file);
        match &ast.pattern(id).value {
            Pattern::Binding(storage, name) => {
                out.insert(name.value.clone(), (storage.variable, storage.mode));
            }
            Pattern::Rest(Some(name)) | Pattern::TypeBinding(name) => {
                out.insert(name.value.clone(), (false, Mode::Plain));
            }
            Pattern::Tuple(items)
            | Pattern::Slice {
                elements: items, ..
            }
            | Pattern::Or(items) => {
                for &item in items {
                    self.collect_pattern_binding_modes(env, item, out);
                }
            }
            Pattern::Constructor(_, payload) => {
                for &item in payload.iter().flatten() {
                    self.collect_pattern_binding_modes(env, item, out);
                }
            }
            Pattern::Wrap(_, payload) => {
                for &item in payload {
                    self.collect_pattern_binding_modes(env, item, out);
                }
            }
            Pattern::Record { fields, .. } => {
                for field in fields {
                    if let Some(pattern) = field.pattern {
                        self.collect_pattern_binding_modes(env, pattern, out);
                    } else {
                        out.insert(
                            field.name.value.clone(),
                            (field.storage.variable, field.storage.mode),
                        );
                    }
                }
            }
            Pattern::Subset {
                binding: Some(id), ..
            } => self.collect_pattern_binding_modes(env, *id, out),
            _ => {}
        }
    }

    fn pattern_payload(
        &mut self,
        env: &Env,
        name: &str,
        resolved: Option<DefinitionId>,
        ty: &Ty,
        span: Span,
    ) -> Vec<Ty> {
        let variant_parent = resolved.and_then(|id| match self.hir.definition(id).kind {
            ril_hir::DefinitionKind::Variant(parent) => Some(parent),
            _ => None,
        });
        match (name, ty) {
            (
                "Let" | "Var" | "Mut" | "SharedMut" | "Ref" | "VarMut" | "VarSharedMut" | "VarRef",
                Ty::Mode,
            ) if variant_parent
                .is_none_or(|p| self.hir.std_type(p) == Some(ril_hir::StdType::FieldMode)) =>
            {
                Vec::new()
            }
            (_, Ty::Adt(adt))
                if matches!(adt.kind, AdtKind::Opaque | AdtKind::OpaqueSum)
                    && adt.defining_scope != env.scope =>
            {
                self.error(Code::E0308, span, "opaque representation is sealed");
                Vec::new()
            }
            (_, Ty::Adt(adt)) if matches!(adt.kind, AdtKind::Sum | AdtKind::OpaqueSum) => {
                if let Some(parent) = variant_parent
                    && parent != adt.definition
                {
                    let parent_def = self.hir.definition(parent);
                    let parent_is_linear = parent_def.stmt.is_some_and(|stmt| {
                        matches!(
                            &self.ast(parent_def.name.span.file).stmt(stmt).value.kind,
                            StmtKind::Type(decl) if decl.is_linear
                        )
                    });
                    let parent_adt = Ty::Adt(std::sync::Arc::new(super::Adt {
                        definition: parent,
                        kind: AdtKind::Sum,
                        is_linear: parent_is_linear,
                        defining_scope: parent_def.scope,
                        visibility: parent_def.visibility,
                        arguments: adt.arguments.clone(),
                    }));
                    if !self.sum_subset(env, &parent_adt, ty) {
                        self.error(
                            Code::E0301,
                            span,
                            format!(
                                "constructor {name} does not belong to {}",
                                ty.display(self.hir)
                            ),
                        );
                        return Vec::new();
                    }
                }
                self.sum_variants(adt).remove(name).unwrap_or_else(|| {
                    self.error(
                        Code::E0301,
                        span,
                        format!(
                            "constructor {name} never appears in {}",
                            ty.display(self.hir)
                        ),
                    );
                    Vec::new()
                })
            }
            (_, Ty::Adt(adt))
                if resolved.is_some_and(|id| id == adt.definition)
                    || (resolved.is_none()
                        && self.hir.definition(adt.definition).name.value == name) =>
            {
                if self.hir.unit_constructor(adt.definition) {
                    Vec::new()
                } else {
                    self.error(
                        Code::E0349,
                        span,
                        "nominal pattern requires 'Name::(...)' syntax",
                    );
                    Vec::new()
                }
            }
            (_, Ty::Unknown | Ty::Infer(_)) => Vec::new(),
            _ => {
                self.error(
                    Code::E0301,
                    span,
                    format!(
                        "constructor {name} is incompatible with {}",
                        ty.display(self.hir)
                    ),
                );
                Vec::new()
            }
        }
    }

    fn wrap_pattern_payload(
        &mut self,
        env: &Env,
        name: &str,
        resolved: Option<DefinitionId>,
        ty: &Ty,
        span: Span,
    ) -> Vec<Ty> {
        match ty {
            Ty::Adt(adt)
                if matches!(adt.kind, AdtKind::Opaque | AdtKind::OpaqueSum)
                    && adt.defining_scope != env.scope =>
            {
                self.error(Code::E0308, span, "opaque representation is sealed");
                Vec::new()
            }
            Ty::Adt(adt) if matches!(adt.kind, AdtKind::Sum | AdtKind::OpaqueSum) => {
                self.error(
                    Code::E0349,
                    span,
                    "sum variants do not use nominal '::(...)' pattern syntax",
                );
                Vec::new()
            }
            Ty::Adt(adt)
                if resolved.is_some_and(|id| id == adt.definition)
                    || (resolved.is_none()
                        && self.hir.definition(adt.definition).name.value == name) =>
            {
                if self.hir.unit_constructor(adt.definition) {
                    self.error(
                        Code::E0349,
                        span,
                        "unit nominal type does not use '::(...)' pattern syntax",
                    );
                    return Vec::new();
                }
                match self.representation(env, adt) {
                    Some(Ty::Tuple(items)) => items.into_iter().map(|m| m.ty).collect(),
                    Some(inner) => vec![inner],
                    None => Vec::new(),
                }
            }
            Ty::Unknown | Ty::Infer(_) => Vec::new(),
            _ => {
                self.error(
                    Code::E0301,
                    span,
                    format!(
                        "nominal pattern {name}::(...) is incompatible with {}",
                        ty.display(self.hir)
                    ),
                );
                Vec::new()
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn check_match(
        &mut self,
        env: &mut Env,
        is_meta: bool,
        arms: &[MatchArm],
        (value, input): (ExprId, &Ty),
        expected: Option<&Ty>,
        span: Span,
        check_tail: bool,
    ) -> Ty {
        let normalized_input = self.normalize(input);
        if is_meta {
            if env.phase != super::check::Phase::Runtime {
                self.error(
                    Code::E0810,
                    span,
                    "'meta match' is only allowed in runtime functions; compile-time code uses plain 'match'",
                );
            }
            let mut concrete = env.clone();
            concrete.phase = super::check::Phase::MetaValue;
            concrete.require_concrete_types = true;
            match self.evaluate_static(&concrete, value) {
                Ok(val) => {
                    if !matches!(val, Value::Type(_)) {
                        let val_span = self.ast(env.file).expr(value).span;
                        self.static_values.insert(val_span, val.clone());
                    }
                    let mut dependent = false;
                    for (index, arm) in arms.iter().enumerate() {
                        let mut local = env.clone();
                        let mut bindings = Default::default();
                        match self.value_pattern(&mut local, arm.pattern, &val, &mut bindings) {
                            Ok(true) => {}
                            Ok(false) => continue,
                            Err(super::eval::Signal::Dependent(_)) => {
                                dependent = true;
                                break;
                            }
                            Err(failure) => {
                                let diag = failure
                                    .diagnostic(self.ast(env.file).pattern(arm.pattern).span);
                                self.diagnostics.push(diag);
                                return Ty::Unknown;
                            }
                        }
                        if let Some(guard) = arm.guard {
                            let mut guard_eval = local.clone();
                            guard_eval.phase = super::check::Phase::MetaValue;
                            match self.evaluate_with_bindings(&guard_eval, guard, &mut bindings) {
                                Ok(Value::Bool(true)) => {}
                                Ok(Value::Bool(false)) => continue,
                                Ok(_) => {
                                    let mut guard_env = local.clone();
                                    guard_env.phase = super::check::Phase::MetaValue;
                                    if env.phase == super::check::Phase::Runtime {
                                        let arm_span = self
                                            .ast(env.file)
                                            .pattern(arm.pattern)
                                            .span
                                            .join(self.ast(env.file).expr(guard).span);
                                        guard_env.static_boundary = Some(arm_span);
                                    }
                                    self.expect(&mut guard_env, guard, &Ty::Bool);
                                    return Ty::Unknown;
                                }
                                Err(super::eval::Signal::Dependent(_)) => {
                                    dependent = true;
                                    break;
                                }
                                Err(failure) => {
                                    let diag =
                                        failure.diagnostic(self.ast(env.file).expr(guard).span);
                                    self.diagnostics.push(diag);
                                    return Ty::Unknown;
                                }
                            }
                        }
                        self.meta_match_decisions.insert(span, index);
                        self.pattern(&mut local, arm.pattern, input);
                        self.refine_type_arm(&mut local, arm.pattern, input, &HashSet::new());
                        if let Some(guard) = arm.guard {
                            let mut guard_env = local.clone();
                            guard_env.phase = super::check::Phase::MetaValue;
                            if env.phase == super::check::Phase::Runtime {
                                let arm_span = self
                                    .ast(env.file)
                                    .pattern(arm.pattern)
                                    .span
                                    .join(self.ast(env.file).expr(guard).span);
                                guard_env.static_boundary = Some(arm_span);
                            }
                            self.expect(&mut guard_env, guard, &Ty::Bool);
                        }
                        if check_tail {
                            local.checking_fn_tail = true;
                        }
                        let found = self.expr(&mut local, arm.body, expected);
                        env.effects_seen.extend(local.effects_seen);
                        return found;
                    }
                    // No arm matched (unless a dependent pattern/guard broke out above).
                    if !dependent && !arms.iter().any(|a| a.guard.is_some()) {
                        self.error(
                            Code::E0303,
                            span,
                            "meta match does not cover the compile-time value",
                        );
                        return Ty::Unknown;
                    }
                }
                Err(super::eval::Signal::Dependent(_)) => {}
                Err(failure) => {
                    let diag = failure.diagnostic(self.ast(env.file).expr(value).span);
                    self.diagnostics.push(diag);
                }
            }
        } else if env.phase == super::check::Phase::Runtime {
            let has_type_pat = arms
                .iter()
                .any(|arm| self.pattern_contains_type(env, arm.pattern));
            if matches!(normalized_input, Ty::TypeValue(_)) || has_type_pat {
                self.error(
                    Code::E0816,
                    span,
                    "matching a type value in runtime code requires 'meta match'",
                );
            }
        }

        let mut prior = Vec::new();
        let mut covered = HashSet::new();
        let mut result = Ty::Never;
        let staged = is_meta && self.stage_match(env, span, value, arms);
        let mut remaining_env = env.clone();
        let mut merged_dbm: Option<super::dbm::Dbm> = None;
        for (index, arm) in arms.iter().enumerate() {
            let mut local = remaining_env.clone();
            if staged {
                local.staging_gates.push(super::staging::StaticGate::Match {
                    span,
                    expected: index,
                });
            }
            self.pattern(&mut local, arm.pattern, input);
            self.seed_pattern_proofs(&mut local, arm.pattern, value);
            if is_meta || env.phase != super::check::Phase::Runtime {
                self.refine_type_arm(&mut local, arm.pattern, input, &covered);
            }
            let (_, pattern_tags) = self.pattern_tags(env, arm.pattern, input);
            let shape = self.pattern_shape(env, arm.pattern, input);
            if !self.useful(env, &prior, shape.clone(), input) {
                self.error(
                    Code::E0304,
                    self.ast(env.file).pattern(arm.pattern).span,
                    "unreachable match arm",
                );
            }
            if let Some(guard) = arm.guard {
                if is_meta {
                    let mut guard_env = local.clone();
                    guard_env.phase = super::check::Phase::MetaValue;
                    if env.phase == super::check::Phase::Runtime {
                        let arm_span = self
                            .ast(env.file)
                            .pattern(arm.pattern)
                            .span
                            .join(self.ast(env.file).expr(guard).span);
                        guard_env.static_boundary = Some(arm_span);
                    }
                    self.expect(&mut guard_env, guard, &Ty::Bool);
                } else {
                    self.expect(&mut local, guard, &Ty::Bool);
                    self.relate(&mut local, guard, true);
                }
            } else {
                covered.extend(pattern_tags);
                prior.push(shape);
                self.negate_pattern_proofs(&mut remaining_env, arm.pattern, value);
            }
            if check_tail {
                local.checking_fn_tail = true;
            }
            let found = self.expr(&mut local, arm.body, expected);
            if found != Ty::Never {
                merged_dbm = Some(match merged_dbm {
                    None => local.refinements.dbm,
                    Some(cur) => super::dbm::Dbm::join(&cur, &local.refinements.dbm),
                });
            }
            result = self.join(env, span, result, found);
            env.effects_seen.extend(local.effects_seen);
        }
        if let Some(dbm) = merged_dbm {
            env.refinements.dbm = dbm;
        }
        if self.useful(env, &prior, super::coverage::Shape::Any, input)
            && !matches!(input, Ty::Unknown | Ty::Never | Ty::Infer(_))
        {
            self.error(
                Code::E0303,
                span,
                "match does not cover every possible value",
            );
        }
        result
    }

    fn pattern_contains_type(&self, env: &Env, pattern: PatternId) -> bool {
        match &self.ast(env.file).pattern(pattern).value {
            Pattern::Type(_) | Pattern::TypeBinding(_) => true,
            Pattern::Or(items) | Pattern::Tuple(items) | Pattern::Wrap(_, items) => items
                .iter()
                .any(|&item| self.pattern_contains_type(env, item)),
            _ => false,
        }
    }

    pub(super) fn match_domain(&mut self, env: &Env, input: &Ty) -> Option<HashSet<String>> {
        Some(match input {
            Ty::Bool => ["true", "false"].into_iter().map(str::to_owned).collect(),
            Ty::Unit => HashSet::from(["()".into()]),
            Ty::Adt(adt) if matches!(adt.kind, AdtKind::Sum | AdtKind::OpaqueSum) => {
                let def = self.hir.definition(adt.definition);
                if !self.hir.same_package(def.scope, env.scope) &&
                    def.stmt.is_some_and(|item| {
                        matches!(&self.ast(def.name.span.file).stmt(item).value.kind, StmtKind::Type(decl)
                            if matches!(&decl.definition, TypeDefinition::Sum(variants)
                                if variants.iter().any(|v| matches!(v, Variant::Extensible))))
                    })
                {
                    return None;
                }
                self.sum_variants(adt).into_keys().collect()
            }
            _ => return None,
        })
    }

    fn pattern_tags(
        &mut self,
        env: &Env,
        pattern: PatternId,
        input: &Ty,
    ) -> (bool, HashSet<String>) {
        match &self.ast(env.file).pattern(pattern).value {
            Pattern::Binding(..) | Pattern::Wildcard => (true, HashSet::new()),
            Pattern::Unit => (input == &Ty::Unit, HashSet::from(["()".into()])),
            Pattern::Literal(literal) => (false, HashSet::from([literal.text.clone()])),
            Pattern::Constructor(path, parts)
                if parts
                    .iter()
                    .flatten()
                    .all(|&part| self.irrefutable(env, part)) =>
            {
                let tag = self
                    .resolve(path.span)
                    .map(|id| self.hir.definition(id).name.value.clone())
                    .or_else(|| path.segments.last().map(|s| s.name.value.clone()));
                (
                    false,
                    tag.map_or_else(HashSet::new, |name| HashSet::from([name])),
                )
            }
            Pattern::Wrap(_, parts) if parts.iter().all(|&part| self.irrefutable(env, part)) => {
                (true, HashSet::new())
            }
            Pattern::Tuple(_) | Pattern::Record { .. } if self.irrefutable(env, pattern) => {
                (true, HashSet::new())
            }
            Pattern::Or(items) => {
                let mut all = false;
                let mut tags = HashSet::new();
                for &item in items {
                    let (covers, known) = self.pattern_tags(env, item, input);
                    all |= covers;
                    tags.extend(known);
                }
                (all, tags)
            }
            Pattern::Type(id) => {
                let mut local = env.clone();
                if let Ty::TypeValue(Some(inner)) = input {
                    if matches!(**inner, Ty::Param(_)) && !self.is_pattern_only_type(env, *id) {
                        let key = self
                            .type_expr(&mut local, *id)
                            .display(self.hir)
                            .to_string();
                        (false, HashSet::from([key]))
                    } else {
                        (false, HashSet::new())
                    }
                } else {
                    (false, HashSet::new())
                }
            }
            _ => (false, HashSet::new()),
        }
    }

    fn irrefutable(&self, env: &Env, pattern: PatternId) -> bool {
        match &self.ast(env.file).pattern(pattern).value {
            Pattern::Wildcard | Pattern::Binding(..) | Pattern::Unit => true,
            Pattern::Tuple(items) | Pattern::Wrap(_, items) => {
                items.iter().all(|&item| self.irrefutable(env, item))
            }
            Pattern::Record { fields, .. } => fields
                .iter()
                .all(|field| field.pattern.is_none_or(|p| self.irrefutable(env, p))),
            Pattern::Or(items) => items.iter().any(|&item| self.irrefutable(env, item)),
            _ => false,
        }
    }

    fn refine_type_arm(
        &mut self,
        local: &mut Env,
        pattern: PatternId,
        input: &Ty,
        covered: &HashSet<String>,
    ) {
        let Ty::TypeValue(Some(target)) = input else {
            return;
        };
        let Ty::Param(parameter) = **target else {
            return;
        };
        let ast = self.ast(local.file);
        let facts: Vec<_> = match &ast.pattern(pattern).value {
            Pattern::Type(ty) if !self.is_pattern_only_type(local, *ty) => {
                vec![self.type_expr(local, *ty)]
            }
            Pattern::Type(_) => Vec::new(),
            Pattern::Or(items) => items
                .iter()
                .filter_map(|&item| match ast.pattern(item).value {
                    Pattern::Type(id) if !self.is_pattern_only_type(local, id) => {
                        Some(self.type_expr(local, id))
                    }
                    _ => None,
                })
                .collect(),
            _ => local
                .domains
                .get(&parameter)
                .into_iter()
                .flatten()
                .filter(|ty| !covered.contains(&ty.display(self.hir).to_string()))
                .cloned()
                .collect(),
        };
        if let [ty] = facts.as_slice() {
            if !matches!(ty, Ty::Unknown | Ty::Param(_)) {
                local
                    .generics
                    .insert(parameter, GenericValue::Type(ty.clone()));
            }
        } else if !facts.is_empty() {
            local.domains.insert(parameter, facts);
        }
    }

    pub(super) fn is_pattern_only_type(&self, env: &Env, id: TypeId) -> bool {
        use ril_syntax::syntax::GenericArg;
        match &self.ast(env.file).ty(id).value {
            Type::TupleAny
            | Type::PatternBinding(_)
            | Type::PatternWildcard
            | Type::PatternLiteral(_) => true,
            Type::Option(inner) => self.is_pattern_only_type(env, *inner),
            Type::Result(ok, err) => {
                self.is_pattern_only_type(env, *ok) || self.is_pattern_only_type(env, *err)
            }
            Type::Array(storage, item) => {
                storage.bind_mode || self.is_pattern_only_type(env, *item)
            }
            Type::Map(key, storage, val) => {
                storage.bind_mode
                    || self.is_pattern_only_type(env, *key)
                    || self.is_pattern_only_type(env, *val)
            }
            Type::Tuple(items) => items
                .iter()
                .any(|(storage, item)| storage.bind_mode || self.is_pattern_only_type(env, *item)),
            Type::Record { fields, tail } => {
                tail.is_some()
                    || fields.iter().any(|field| {
                        field.storage.bind_mode || self.is_pattern_only_type(env, field.ty)
                    })
            }
            Type::Named(path) => {
                if let Some(def_id) = self.resolve(path.span)
                    && matches!(
                        self.hir.definition(def_id).kind,
                        ril_hir::DefinitionKind::Primitive(_)
                    )
                    && matches!(
                        self.hir.definition(def_id).name.value.as_str(),
                        "Nominal" | "KeyOf"
                    )
                {
                    return true;
                }
                path.segments.last().is_some_and(|seg| {
                    seg.arguments.iter().any(|arg| match arg {
                        GenericArg::Type(ty) => self.is_pattern_only_type(env, *ty),
                        GenericArg::Mode(storage) => storage.bind_mode,
                        GenericArg::Value(_) => false,
                    })
                })
            }
            _ => false,
        }
    }

    pub(super) fn type_pattern_shape_key(&mut self, env: &Env, id: TypeId) -> String {
        use ril_syntax::syntax::{FieldTail, GenericArg};
        if !self.is_pattern_only_type(env, id) {
            return self
                .type_expr(&mut env.clone(), id)
                .display(self.hir)
                .to_string();
        }
        let format_storage = |storage: &ril_syntax::syntax::Storage| -> String {
            if storage.bind_mode {
                "_".into()
            } else {
                let mut out = String::new();
                if storage.variable {
                    out.push_str("var ");
                }
                match storage.mode {
                    Mode::Plain => {}
                    Mode::Ref => out.push_str("ref"),
                    Mode::Mut => out.push_str("mut"),
                    Mode::Shared => out.push_str("^mut"),
                    Mode::New => out.push_str("new"),
                    Mode::Via => out.push_str("via"),
                    Mode::Infer => out.push_str("infer"),
                }
                out.trim().to_owned()
            }
        };
        match &self.ast(env.file).ty(id).value {
            Type::PatternWildcard | Type::PatternBinding(_) => "_".into(),
            Type::PatternLiteral(lit) => lit.text.clone(),
            Type::Unit => "()".into(),
            Type::TupleAny => "(..)".into(),
            Type::Option(inner) => format!("?{}", self.type_pattern_shape_key(env, *inner)),
            Type::Result(ok, err) => format!(
                "!<{}, {}>",
                self.type_pattern_shape_key(env, *ok),
                self.type_pattern_shape_key(env, *err)
            ),
            Type::Array(storage, item) => format!(
                "[{}]{}",
                format_storage(storage),
                self.type_pattern_shape_key(env, *item)
            ),
            Type::Map(key, storage, val) => format!(
                "[{}: {} {}]",
                self.type_pattern_shape_key(env, *key),
                format_storage(storage),
                self.type_pattern_shape_key(env, *val)
            ),
            Type::Tuple(items) => {
                let parts: Vec<_> = items
                    .iter()
                    .map(|(_, item)| self.type_pattern_shape_key(env, *item))
                    .collect();
                format!("({})", parts.join(", "))
            }
            Type::Record { fields, tail } => {
                let mut parts: Vec<_> = fields
                    .iter()
                    .map(|field| {
                        let m = format_storage(&field.storage);
                        let t = self.type_pattern_shape_key(env, field.ty);
                        if m.is_empty() {
                            format!("{}: {t}", field.name.value)
                        } else {
                            format!("{m} {}: {t}", field.name.value)
                        }
                    })
                    .collect();
                parts.sort();
                if matches!(tail, Some(FieldTail::Open | FieldTail::Named(_))) {
                    parts.push("..".into());
                }
                format!(".{{ {} }}", parts.join(", "))
            }
            Type::Named(path) => {
                let name = self
                    .resolve(path.span)
                    .map(|def_id| self.hir.definition(def_id).name.value.clone())
                    .or_else(|| path.segments.last().map(|s| s.name.value.clone()))
                    .unwrap_or_default();
                let args = path
                    .segments
                    .last()
                    .map_or(&[][..], |seg| seg.arguments.as_slice());
                if args.is_empty() {
                    name
                } else {
                    let rendered: Vec<_> = args
                        .iter()
                        .map(|arg| match arg {
                            GenericArg::Type(ty) => self.type_pattern_shape_key(env, *ty),
                            GenericArg::Mode(storage) => format_storage(storage),
                            GenericArg::Value(expr) => {
                                format!("val:{}", self.ast(env.file).expr(*expr).span.start)
                            }
                        })
                        .collect();
                    format!("{name}<{}>", rendered.join(", "))
                }
            }
            _ => "_".into(),
        }
    }

    fn check_type_pattern_syntax(&mut self, env: &mut Env, id: TypeId) {
        use ril_syntax::syntax::GenericArg;
        let node = self.ast(env.file).ty(id);
        match &node.value {
            Type::Option(inner) => self.check_type_pattern_syntax(env, *inner),
            Type::Result(ok, err) => {
                self.check_type_pattern_syntax(env, *ok);
                self.check_type_pattern_syntax(env, *err);
            }
            Type::Array(_, item) => self.check_type_pattern_syntax(env, *item),
            Type::Map(key, _, val) => {
                self.check_type_pattern_syntax(env, *key);
                self.check_type_pattern_syntax(env, *val);
            }
            Type::Tuple(items) => {
                for &(_, item) in items {
                    self.check_type_pattern_syntax(env, item);
                }
            }
            Type::Record { fields, .. } => {
                for field in fields {
                    self.check_type_pattern_syntax(env, field.ty);
                }
            }
            Type::Named(path) => {
                let args = path
                    .segments
                    .last()
                    .map_or(&[][..], |seg| seg.arguments.as_slice());
                if let Some(def_id) = self.resolve(path.span)
                    && matches!(
                        self.hir.definition(def_id).kind,
                        ril_hir::DefinitionKind::Primitive(_)
                    )
                    && self.hir.definition(def_id).name.value == "Nominal"
                    && !matches!(args, [GenericArg::Type(_)])
                {
                    self.error(
                        Code::E0340,
                        path.span,
                        "Nominal pattern requires exactly one type argument",
                    );
                }
                for arg in args {
                    if let GenericArg::Type(ty) = arg {
                        self.check_type_pattern_syntax(env, *ty);
                    }
                }
            }
            _ => {}
        }
    }

    fn match_member_mode(
        &mut self,
        env: &mut Env,
        storage: &ril_syntax::syntax::Storage,
        actual: crate::ty::MemberMode,
    ) -> bool {
        if storage.bind_mode {
            if let Some(path) = &storage.mode_path
                && let Some(id) = self.resolve(path.span)
            {
                env.generics.insert(id, GenericValue::Mode(actual));
            }
            return true;
        }
        let expected = self.member_mode(env, storage);
        expected == actual
    }

    pub(super) fn match_type_pattern(
        &mut self,
        env: &mut Env,
        pattern: TypeId,
        target: &Ty,
    ) -> bool {
        self.match_type_pattern_inner(env, pattern, target, false)
            .unwrap_or(true)
    }

    fn match_type_pattern_eval(
        &mut self,
        env: &mut Env,
        pattern: TypeId,
        target: &Ty,
    ) -> super::eval::Eval<bool> {
        self.match_type_pattern_inner(env, pattern, target, true)
    }

    fn match_type_pattern_inner(
        &mut self,
        env: &mut Env,
        pattern: TypeId,
        target: &Ty,
        strict_eval: bool,
    ) -> super::eval::Eval<bool> {
        use ril_hir::{DefinitionKind, StdType};
        use ril_syntax::syntax::{FieldTail, GenericArg};
        let target = self.normalize(target);
        let pattern_span = self.ast(env.file).ty(pattern).span;
        match (&self.ast(env.file).ty(pattern).value, &target) {
            (Type::PatternWildcard, _) => Ok(true),
            (Type::PatternBinding(name), _) => {
                if let Some(id) = self.resolve(name.span) {
                    env.generics.insert(id, GenericValue::Type(target.clone()));
                }
                Ok(true)
            }
            (_, Ty::Param(_) | Ty::Infer(_) | Ty::Projection(..) | Ty::Unknown) => {
                if strict_eval {
                    Err(super::eval::Signal::Dependent(pattern_span))
                } else {
                    Ok(true)
                }
            }
            (Type::Option(item), target) => match target.as_option(self.hir).cloned() {
                Some(inner) => self.match_type_pattern_inner(env, *item, &inner, strict_eval),
                None => Ok(false),
            },
            (Type::Result(ok, err), target) => {
                match target
                    .as_result(self.hir)
                    .map(|(a, b)| (a.clone(), b.clone()))
                {
                    Some((a, b)) => Ok(self.match_type_pattern_inner(env, *ok, &a, strict_eval)?
                        && self.match_type_pattern_inner(env, *err, &b, strict_eval)?),
                    None => Ok(false),
                }
            }
            (Type::Array(storage, item), Ty::Array(target)) => {
                Ok(self.match_member_mode(env, storage, target.mode)
                    && self.match_type_pattern_inner(env, *item, &target.ty, strict_eval)?)
            }
            (Type::Map(key, storage, val), Ty::Map(tk, tv)) => {
                Ok(self.match_type_pattern_inner(env, *key, tk, strict_eval)?
                    && self.match_member_mode(env, storage, tv.mode)
                    && self.match_type_pattern_inner(env, *val, &tv.ty, strict_eval)?)
            }
            (Type::TupleAny, Ty::Tuple(_)) => Ok(true),
            (Type::Tuple(items), Ty::Tuple(targets)) => {
                if items.len() != targets.len() {
                    return Ok(false);
                }
                for ((_, id), target) in items.iter().zip(targets) {
                    if !self.match_type_pattern_inner(env, *id, &target.ty, strict_eval)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (Type::Record { fields, tail }, Ty::Record(target, open)) => {
                if tail.is_none() && fields.len() != target.len() {
                    return Ok(false);
                }
                let mut matched = HashSet::new();
                for field in fields {
                    let Some(member) = target.get(&field.name.value) else {
                        return Ok(false);
                    };
                    if !self.match_member_mode(env, &field.storage, member.mode)
                        || !self.match_type_pattern_inner(env, field.ty, &member.ty, strict_eval)?
                    {
                        return Ok(false);
                    }
                    matched.insert(field.name.value.as_str());
                }
                if let Some(FieldTail::Named(name)) = tail
                    && let Some(id) = self.resolve(name.span)
                {
                    let rest: std::collections::BTreeMap<_, _> = target
                        .iter()
                        .filter(|(k, _)| !matched.contains(k.as_str()))
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect();
                    env.generics
                        .insert(id, GenericValue::Type(Ty::Record(rest, *open)));
                }
                Ok(true)
            }
            (Type::Named(path), _)
                if self.resolve(path.span).is_some_and(|id| {
                    matches!(self.hir.definition(id).kind, DefinitionKind::Primitive(_))
                        && self.hir.definition(id).name.value == "Nominal"
                }) =>
            {
                let args = path
                    .segments
                    .last()
                    .map_or(&[][..], |s| s.arguments.as_slice());
                let [GenericArg::Type(inner_pat)] = args else {
                    return Ok(false);
                };
                let Ty::Adt(adt) = &target else {
                    return Ok(false);
                };
                let accessible = adt.kind == AdtKind::Nominal
                    || (adt.kind == AdtKind::Opaque && adt.defining_scope == env.effective_scope());
                if !accessible {
                    return Ok(false);
                }
                let Some(rep) = self.representation(env, adt) else {
                    return Ok(false);
                };
                self.match_type_pattern_inner(env, *inner_pat, &rep, strict_eval)
            }
            (Type::Named(path), _)
                if path
                    .segments
                    .last()
                    .is_some_and(|seg| !seg.arguments.is_empty()) =>
            {
                let Some(id) = self.resolve(path.span) else {
                    return Ok(false);
                };
                let args = path
                    .segments
                    .last()
                    .map_or(&[][..], |s| s.arguments.as_slice());
                if let Some(std_ty) = self.hir.std_type(id)
                    && std_ty == StdType::Derived
                {
                    return match (args, &target) {
                        ([GenericArg::Type(p)], Ty::Draft(t)) => {
                            self.match_type_pattern_inner(env, *p, t, strict_eval)
                        }
                        _ => Ok(false),
                    };
                }
                if matches!(self.hir.definition(id).kind, DefinitionKind::Primitive(_))
                    && self.hir.definition(id).name.value == "Type"
                {
                    return match (args, &target) {
                        ([GenericArg::Type(p)], Ty::TypeValue(Some(t))) => {
                            self.match_type_pattern_inner(env, *p, t, strict_eval)
                        }
                        _ => Ok(false),
                    };
                }
                let Ty::Adt(adt) = &target else {
                    return Ok(false);
                };
                if adt.definition != id || args.len() != adt.arguments.len() {
                    return Ok(false);
                }
                for (pat_arg, target_arg) in args.iter().zip(&adt.arguments) {
                    let ok = match (pat_arg, target_arg) {
                        (GenericArg::Type(pat_ty), GenericValue::Type(target_ty)) => {
                            self.match_type_pattern_inner(env, *pat_ty, target_ty, strict_eval)?
                        }
                        (GenericArg::Type(pat_ty), GenericValue::Data(target_val)) => {
                            match &self.ast(env.file).ty(*pat_ty).value {
                                Type::PatternWildcard => true,
                                Type::PatternBinding(name) => {
                                    if let Some(bid) = self.resolve(name.span) {
                                        env.generics
                                            .insert(bid, GenericValue::Data(target_val.clone()));
                                    }
                                    true
                                }
                                Type::PatternLiteral(lit) => literal(lit)
                                    .is_ok_and(|v| super::value::ieee_equal(&v, target_val)),
                                _ => false,
                            }
                        }
                        (GenericArg::Type(pat_ty), GenericValue::Mode(target_mode)) => {
                            match &self.ast(env.file).ty(*pat_ty).value {
                                Type::PatternWildcard => true,
                                Type::PatternBinding(name) => {
                                    if let Some(bid) = self.resolve(name.span) {
                                        env.generics.insert(bid, GenericValue::Mode(*target_mode));
                                    }
                                    true
                                }
                                _ => false,
                            }
                        }
                        (GenericArg::Mode(storage), GenericValue::Mode(target_mode)) => {
                            self.match_member_mode(env, storage, *target_mode)
                        }
                        (GenericArg::Value(expr), GenericValue::Data(target_val)) => self
                            .eval_root(env, *expr, false)
                            .is_some_and(|v| super::value::ieee_equal(&v, target_val)),
                        _ => false,
                    };
                    if !ok {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(self.type_expr(env, pattern) == target),
        }
    }

    pub(super) fn map_static_bindings(&mut self, env: &mut Env, pattern: PatternId, value: &Value) {
        let mut bindings = HashMap::new();
        if self
            .value_pattern(env, pattern, value, &mut bindings)
            .unwrap_or(false)
        {
            for (def, value) in bindings {
                env.generics.insert(def, GenericValue::Data(value));
            }
        }
    }

    pub(super) fn value_pattern(
        &mut self,
        env: &mut Env,
        pattern: PatternId,
        value: &Value,
        bindings: &mut HashMap<DefinitionId, Value>,
    ) -> super::eval::Eval<bool> {
        let mut matched = MatchedValues {
            locals: std::mem::take(bindings),
            paths: HashMap::new(),
        };
        let result = self.value_pattern_at(env, pattern, value, &mut matched, None);
        *bindings = matched.locals;
        result
    }

    pub(super) fn value_pattern_at(
        &mut self,
        env: &mut Env,
        pattern: PatternId,
        value: &Value,
        bindings: &mut MatchedValues,
        place: Option<&[Value]>,
    ) -> super::eval::Eval<bool> {
        let ast = self.ast(env.file);
        let node = ast.pattern(pattern);
        match (&node.value, value) {
            (Pattern::Wildcard | Pattern::Rest(None), _) => Ok(true),
            (Pattern::Binding(storage, name), value) => {
                if let Some(id) = self.resolve(name.span) {
                    bindings.bind(id, value, place, storage.mode);
                }
                Ok(true)
            }
            (Pattern::Rest(Some(name)), value) => {
                if let Some(id) = self.resolve(name.span) {
                    bindings.bind(id, value, None, Mode::Plain);
                }
                Ok(true)
            }
            (Pattern::Unit, Value::Unit) => Ok(true),
            (Pattern::Literal(pattern), value) => {
                Ok(literal(pattern).is_ok_and(|pattern| super::value::ieee_equal(&pattern, value)))
            }
            (Pattern::Tuple(items), Value::Tuple(values)) => {
                if items.len() != values.len() {
                    return Ok(false);
                }
                for (index, (&id, value)) in items.iter().zip(values).enumerate() {
                    let child = next_coordinate(place, || Value::Int(index.into()));
                    if !self.value_pattern_at(env, id, value, bindings, child.as_deref())? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (
                Pattern::Slice {
                    text: false,
                    elements,
                },
                Value::Array(values),
            ) => {
                let (before, rest, after) = ast.slice_parts(elements);
                let Some(end) = values.len().checked_sub(after.len()) else {
                    return Ok(false);
                };
                let Some(middle) = values.get(before.len()..end) else {
                    return Ok(false);
                };
                if rest.is_none() && !middle.is_empty() {
                    return Ok(false);
                }
                for (id, index) in before
                    .iter()
                    .copied()
                    .zip(0..before.len())
                    .chain(after.iter().copied().zip(end..values.len()))
                {
                    let child = next_coordinate(place, || Value::Int(index.into()));
                    let Some(value) = values.get(index) else {
                        return Ok(false);
                    };
                    if !self.value_pattern_at(env, id, value, bindings, child.as_deref())? {
                        return Ok(false);
                    }
                }
                if let Some(id) = rest {
                    return self.value_pattern_at(
                        env,
                        id,
                        &Value::Array(middle.to_vec()),
                        bindings,
                        None,
                    );
                }
                Ok(true)
            }
            (
                Pattern::Slice {
                    text: true,
                    elements,
                },
                Value::Str(text),
            ) => {
                let (before, rest, after) = ast.slice_parts(elements);
                let Some(prefix) = text_slice_fragment(ast, before) else {
                    return Ok(false);
                };
                let Some(suffix) = text_slice_fragment(ast, after) else {
                    return Ok(false);
                };
                let Some(middle) = text
                    .strip_prefix(&prefix)
                    .and_then(|tail| tail.strip_suffix(&suffix))
                else {
                    return Ok(false);
                };
                match rest {
                    None => Ok(middle.is_empty()),
                    Some(id) => {
                        self.value_pattern_at(env, id, &Value::Str(middle.into()), bindings, None)
                    }
                }
            }
            (Pattern::Wrap(_, parts), value) => match parts.as_slice() {
                [] => Ok(matches!(value, Value::Unit)),
                [inner] => self.value_pattern_at(env, *inner, value, bindings, place),
                many => {
                    let Value::Tuple(values) = value else {
                        return Ok(false);
                    };
                    if many.len() != values.len() {
                        return Ok(false);
                    }
                    for (index, (&id, value)) in many.iter().zip(values).enumerate() {
                        let child = next_coordinate(place, || Value::Int(index.into()));
                        if !self.value_pattern_at(env, id, value, bindings, child.as_deref())? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
            },
            (Pattern::Constructor(path, None), Value::Unit)
                if self
                    .resolve(path.span)
                    .is_some_and(|id| self.hir.unit_constructor(id)) =>
            {
                Ok(true)
            }
            (Pattern::Constructor(path, parts), Value::Tag(tag, values)) => {
                let expected = self
                    .resolve(path.span)
                    .map(|id| self.hir.definition(id).name.value.as_str())
                    .or_else(|| {
                        path.segments
                            .last()
                            .map(|segment| segment.name.value.as_str())
                    });
                if expected != Some(tag.as_str())
                    || parts.as_ref().map_or(0, Vec::len) != values.len()
                {
                    return Ok(false);
                }
                for (index, (&id, value)) in parts.iter().flatten().zip(values).enumerate() {
                    let child = next_coordinate(place, || Value::Int(index.into()));
                    if !self.value_pattern_at(env, id, value, bindings, child.as_deref())? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (Pattern::Subset { binding, .. }, Value::Tag(tag, _)) => {
                if !self
                    .subset_tags
                    .get(&node.span)
                    .is_some_and(|tags| tags.contains(tag))
                {
                    return Ok(false);
                }
                match binding {
                    Some(id) => self.value_pattern_at(env, *id, value, bindings, place),
                    None => Ok(true),
                }
            }
            (Pattern::Or(items), value) => {
                for &id in items {
                    let mut local_bindings = bindings.clone();
                    let mut local_env = env.clone();
                    if self.value_pattern_at(
                        &mut local_env,
                        id,
                        value,
                        &mut local_bindings,
                        place,
                    )? {
                        *bindings = local_bindings;
                        *env = local_env;
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            (Pattern::Record { fields, .. }, Value::Record(record)) => {
                for field in fields {
                    let Some(value) = record.get(&field.name.value) else {
                        return Ok(false);
                    };
                    let child = next_coordinate(place, || Value::Str(field.name.value.clone()));
                    if let Some(id) = field.pattern {
                        if !self.value_pattern_at(env, id, value, bindings, child.as_deref())? {
                            return Ok(false);
                        }
                    } else if let Some(id) = self.resolve(field.name.span) {
                        bindings.bind(id, value, child.as_deref(), field.storage.mode);
                    }
                }
                Ok(true)
            }
            (
                Pattern::Range {
                    low,
                    high,
                    inclusive,
                },
                Value::Int(value),
            ) => Ok(match (literal(low), literal(high)) {
                (Ok(Value::Int(a)), Ok(Value::Int(b))) => {
                    &a <= value && (value < &b || *inclusive && value == &b)
                }
                _ => false,
            }),
            (Pattern::Type(pattern), Value::Type(ty)) => {
                self.match_type_pattern_eval(env, *pattern, ty)
            }
            _ => Ok(false),
        }
    }
}
