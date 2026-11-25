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
                let name = path
                    .segments
                    .last()
                    .map_or("", |part| part.name.value.as_str());
                let resolved_ctor = self.resolve(path.span);
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
            Pattern::Record { name, fields, rest } => {
                if let Some(path) = name
                    && let Some(expected_id) = self.resolve(path.span)
                    && !matches!(normalized, Ty::Unknown | Ty::Infer(_))
                {
                    let def = self.hir.definition(expected_id);
                    let is_alias = def.stmt.is_some_and(|stmt| {
                        matches!(
                            &self.ast(def.name.span.file).stmt(stmt).value.kind,
                            StmtKind::Type(decl) if decl.kind == ril_syntax::syntax::TypeKind::Alias
                        )
                    });
                    if !is_alias {
                        let matches_id =
                            matches!(&normalized, Ty::Adt(adt) if adt.definition == expected_id);
                        if !matches_id {
                            self.error(
                                Code::E0301,
                                node.span,
                                "record pattern type does not match the matched value",
                            );
                        }
                    }
                }
                let ty = if let Ty::Adt(adt) = &normalized {
                    match adt.kind {
                        AdtKind::Foreign => {
                            self.error(
                                Code::E0907,
                                node.span,
                                "foreign representation cannot be matched",
                            );
                            Ty::Unknown
                        }
                        AdtKind::Opaque if adt.defining_scope != env.scope => {
                            self.error(Code::E0308, node.span, "opaque representation is sealed");
                            Ty::Unknown
                        }
                        _ => self.representation(env, adt).unwrap_or(Ty::Unknown),
                    }
                } else {
                    normalized
                };
                if let Ty::Record(known, open) = ty {
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
                } else if ty != Ty::Unknown {
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
            ("Some", Ty::Option(inner))
                if variant_parent
                    .is_none_or(|p| self.hir.std_type(p) == Some(ril_hir::StdType::Option)) =>
            {
                vec![(**inner).clone()]
            }
            ("Ok", Ty::Result(inner, _))
                if variant_parent
                    .is_none_or(|p| self.hir.std_type(p) == Some(ril_hir::StdType::Result)) =>
            {
                vec![(**inner).clone()]
            }
            ("Err", Ty::Result(_, inner))
                if variant_parent
                    .is_none_or(|p| self.hir.std_type(p) == Some(ril_hir::StdType::Result)) =>
            {
                vec![(**inner).clone()]
            }
            ("None", Ty::Option(_))
                if variant_parent
                    .is_none_or(|p| self.hir.std_type(p) == Some(ril_hir::StdType::Option)) =>
            {
                Vec::new()
            }
            (
                "Let" | "Var" | "Mut" | "SharedMut" | "Ref" | "VarMut" | "VarSharedMut" | "VarRef",
                Ty::Mode,
            ) if variant_parent
                .is_none_or(|p| self.hir.std_type(p) == Some(ril_hir::StdType::MemberMode)) =>
            {
                Vec::new()
            }
            (_, Ty::Adt(adt)) if adt.kind == AdtKind::Foreign => {
                self.error(
                    Code::E0907,
                    span,
                    "foreign representation cannot be matched",
                );
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
                    let parent_adt = Ty::Adt(std::sync::Arc::new(super::Adt {
                        definition: parent,
                        kind: AdtKind::Sum,
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
                match self.representation(env, adt) {
                    Some(Ty::Tuple(items)) => items.into_iter().map(|m| m.ty).collect(),
                    Some(Ty::Unit) | None => Vec::new(),
                    Some(inner) => vec![inner],
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

    pub(super) fn check_match(
        &mut self,
        env: &mut Env,
        arms: &[MatchArm],
        (value, input): (ExprId, &Ty),
        expected: Option<&Ty>,
        span: Span,
    ) -> Ty {
        let mut prior = Vec::new();
        let mut covered = HashSet::new();
        let mut result = Ty::Never;
        let staged = self.stage_match(env, span, value, arms);
        for (index, arm) in arms.iter().enumerate() {
            let mut local = env.clone();
            if staged {
                local.staging_gates.push(super::staging::StaticGate::Match {
                    span,
                    expected: index,
                });
            }
            self.pattern(&mut local, arm.pattern, input);
            self.refine_type_arm(&mut local, arm.pattern, input, &covered);
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
                self.expect(&mut local, guard, &Ty::Bool);
            } else {
                covered.extend(pattern_tags);
                prior.push(shape);
            }
            let found = self.expr(&mut local, arm.body, expected);
            result = self.join(env, span, result, found);
            env.effects_seen.extend(local.effects_seen);
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

    pub(super) fn match_domain(&mut self, env: &Env, input: &Ty) -> Option<HashSet<String>> {
        Some(match input {
            Ty::Bool => ["true", "false"].into_iter().map(str::to_owned).collect(),
            Ty::Option(_) => ["Some", "None"].into_iter().map(str::to_owned).collect(),
            Ty::Result(..) => ["Ok", "Err"].into_iter().map(str::to_owned).collect(),
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
                (
                    false,
                    path.segments
                        .last()
                        .map(|segment| HashSet::from([segment.name.value.clone()]))
                        .unwrap_or_default(),
                )
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
                    if matches!(**inner, Ty::Param(_)) {
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
            Pattern::Tuple(items) => items.iter().all(|&item| self.irrefutable(env, item)),
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
            Pattern::Type(ty) => vec![self.type_expr(local, *ty)],
            Pattern::Or(items) => items
                .iter()
                .filter_map(|&item| match ast.pattern(item).value {
                    Pattern::Type(id) => Some(self.type_expr(local, id)),
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
        use ril_hir::StdType;
        use ril_syntax::syntax::{FieldTail, GenericArg};
        let target = self.normalize(target);
        match (&self.ast(env.file).ty(pattern).value, &target) {
            (Type::PatternWildcard, _) => true,
            (Type::PatternBinding(name), _) => {
                if let Some(id) = self.resolve(name.span) {
                    env.generics.insert(id, GenericValue::Type(target.clone()));
                }
                true
            }
            (_, Ty::Param(_) | Ty::Unknown) => true,
            (Type::Option(item), Ty::Option(target)) => self.match_type_pattern(env, *item, target),
            (Type::Result(ok, err), Ty::Result(a, b)) => {
                self.match_type_pattern(env, *ok, a) && self.match_type_pattern(env, *err, b)
            }
            (Type::Array(storage, item), Ty::Array(target)) => {
                self.match_member_mode(env, storage, target.mode)
                    && self.match_type_pattern(env, *item, &target.ty)
            }
            (Type::Map(key, storage, val), Ty::Map(tk, tv)) => {
                self.match_type_pattern(env, *key, tk)
                    && self.match_member_mode(env, storage, tv.mode)
                    && self.match_type_pattern(env, *val, &tv.ty)
            }
            (Type::Tuple(items), Ty::Tuple(targets)) => {
                items.len() == targets.len()
                    && items
                        .iter()
                        .zip(targets)
                        .all(|((_, id), target)| self.match_type_pattern(env, *id, &target.ty))
            }
            (Type::Record { fields, tail }, Ty::Record(target, open)) => {
                if tail.is_none() && fields.len() != target.len() {
                    return false;
                }
                let mut matched = HashSet::new();
                for field in fields {
                    let Some(member) = target.get(&field.name.value) else {
                        return false;
                    };
                    if !self.match_member_mode(env, &field.storage, member.mode)
                        || !self.match_type_pattern(env, field.ty, &member.ty)
                    {
                        return false;
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
                true
            }
            (Type::Named(path), _)
                if path
                    .segments
                    .last()
                    .is_some_and(|seg| !seg.arguments.is_empty()) =>
            {
                let Some(id) = self.resolve(path.span) else {
                    return false;
                };
                let args = path
                    .segments
                    .last()
                    .map_or(&[][..], |s| s.arguments.as_slice());
                if let Some(std_ty) = self.hir.std_type(id) {
                    return match (std_ty, args, &target) {
                        (StdType::Set, [GenericArg::Type(p)], Ty::Set(t))
                        | (StdType::Option, [GenericArg::Type(p)], Ty::Option(t))
                        | (StdType::Draft, [GenericArg::Type(p)], Ty::Draft(t))
                        | (StdType::Task, [GenericArg::Type(p)], Ty::Task(t))
                        | (StdType::Sender, [GenericArg::Type(p)], Ty::Sender(t))
                        | (StdType::Receiver, [GenericArg::Type(p)], Ty::Receiver(t)) => {
                            self.match_type_pattern(env, *p, t)
                        }
                        (
                            StdType::Result,
                            [GenericArg::Type(pa), GenericArg::Type(pb)],
                            Ty::Result(ta, tb),
                        ) => {
                            self.match_type_pattern(env, *pa, ta)
                                && self.match_type_pattern(env, *pb, tb)
                        }
                        _ => false,
                    };
                }
                let Ty::Adt(adt) = &target else {
                    return false;
                };
                if adt.definition != id || args.len() != adt.arguments.len() {
                    return false;
                }
                for (pat_arg, target_arg) in args.iter().zip(&adt.arguments) {
                    let ok = match (pat_arg, target_arg) {
                        (GenericArg::Type(pat_ty), GenericValue::Type(target_ty)) => {
                            self.match_type_pattern(env, *pat_ty, target_ty)
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
                        return false;
                    }
                }
                true
            }
            _ => self.type_expr(env, pattern) == target,
        }
    }

    pub(super) fn map_static_bindings(&mut self, env: &mut Env, pattern: PatternId, value: &Value) {
        let mut bindings = HashMap::new();
        if self.value_pattern(env, pattern, value, &mut bindings) {
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
    ) -> bool {
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
    ) -> bool {
        let ast = self.ast(env.file);
        let node = ast.pattern(pattern);
        match (&node.value, value) {
            (Pattern::Wildcard | Pattern::Rest(None), _) => true,
            (Pattern::Binding(storage, name), value) => {
                if let Some(id) = self.resolve(name.span) {
                    bindings.bind(id, value, place, storage.mode);
                }
                true
            }
            (Pattern::Rest(Some(name)), value) => {
                if let Some(id) = self.resolve(name.span) {
                    bindings.bind(id, value, None, Mode::Plain);
                }
                true
            }
            (Pattern::Unit, Value::Unit) => true,
            (Pattern::Literal(pattern), value) => {
                literal(pattern).is_ok_and(|pattern| super::value::ieee_equal(&pattern, value))
            }
            (Pattern::Tuple(items), Value::Tuple(values)) => {
                items.len() == values.len()
                    && items
                        .iter()
                        .zip(values)
                        .enumerate()
                        .all(|(index, (&id, value))| {
                            let child = next_coordinate(place, || Value::Int(index.into()));
                            self.value_pattern_at(env, id, value, bindings, child.as_deref())
                        })
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
                    return false;
                };
                let Some(middle) = values.get(before.len()..end) else {
                    return false;
                };
                if rest.is_none() && !middle.is_empty() {
                    return false;
                }
                before
                    .iter()
                    .copied()
                    .zip(0..before.len())
                    .chain(after.iter().copied().zip(end..values.len()))
                    .all(|(id, index)| {
                        let child = next_coordinate(place, || Value::Int(index.into()));
                        values.get(index).is_some_and(|value| {
                            self.value_pattern_at(env, id, value, bindings, child.as_deref())
                        })
                    })
                    && rest.is_none_or(|id| {
                        self.value_pattern_at(
                            env,
                            id,
                            &Value::Array(middle.to_vec()),
                            bindings,
                            None,
                        )
                    })
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
                    return false;
                };
                let Some(suffix) = text_slice_fragment(ast, after) else {
                    return false;
                };
                let Some(middle) = text
                    .strip_prefix(&prefix)
                    .and_then(|tail| tail.strip_suffix(&suffix))
                else {
                    return false;
                };
                rest.map_or_else(
                    || middle.is_empty(),
                    |id| self.value_pattern_at(env, id, &Value::Str(middle.into()), bindings, None),
                )
            }
            (Pattern::Constructor(path, parts), Value::Tag(tag, values)) => {
                path.segments
                    .last()
                    .is_some_and(|segment| segment.name.value == *tag)
                    && parts.as_ref().map_or(0, Vec::len) == values.len()
                    && parts.iter().flatten().zip(values).enumerate().all(
                        |(index, (&id, value))| {
                            let child = next_coordinate(place, || Value::Int(index.into()));
                            self.value_pattern_at(env, id, value, bindings, child.as_deref())
                        },
                    )
            }
            (Pattern::Subset { binding, .. }, Value::Tag(tag, _)) => {
                self.subset_tags
                    .get(&node.span)
                    .is_some_and(|tags| tags.contains(tag))
                    && binding
                        .is_none_or(|id| self.value_pattern_at(env, id, value, bindings, place))
            }
            (Pattern::Or(items), value) => items.iter().any(|&id| {
                let mut local_bindings = bindings.clone();
                let mut local_env = env.clone();
                if self.value_pattern_at(&mut local_env, id, value, &mut local_bindings, place) {
                    *bindings = local_bindings;
                    *env = local_env;
                    true
                } else {
                    false
                }
            }),
            (Pattern::Record { fields, .. }, Value::Record(record)) => fields.iter().all(|field| {
                record.get(&field.name.value).is_some_and(|value| {
                    let child = next_coordinate(place, || Value::Str(field.name.value.clone()));
                    if let Some(id) = field.pattern {
                        self.value_pattern_at(env, id, value, bindings, child.as_deref())
                    } else {
                        if let Some(id) = self.resolve(field.name.span) {
                            bindings.bind(id, value, child.as_deref(), field.storage.mode);
                        }
                        true
                    }
                })
            }),
            (
                Pattern::Range {
                    low,
                    high,
                    inclusive,
                },
                Value::Int(value),
            ) => match (literal(low), literal(high)) {
                (Ok(Value::Int(a)), Ok(Value::Int(b))) => {
                    &a <= value && (value < &b || *inclusive && value == &b)
                }
                _ => false,
            },
            (Pattern::Type(pattern), Value::Type(ty)) => self.match_type_pattern(env, *pattern, ty),
            _ => false,
        }
    }
}
