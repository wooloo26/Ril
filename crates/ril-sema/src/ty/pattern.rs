use std::collections::{HashMap, HashSet};

use ril_base::{diag::Code, span::Span};
use ril_frontend::syntax::{
    LiteralKind, MatchArm, Pattern, PatternId, StmtKind, Type, TypeDefinition, TypeId, Variant,
};

use super::{
    AdtKind, GenericValue, Member, Ty, Value,
    check::{Checker, Env},
    literal,
};

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
                let mut domain = None;
                for &item in items {
                    let names = self.pattern_names(env, item);
                    if domain.as_ref().is_some_and(|expected| expected != &names) {
                        self.error(
                            Code::E0346,
                            ast.pattern(item).span,
                            "alternative patterns must bind the same names",
                        );
                    }
                    domain = Some(names);
                    self.pattern(env, item, input);
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
                                Code::E0551,
                                ast.pattern(item).span,
                                "only one rest element is allowed",
                            );
                        }
                        rest = true;
                        self.pattern(env, item, &normalized);
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
                let payload = self.pattern_payload(env, name, &normalized, node.span);
                let unit_payload = name == "Ok"
                    && payload.as_slice() == [Ty::Unit]
                    && items.as_ref().is_some_and(Vec::is_empty);
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
            Pattern::Record { fields, rest, .. } => {
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
                    if !rest && !open && fields.len() != known.len() {
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

    fn pattern_payload(&mut self, env: &Env, name: &str, ty: &Ty, span: Span) -> Vec<Ty> {
        match (name, ty) {
            ("Some", Ty::Option(inner))
            | ("Ok", Ty::Result(inner, _))
            | ("Err", Ty::Result(_, inner)) => vec![(**inner).clone()],
            ("None", Ty::Option(_)) => Vec::new(),
            (_, Ty::Adt(adt)) if adt.kind == AdtKind::Foreign => {
                self.error(
                    Code::E0907,
                    span,
                    "foreign representation cannot be matched",
                );
                Vec::new()
            }
            (_, Ty::Adt(adt))
                if adt.kind == AdtKind::OpaqueSum && adt.defining_scope != env.scope =>
            {
                self.error(Code::E0308, span, "opaque sum is sealed");
                Vec::new()
            }
            (_, Ty::Adt(adt)) if matches!(adt.kind, AdtKind::Sum | AdtKind::OpaqueSum) => {
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
            (_, Ty::Adt(adt)) if self.hir.definition(adt.definition).name.value == name => {
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
        input: &Ty,
        expected: Option<&Ty>,
        span: Span,
    ) -> Ty {
        let mut prior = Vec::new();
        let mut covered = HashSet::new();
        let mut result = Ty::Never;
        for arm in arms {
            let mut local = env.clone();
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

    pub(super) fn match_type_pattern(
        &mut self,
        env: &mut Env,
        pattern: TypeId,
        target: &Ty,
    ) -> bool {
        match (&self.ast(env.file).ty(pattern).value, target) {
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
            (Type::Array(_, item), Ty::Array(target)) => {
                self.match_type_pattern(env, *item, &target.ty)
            }
            (Type::Tuple(items), Ty::Tuple(targets)) => {
                items.len() == targets.len()
                    && items
                        .iter()
                        .zip(targets)
                        .all(|((_, id), target)| self.match_type_pattern(env, *id, &target.ty))
            }
            (Type::Record { fields, tail }, Ty::Record(target, _)) => {
                (tail.is_some() || fields.len() == target.len())
                    && fields.iter().all(|field| {
                        target.get(&field.name.value).is_some_and(|member| {
                            self.match_type_pattern(env, field.ty, &member.ty)
                        })
                    })
            }
            _ => self.type_expr(env, pattern) == *target,
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
        bindings: &mut HashMap<ril_frontend::hir::DefinitionId, Value>,
    ) -> bool {
        let ast = self.ast(env.file);
        let node = ast.pattern(pattern);
        match (&node.value, value) {
            (Pattern::Wildcard | Pattern::Rest(None), _) => true,
            (Pattern::Binding(_, name) | Pattern::Rest(Some(name)), value) => {
                if let Some(id) = self.resolve(name.span) {
                    bindings.insert(id, value.clone());
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
                        .all(|(&id, value)| self.value_pattern(env, id, value, bindings))
            }
            (Pattern::Constructor(path, parts), Value::Tag(tag, values)) => {
                path.segments
                    .last()
                    .is_some_and(|segment| segment.name.value == *tag)
                    && parts.as_ref().map_or(0, Vec::len) == values.len()
                    && parts
                        .iter()
                        .flatten()
                        .zip(values)
                        .all(|(&id, value)| self.value_pattern(env, id, value, bindings))
            }
            (Pattern::Subset { binding, .. }, Value::Tag(tag, _)) => {
                self.subset_tags
                    .get(&node.span)
                    .is_some_and(|tags| tags.contains(tag))
                    && binding.is_none_or(|id| self.value_pattern(env, id, value, bindings))
            }
            (Pattern::Or(items), value) => items.iter().any(|&id| {
                let mut local = bindings.clone();
                if self.value_pattern(env, id, value, &mut local) {
                    *bindings = local;
                    true
                } else {
                    false
                }
            }),
            (Pattern::Record { fields, .. }, Value::Record(record)) => fields.iter().all(|field| {
                record.get(&field.name.value).is_some_and(|value| {
                    if let Some(id) = field.pattern {
                        self.value_pattern(env, id, value, bindings)
                    } else {
                        if let Some(id) = self.resolve(field.name.span) {
                            bindings.insert(id, value.clone());
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
