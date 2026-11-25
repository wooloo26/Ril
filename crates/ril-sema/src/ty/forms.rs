mod instantiate;
mod resolve;

use std::collections::HashSet;

use ril_hir::{DefinitionId, DefinitionKind};
use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::{
    self, GenericArg, GenericParam, Member as Coordinate, Mode, StateKind, StmtKind, Type,
    TypeDecl, TypeDefinition, TypeKind, Variant,
};

use super::{
    AdtKind, Callable, GenericValue, Member, Parameter, Ty, Value,
    check::{Checker, Env, Phase, path_name, transform},
};

impl Checker<'_> {
    pub(super) fn nominal_fields(&self, env: &mut Env, declaration: &TypeDecl) {
        if declaration.kind != TypeKind::Alias
            && let TypeDefinition::Data(id) = declaration.definition
        {
            let node = self.ast(env.file).ty(id);
            if matches!(node.value, Type::Record { .. }) {
                env.nominal_fields = Some(node.span);
            }
        }
    }

    pub(super) fn validate_defaults(&mut self, env: &Env, parameters: &[GenericParam]) {
        let mut started = false;
        for (index, parameter) in parameters.iter().enumerate() {
            if let Some(default) = &parameter.default {
                started = true;
                let span = match default {
                    GenericArg::Type(ty) => self.ast(env.file).ty(*ty).span,
                    GenericArg::Value(expr) => self.ast(env.file).expr(*expr).span,
                    GenericArg::Mode(_) => continue,
                };
                let refs: HashSet<_> = self.hir.references_within(span).map(|(_, id)| id).collect();
                if parameters
                    .iter()
                    .skip(index)
                    .filter_map(|param| self.resolve(param.name.span))
                    .any(|id| refs.contains(&id))
                {
                    self.error(
                        Code::E0320,
                        span,
                        "default refers to itself or a subsequent generic parameter",
                    );
                }
            } else if started {
                self.error(
                    Code::E0316,
                    parameter.name.span,
                    "required generic parameter follows a default",
                );
            }
        }
    }

    pub(super) fn check_pure_default(&mut self, env: &Env, expr: syntax::ExprId, expected: &Ty) {
        let mut local = env.clone();
        local.effects_seen.clear();
        self.expect(&mut local, expr, expected);
        if !local.effects_seen.is_empty() {
            self.error(
                Code::E0409,
                self.ast(env.file).expr(expr).span,
                "default must be pure",
            );
        }
    }

    pub(super) fn check_guard(&mut self, env: &Env, guard: syntax::ExprId, output: &Ty) {
        let ast = self.ast(env.file);
        let original = ast.expr(guard);
        let mut node = original;
        if let syntax::Expr::Unary { op, value } = &node.value
            && op.value == "ref"
        {
            node = ast.expr(*value);
        }
        if let syntax::Expr::Call { callee, .. } = node.value {
            node = ast.expr(callee);
        }
        let syntax::Expr::Path(path) = &node.value else {
            return;
        };
        let Some(id) = self.resolve(path.span) else {
            return;
        };
        let signature = self.declare_function(id);
        if signature.open_effects
            || signature.open_state
            || !signature.effects.is_empty()
            || !signature.state.is_empty()
        {
            self.error(Code::E0409, original.span, "signature guard must be pure");
        }
        let compatible = match (&signature.result, output) {
            (Ty::Option(inner), Ty::Option(_)) if inner.as_ref() == &Ty::Unit => true,
            (Ty::Result(ok, err), Ty::Result(_, expected)) if ok.as_ref() == &Ty::Unit => {
                self.fits(env, err, expected) || self.sum_subset(env, err, expected)
            }
            (Ty::Option(inner), _) if inner.as_ref() == &Ty::Unit => false,
            (Ty::Result(ok, _), _) if ok.as_ref() == &Ty::Unit => false,
            (Ty::Unknown, _) => return,
            _ => {
                self.error(
                    Code::E0712,
                    original.span,
                    "signature guard must return fallible unit",
                );
                return;
            }
        };
        if !compatible {
            self.error(
                Code::E0713,
                original.span,
                "signature guard cannot propagate its failure",
            );
        }
    }

    pub(super) fn generic_env(&mut self, env: &mut Env, params: &[GenericParam]) {
        for param in params {
            if let Some(id) = self.resolve(param.name.span) {
                if param.guards.iter().any(|guard| {
                    self.resolve(guard.span).is_some_and(|symbol| {
                        let symbol = self.hir.definition(symbol);
                        matches!(symbol.kind, DefinitionKind::Primitive(_))
                            && symbol.name.value == "Sendable"
                    })
                }) {
                    env.sendable_guards.insert(id);
                }
                if param
                    .name
                    .value
                    .starts_with(|c: char| c.is_ascii_lowercase() || c == '_')
                {
                    let ty = param
                        .bound
                        .first()
                        .map(|&ty| self.type_expr(env, ty))
                        .unwrap_or(Ty::Unknown);
                    self.bindings.insert(id, ty);
                } else if !env.generics.contains_key(&id) {
                    let domain: Vec<_> = param
                        .bound
                        .iter()
                        .map(|&ty| self.type_expr(env, ty))
                        .collect();
                    if !domain.is_empty() {
                        env.domains.insert(id, domain);
                    }
                }
            }
        }
    }

    pub(super) fn callable(
        &mut self,
        env: &mut Env,
        signature: &syntax::Signature,
        named: bool,
    ) -> Callable {
        // Read the complete signature before deciding which mode parameters
        // are in scope for a nested callable type.
        let enclosing = env.mode_scope.take();
        let params: Vec<_> = signature
            .params
            .iter()
            .map(|param| {
                let ty = if let Some(ty) = param.ty {
                    self.type_expr(env, ty)
                } else if let Some(&guard) = param.guards.first() {
                    self.guard_parameter(env, guard)
                } else {
                    if named && let Some(name) = &param.name {
                        self.error(
                            Code::E0544,
                            name.span,
                            "named parameter needs a type or a first guard",
                        );
                    }
                    self.fresh()
                };
                if param.is_meta {
                    self.declare_meta_key(env, param);
                }
                if matches!(param.mode, Mode::Ref | Mode::Mut | Mode::Shared) && ty.is_value() {
                    let span = param.name.as_ref().map_or_else(
                        || self.ast(env.file).ty(signature.result).span,
                        |name| name.span,
                    );
                    self.error(
                        Code::E0401,
                        span,
                        "value-type parameter cannot carry live access",
                    );
                }
                if !named && param.mode == Mode::Via && ty.is_value() {
                    let span = param.ty.map_or_else(
                        || self.ast(env.file).ty(signature.result).span,
                        |ty| self.ast(env.file).ty(ty).span,
                    );
                    self.error(
                        Code::E0550,
                        span,
                        "via is redundant on a value-type parameter",
                    );
                }
                if named
                    && !param.is_meta
                    && env.phase == Phase::Runtime
                    && ty.contains_type_value()
                {
                    let span = param.name.as_ref().map_or_else(
                        || self.ast(env.file).ty(signature.result).span,
                        |name| name.span,
                    );
                    self.error(
                        Code::E0816,
                        span,
                        "runtime parameter cannot contain a type value",
                    );
                }
                if param.default.is_some()
                    && matches!(param.mode, Mode::Mut | Mode::Shared | Mode::New | Mode::Via)
                {
                    let span = param.name.as_ref().map_or_else(
                        || self.ast(env.file).ty(signature.result).span,
                        |name| name.span,
                    );
                    self.error(
                        Code::E0404,
                        span,
                        "a writable, new, or mode-inferred parameter cannot have a default",
                    );
                }
                Parameter {
                    label: param
                        .name
                        .as_ref()
                        .map(|name| name.value.clone())
                        .filter(|name| name != "_"),
                    mode: param.mode,
                    ty,
                    optional: param.default.is_some(),
                    is_meta: param.is_meta,
                }
            })
            .collect();
        let result = self.type_expr(env, signature.result);
        env.mode_scope = enclosing;
        let effects = signature
            .obligations
            .effects
            .iter()
            .map(|path| self.effect_label(env, path))
            .collect();
        let state = signature
            .obligations
            .state
            .iter()
            .map(|clause| {
                let name = match clause.kind {
                    StateKind::Write => "mut",
                    StateKind::Share => "^mut",
                    StateKind::Capture => "capture",
                    StateKind::Environment => "up",
                    StateKind::Return => "return",
                };
                if clause.bindings.is_empty() {
                    name.into()
                } else {
                    let bindings = clause
                        .bindings
                        .iter()
                        .map(|(storage, path)| {
                            let mode = super::mode_name(self.member_mode(env, storage));
                            let name = path_name(path);
                            if mode.is_empty() {
                                name
                            } else if name.is_empty() {
                                mode.into()
                            } else {
                                format!("{mode} {name}")
                            }
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{name}({bindings})")
                }
            })
            .collect();
        let callable = Callable {
            parameters: params,
            result,
            result_mode: signature.result_mode,
            effects,
            open_effects: signature.obligations.open_effects,
            state,
            open_state: signature.obligations.open_state,
        };
        if let Some(enclosing) = enclosing {
            let template = callable.has_via_inputs() || enclosing && !named;
            let result_span = self.ast(env.file).ty(signature.result).span;
            if signature.result_mode == Mode::Infer && !template {
                self.error(
                    Code::E0412,
                    result_span,
                    "infer requires a via input in scope",
                );
            }
            for (syntax, param) in signature.params.iter().zip(&callable.parameters) {
                let span = syntax
                    .ty
                    .map_or(result_span, |ty| self.ast(env.file).ty(ty).span);
                self.check_nested_callable_modes(&param.ty, template, span);
            }
            self.check_nested_callable_modes(&callable.result, template, result_span);
        }
        callable
    }

    fn check_nested_callable_modes(&mut self, ty: &Ty, enclosing: bool, span: Span) {
        transform(ty, &mut |ty| {
            let Ty::Callable(callable) = ty else {
                return None;
            };
            let template = enclosing || callable.has_via_inputs();
            if callable.result_mode == Mode::Infer && !template {
                self.error(Code::E0412, span, "infer requires a via input in scope");
            }
            for param in &callable.parameters {
                self.check_nested_callable_modes(&param.ty, template, span);
            }
            self.check_nested_callable_modes(&callable.result, template, span);
            Some(Ty::Unknown)
        });
    }

    fn guard_parameter(&mut self, env: &Env, guard: syntax::ExprId) -> Ty {
        let ast = self.ast(env.file);
        let mut node = ast.expr(guard);
        if let syntax::Expr::Unary { op, value } = &node.value
            && op.value == "ref"
        {
            node = ast.expr(*value);
        }
        if let syntax::Expr::Call { callee, .. } = node.value {
            node = ast.expr(callee);
        }
        if let syntax::Expr::Path(path) = &node.value
            && let Some(id) = self.resolve(path.span)
        {
            let call = self.declare_function(id);
            if let Some(param) = call.parameters.first() {
                return param.ty.clone();
            }
        }
        self.error(
            Code::E0544,
            node.span,
            "first guard does not determine the parameter type",
        );
        Ty::Unknown
    }

    pub(super) fn project(
        &mut self,
        env: &mut Env,
        field: &Coordinate,
        base: &Ty,
        span: Span,
        type_level: bool,
    ) -> Ty {
        let mut ty = self.normalize(base);
        if let Coordinate::Computed(expr) = field
            && let syntax::Expr::Path(path) = &self.ast(env.file).expr(*expr).value
            && let Some(key) = self.resolve(path.span)
            && env
                .meta_keys
                .get(&key)
                .is_some_and(|target| self.normalize(target) == ty)
            && !env.generics.contains_key(&key)
        {
            return Ty::Projection(Box::new(ty), key);
        }
        if ty == Ty::PanicInfo {
            self.error(Code::E0308, span, "PanicInfo is opaque");
            return Ty::Unknown;
        }
        if let Ty::Param(id) = &ty {
            let id = *id;
            if let Some(GenericValue::Type(specialized)) = env.generics.get(&id) {
                ty = specialized.clone();
            } else if let Some(domains) = env.domains.get(&id)
                && let [record @ Ty::Record(_, _)] = domains.as_slice()
            {
                ty = record.clone();
            }
        }
        if let Ty::Adt(adt) = &ty {
            match adt.kind {
                AdtKind::Foreign => {
                    self.error(Code::E0907, span, "foreign representation is sealed");
                    return Ty::Unknown;
                }
                AdtKind::Opaque | AdtKind::OpaqueSum if adt.defining_scope != env.scope => {
                    self.error(Code::E0308, span, "opaque representation is sealed");
                    return Ty::Unknown;
                }
                AdtKind::Nominal | AdtKind::Opaque => {
                    if let Some(rep) = self.representation(env, adt) {
                        ty = rep;
                    }
                }
                AdtKind::Sum | AdtKind::OpaqueSum if type_level => {
                    let def = self.hir.definition(adt.definition);
                    if let Coordinate::Name(name) = field
                        && let Some(stmt) = def.stmt
                        && let StmtKind::Type(decl) = &self.ast(def.name.span.file).stmt(stmt).value.kind
                        && let TypeDefinition::Sum(variants) = &decl.definition
                        && let Some(Variant::Constructor { payload, .. }) = variants.iter().find(|variant|
                            matches!(variant, Variant::Constructor { name: variant, .. } if variant.value == name.value))
                    {
                        let mut local = self.instantiate_adt(adt);
                        let parts: Vec<_> = payload.iter().flatten().map(|&ty| Member::plain(self.type_expr(&mut local, ty))).collect();
                        return match parts.as_slice() {
                            [] => Ty::Unit,
                            [one] => one.ty.clone(),
                            _ => Ty::Tuple(parts),
                        };
                    }
                }
                _ => {}
            }
        }
        let coordinate = match field {
            Coordinate::Name(name) => Some(Value::Str(name.value.clone())),
            Coordinate::Index(name) => name.value.parse().ok().map(Value::Int),
            Coordinate::Computed(expr) => self.eval_root(env, *expr, false),
        };
        match (&ty, coordinate) {
            (Ty::Draft(inner), _) => self.project(env, field, inner, span, type_level),
            (Ty::Record(fields, open), Some(Value::Str(name))) => {
                fields.get(&name).map(|m| m.ty.clone()).unwrap_or_else(|| {
                    if !open {
                        self.error(Code::E0336, span, format!("unknown record field {name}"));
                    }
                    Ty::Unknown
                })
            }
            (Ty::Tuple(items), Some(Value::Int(index))) => {
                use num_traits::{Signed as _, ToPrimitive as _};
                if index.is_negative() {
                    self.error(Code::E0815, span, "negative static tuple coordinate");
                    return Ty::Unknown;
                }
                index
                    .to_usize()
                    .and_then(|index| items.get(index))
                    .map(|m| m.ty.clone())
                    .unwrap_or_else(|| {
                        self.error(Code::E0312, span, "tuple coordinate is out of bounds");
                        Ty::Unknown
                    })
            }
            (Ty::Record(..) | Ty::Tuple(_), None) => {
                self.error(Code::E0324, span, "projection coordinate must be static");
                Ty::Unknown
            }
            (Ty::Unknown | Ty::Never | Ty::Infer(_), _) => Ty::Unknown,
            _ => {
                self.error(
                    Code::E0337,
                    span,
                    "member projection requires a valid record or tuple coordinate",
                );
                Ty::Unknown
            }
        }
    }

    pub(super) fn declare_meta_key(&mut self, env: &mut Env, parameter: &syntax::Parameter) {
        let Some(key) = parameter
            .name
            .as_ref()
            .and_then(|name| self.resolve(name.span))
        else {
            return;
        };
        self.meta_parameters.insert(key);
        for &guard in &parameter.guards {
            if let syntax::Expr::Path(path) = &self.ast(env.file).expr(guard).value
                && self.prelude_key(path)
                && let Some(argument) = path
                    .segments
                    .last()
                    .and_then(|member| member.arguments.first())
            {
                let owner = self.type_argument(env, argument);
                env.meta_keys.insert(key, owner);
                return;
            }
        }
    }

    fn prelude_key(&self, path: &syntax::Path) -> bool {
        self.resolve(path.span).is_some_and(|id| {
            let def = self.hir.definition(id);
            matches!(def.kind, DefinitionKind::Primitive(_)) && def.name.value == "Key"
        })
    }

    fn has_key(&mut self, env: &Env, base: &Ty, key: &Value) -> bool {
        match (self.normalize(base), key) {
            (Ty::Record(fields, _), Value::Str(key)) => fields.contains_key(key),
            (Ty::Tuple(items), Value::Int(key)) => {
                use num_traits::ToPrimitive as _;
                key.to_usize().is_some_and(|index| index < items.len())
            }
            (Ty::Adt(adt), _)
                if adt.kind == AdtKind::Nominal
                    || adt.kind == AdtKind::Opaque && adt.defining_scope == env.scope =>
            {
                self.representation(env, &adt)
                    .is_some_and(|ty| self.has_key(env, &ty, key))
            }
            (Ty::Unknown | Ty::Infer(_), _) => true,
            _ => false,
        }
    }

    pub(super) fn specialize_projections(&mut self, env: &mut Env, ty: &Ty, span: Span) -> Ty {
        transform(ty, &mut |candidate| {
            let Ty::Projection(base, key) = candidate else {
                return None;
            };
            let Some(GenericValue::Data(key)) = env.generics.get(key) else {
                return None;
            };
            let field = match key {
                Value::Str(name) => Coordinate::Name(syntax::Name::new(name.clone(), span)),
                Value::Int(index) => Coordinate::Index(syntax::Name::new(index.to_string(), span)),
                _ => return Some(Ty::Unknown),
            };
            if !self.has_key(env, base, key) {
                return Some(Ty::Unknown);
            }
            Some(self.project(env, &field, base, span, true))
        })
    }

    pub(super) fn eligible_key(
        &mut self,
        env: &Env,
        ty: &Ty,
        seen: &mut HashSet<DefinitionId>,
    ) -> bool {
        let immutable = |m: &Member| m.mode == super::MemberMode::PLAIN;
        match ty {
            Ty::F64 | Ty::Callable(_) | Ty::Draft(_) | Ty::TypeValue(_) => false,
            Ty::Array(member) => immutable(member) && self.eligible_key(env, &member.ty, seen),
            Ty::Map(key, member) => {
                immutable(member)
                    && self.eligible_key(env, key, seen)
                    && self.eligible_key(env, &member.ty, seen)
            }
            Ty::Record(fields, open) => {
                !open
                    && fields
                        .values()
                        .all(|member| immutable(member) && self.eligible_key(env, &member.ty, seen))
            }
            Ty::Tuple(items) => items
                .iter()
                .all(|member| immutable(member) && self.eligible_key(env, &member.ty, seen)),
            Ty::Option(inner) | Ty::Set(inner) => self.eligible_key(env, inner, seen),
            Ty::Result(ok, err) => {
                self.eligible_key(env, ok, seen) && self.eligible_key(env, err, seen)
            }
            Ty::Adt(adt) if adt.kind == AdtKind::Foreign => false,
            Ty::Adt(adt) if seen.insert(adt.definition) => self
                .representation(env, adt)
                .is_none_or(|ty| self.eligible_key(env, &ty, seen)),
            _ => true,
        }
    }
}
