use std::{
    collections::{BTreeMap, HashSet},
    sync::Arc,
};

use ril_hir::{DefinitionKind, PrimitivePhase};
use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::{self, Argument, Expr, ExprId, Mode};

use crate::ty::{
    AdtKind, Callable, Member, Parameter, Ty,
    check::{Checker, Env, ImplicitExits, Phase, substitute, unknown_callable},
};

impl Checker<'_> {
    pub(super) fn propagate(&mut self, env: &Env, actual: Ty, span: Span) -> Ty {
        let actual = self.normalize(&actual);
        self.propagation_inputs.insert(span, actual.clone());
        if let Some((ok, error)) = actual.as_result(self.hir) {
            let (ok, error) = (ok.clone(), error.clone());
            if let Some(index) = env.inferred_return {
                if !env.shadow {
                    self.closure_exits(index).errors.push(error);
                }
            } else if !env
                .expected_return
                .as_ref()
                .and_then(|ty| ty.as_result(self.hir))
                .is_some_and(|(_, target)| {
                    self.fits(env, &error, target) || self.sum_subset(env, &error, target)
                })
            {
                self.error(
                    Code::E0713,
                    span,
                    "enclosing function cannot propagate this error type",
                );
            }
            return ok;
        }
        if let Some(ok) = actual.as_option(self.hir) {
            let ok = ok.clone();
            if let Some(index) = env.inferred_return {
                if !env.shadow {
                    self.closure_exits(index).none = true;
                }
            } else if !env
                .expected_return
                .as_ref()
                .is_some_and(|ty| ty.is_option(self.hir))
            {
                self.error(
                    Code::E0713,
                    span,
                    "enclosing function cannot propagate None",
                );
            }
            return ok;
        }
        match actual {
            Ty::Unknown | Ty::Never => actual,
            _ => {
                self.error(Code::E0712, span, "propagation requires Result or Option");
                Ty::Unknown
            }
        }
    }

    pub(super) fn check_return(&mut self, env: &mut Env, value: Option<ExprId>, span: Span) {
        let target = env.expected_return.clone();
        let actual = value.map_or(Ty::Unit, |value| self.expr(env, value, target.as_ref()));
        if env.return_scope.is_some_and(|scope| {
            self.exposes_type(&actual, |id| {
                let name = self.hir.definition(id).name.span;
                name.file == scope.file && scope.start <= name.start && name.end <= scope.end
            })
        }) {
            self.error(
                Code::E0315,
                span,
                "return exposes a type declared inside the callable",
            );
        } else if let Some(target) = target {
            self.require(env, span, &actual, &target);
        } else if let Some(index) = env.inferred_return
            && !env.shadow
        {
            self.closure_exits(index).returns.push((span, actual));
        }
    }

    fn infer_closure_result(
        &mut self,
        env: &Env,
        body: Ty,
        exits: ImplicitExits,
        span: Span,
    ) -> Ty {
        let result = exits
            .returns
            .into_iter()
            .fold(body, |result, (at, returned)| {
                self.join(env, at, result, returned)
            });
        let result = self.normalize(&result);
        if exits.errors.is_empty() && !exits.none {
            return result;
        }
        if exits.none {
            if exits.errors.is_empty() {
                let fresh = self.fresh();
                let target = self.make_option(fresh);
                if self.fits(env, &result, &target) {
                    return self.normalize(&target);
                }
            }
        } else {
            let mut errors = exits
                .errors
                .iter()
                .map(|ty| self.normalize(ty))
                .collect::<Vec<_>>();
            let mut greatest = None;
            // A candidate must dominate every error originating at a propagation site.
            // Distinct nominal types with equal tag sets are still separate candidates.
            while let Some(candidate) = errors.pop() {
                if exits.errors.iter().all(|ty| {
                    let ty = self.normalize(ty);
                    ty == candidate || self.sum_subset(env, &ty, &candidate)
                }) {
                    if greatest
                        .as_ref()
                        .is_some_and(|previous| previous != &candidate)
                    {
                        greatest = None;
                        break;
                    }
                    greatest = Some(candidate);
                }
            }
            if let Some(error) = greatest {
                let fresh = self.fresh();
                let target = self.make_result(fresh, error);
                if self.fits(env, &result, &target) {
                    return self.normalize(&target);
                }
            }
        }
        self.error(
            Code::E0344,
            span,
            "cannot infer a fallible closure result from these propagation sites",
        );
        Ty::Unknown
    }

    pub(super) fn closure(
        &mut self,
        env: &Env,
        (span, params): (Span, &[syntax::Parameter]),
        obligations: &syntax::Obligations,
        body: ExprId,
        expected: Option<&Ty>,
    ) -> Ty {
        let expected_call = if let Some(Ty::Callable(call)) = expected {
            Some(call)
        } else {
            None
        };
        let mut local = env.clone();
        if params.iter().any(|param| param.mode == Mode::Via) {
            local.mode_scope = Some(true);
        }
        if env.phase == Phase::Runtime && params.iter().any(|param| param.is_meta) {
            local.staging_owner = Some(span);
        }
        local.expected_return = expected_call.map(|sig| sig.result.clone());
        local.inferred_return = None;
        local.return_scope = Some(self.ast(env.file).expr(body).span);
        let mut parameters = Vec::new();
        for (index, item) in params.iter().enumerate() {
            if item.is_meta {
                self.declare_meta_key(&mut local, item);
            }
            let expected_param = expected_call.and_then(|sig| sig.parameters.get(index));
            let ty = if let Some(ty) = item.ty {
                self.type_expr(&mut local, ty)
            } else if let Some(param) = expected_param {
                param.ty.clone()
            } else {
                self.fresh()
            };
            if let Some(pattern) = item.pattern {
                self.pattern(&mut local, pattern, &ty);
            } else if let Some(name) = &item.name {
                self.define_name(name, ty.clone());
            }
            if let Some(default) = item.default {
                if item.is_meta {
                    let mut meta_env = local.clone();
                    meta_env.phase = Phase::MetaValue;
                    self.expect(&mut meta_env, default, &ty);
                } else {
                    self.expect(&mut local, default, &ty);
                }
            }
            let is_wildcard = item.name.as_ref().is_some_and(|name| name.value == "_")
                || item.pattern.is_some_and(|pat| {
                    matches!(
                        self.ast(env.file).pattern(pat).value,
                        syntax::Pattern::Wildcard
                    )
                });
            let mode = if item.mode == Mode::Plain
                && is_wildcard
                && expected_param.is_some_and(|param| {
                    param.mode == Mode::New
                        && matches!(self.normalize(&param.ty), Ty::Callable(c) if c.is_ctl)
                }) {
                Mode::New
            } else {
                item.mode
            };
            parameters.push(Parameter {
                label: item.name.as_ref().map(|name| name.value.clone()),
                mode,
                ty,
                optional: item.default.is_some(),
                is_meta: item.is_meta,
            });
        }
        if parameters.iter().any(|param| param.ty.has_via_members()) {
            local.mode_scope = Some(true);
        }
        let infer_result = local.expected_return.is_none();
        if infer_result {
            local.inferred_return = Some(self.implicit_exits.len());
            self.implicit_exits.push(ImplicitExits::default());
        }
        let target = local.expected_return.clone();
        let result = self.expr(&mut local, body, target.as_ref());
        let result = if infer_result {
            let exits = self.implicit_exits.pop().unwrap_or_else(|| {
                ril_source::ice!("missing inference state for the current closure")
            });
            self.infer_closure_result(&local, result, exits, self.ast(env.file).expr(body).span)
        } else {
            result
        };
        let effects = if obligations.effects.is_empty() {
            let mut used: Vec<_> = local
                .effects_seen
                .difference(&env.effects_seen)
                .cloned()
                .collect();
            used.sort();
            used
        } else {
            obligations
                .effects
                .iter()
                .map(|path| self.effect_label(&mut local, path))
                .collect()
        };
        let once = obligations
            .state
            .iter()
            .any(|clause| clause.kind == syntax::StateKind::Once);
        Ty::Callable(Arc::new(Callable {
            parameters,
            result,
            effects,
            open_effects: obligations.open_effects,
            once,
            ..unknown_callable()
        }))
    }

    pub(super) fn call(
        &mut self,
        env: &mut Env,
        callee_id: ExprId,
        args: &[Argument],
        expected: Option<&Ty>,
        span: Span,
    ) -> Ty {
        let ast = self.ast(env.file);
        let callee = ast.expr(callee_id);
        let path = match &callee.value {
            Expr::Path(path) => Some(path),
            _ => None,
        };
        let def_id = path.and_then(|p| self.resolve(p.span));
        let effect_arguments = if let (Some(id), Some(path)) = (def_id, path) {
            let args = self.operation_instance(env, id, path);
            if !env.shadow
                && let Some(label) = self.operation_effects.get(&path.span)
            {
                env.effects_seen.insert(label.clone());
            }
            args
        } else {
            Default::default()
        };
        let (ty, generics) = if let Some(id) = def_id {
            let def = self.hir.definition(id);
            match def.kind {
                DefinitionKind::Primitive(phase) => {
                    if !env.shadow {
                        if phase == PrimitivePhase::Runtime && env.phase != Phase::Runtime {
                            self.error(
                                Code::E0810,
                                callee.span,
                                "runtime primitive called in static computation",
                            );
                        } else if phase == PrimitivePhase::Static && env.phase == Phase::Runtime {
                            self.error(
                                Code::E0810,
                                callee.span,
                                "calling a meta fn in runtime code requires 'meta'",
                            );
                        }
                    }
                    if self.hir.primitive_module(id) == Some("Reflect")
                        && matches!(
                            def.name.value.as_str(),
                            "attrs" | "field_attrs" | "variant_attrs"
                        )
                        && let Some(path) = path
                    {
                        return self.reflect_call(env, path, args, expected, span);
                    }
                    if self
                        .hir
                        .intrinsic(id)
                        .is_some_and(ril_hir::Intrinsic::uses_declared_signature)
                    {
                        let type_args = path
                            .and_then(|p| p.segments.last())
                            .map_or(&[][..], |p| p.arguments.as_slice());
                        let generic = self.call_argument_types(env, id, type_args, span);
                        (Ty::Callable(self.declare_function(id)), generic)
                    } else {
                        return self.primitive_call(env, &def.name.value, args, expected, span);
                    }
                }
                DefinitionKind::Type => {
                    for arg in args {
                        self.expr(env, arg.value, None);
                    }
                    self.error(
                        Code::E0338,
                        callee.span,
                        "nominal construction requires 'Name::(...)' syntax",
                    );
                    return Ty::Unknown;
                }
                DefinitionKind::Function => {
                    let is_stdlib = self.hir.is_stdlib_file(def.name.span.file);
                    if !env.shadow && self.is_meta_fn(id) && env.phase == Phase::Runtime {
                        self.error(
                            Code::E0810,
                            callee.span,
                            "calling a meta fn in runtime code requires 'meta'",
                        );
                    }
                    if !env.shadow
                        && !self.is_meta_fn(id)
                        && !is_stdlib
                        && env.phase != Phase::Runtime
                    {
                        self.error(
                            Code::E0810,
                            callee.span,
                            "ordinary runtime fn called in static computation",
                        );
                    }
                    let args = path
                        .and_then(|p| p.segments.last())
                        .map_or(&[][..], |p| p.arguments.as_slice());
                    let mut generic = self.call_argument_types(env, id, args, span);
                    generic.extend(effect_arguments);
                    (Ty::Callable(self.declare_function(id)), generic)
                }
                _ => (
                    self.path_expr(
                        env,
                        path.unwrap_or_else(|| ril_source::ice!("resolved call without path")),
                        expected,
                        true,
                    ),
                    Default::default(),
                ),
            }
        } else if let Expr::Closure {
            params,
            obligations,
            body,
        } = &callee.value
        {
            (
                self.closure(env, (callee.span, params), obligations, *body, None),
                Default::default(),
            )
        } else {
            (self.expr(env, callee_id, None), Default::default())
        };
        self.types.insert(callee.span, ty.clone());
        let Ty::Callable(call) = self.normalize(&ty) else {
            for arg in args {
                self.expr(env, arg.value, None);
            }
            if ty != Ty::Unknown && ty != Ty::Never {
                self.error(Code::E0338, callee.span, "expression is not callable");
            }
            return Ty::Unknown;
        };

        let result = substitute(&call.result, &generics);
        let has_meta = call.parameters.iter().any(|parameter| parameter.is_meta);
        if let Some(expect) = expected {
            self.fits(env, &result, expect);
        }
        if def_id
            .is_some_and(|id| matches!(self.hir.definition(id).kind, DefinitionKind::Variant(_)))
            && (args.is_empty()
                && matches!(call.parameters.as_slice(), [parameter] if {
                    let norm = self.normalize(&parameter.ty);
                    norm == Ty::Unit || (matches!(norm, Ty::Infer(_)) && self.fits(env, &Ty::Unit, &norm))
                })
                || self.check_tuple_payload(
                    env,
                    args,
                    &call
                        .parameters
                        .iter()
                        .map(|p| p.ty.clone())
                        .collect::<Vec<_>>(),
                    span,
                ))
        {
            return self.normalize(&result);
        }
        let mut used = vec![false; call.parameters.len()];
        let mut metadata = BTreeMap::new();
        for arg in args {
            let location = if let Some(name) = &arg.name {
                call.parameters
                    .iter()
                    .position(|p| p.label.as_deref() == Some(&name.value))
            } else {
                used.iter().position(|used| !used)
            };
            let arg_span = ast.expr(arg.value).span;
            let Some(index) = location else {
                self.error(
                    if arg.name.is_some() {
                        Code::E0339
                    } else {
                        Code::E0314
                    },
                    arg_span,
                    "no parameter matches this argument",
                );
                self.expr(env, arg.value, None);
                continue;
            };
            if used.get(index) == Some(&true) {
                self.error(Code::E0325, arg_span, "parameter was already supplied");
            }
            if let Some(used) = used.get_mut(index) {
                *used = true;
            }
            let parameter = call
                .parameters
                .get(index)
                .unwrap_or_else(|| ril_source::ice!("bound argument without parameter"));
            let param_ty = substitute(&parameter.ty, &generics);
            let allows_draft_receiver = index == 0
                && def_id.is_some_and(|id| {
                    matches!(self.hir.primitive_module(id), Some("Array" | "Map" | "Set"))
                });
            if allows_draft_receiver {
                let actual = self.expr(env, arg.value, None);
                let normalized = self.normalize(&actual);
                if let Ty::Draft(inner) = normalized {
                    self.require(env, arg_span, &inner, &param_ty);
                } else {
                    self.require(env, arg_span, &normalized, &param_ty);
                }
            } else if parameter.is_meta {
                let mut arg_env = env.clone();
                arg_env.phase = Phase::MetaValue;
                if env.phase == Phase::Runtime {
                    arg_env.static_boundary = Some(arg_span);
                }
                self.expect(&mut arg_env, arg.value, &param_ty);
            } else {
                self.expect(env, arg.value, &param_ty);
            }
            if matches!(arg.mode, Mode::Mut | Mode::Shared | Mode::Ref)
                && let Some(arg_ty) = self.types.get(&arg_span).cloned()
                && self.is_value_ty(env, &arg_ty)
            {
                self.error(
                    Code::E0401,
                    arg_span,
                    "value-type argument cannot carry live authority",
                );
            }
            if !parameter.is_meta && parameter.mode != Mode::Via && parameter.mode != arg.mode {
                self.error(
                    if arg.mode == Mode::Plain {
                        Code::E0405
                    } else {
                        Code::E0406
                    },
                    arg_span,
                    "required explicit argument mode does not match",
                );
            }
            if parameter.is_meta
                && env.phase == Phase::Runtime
                && !env.shadow
                && let Some(value) = self.stage_static_argument(env, arg.value, true)
            {
                metadata.insert(index, value);
            }
        }
        if call
            .parameters
            .iter()
            .zip(&used)
            .any(|(param, supplied)| !supplied && !param.optional)
        {
            self.error(Code::E0314, span, "required argument is missing");
        }
        if call.open_effects
            || call.open_state
            || call.effects.iter().any(|eff| eff != "io")
            || call
                .state
                .iter()
                .any(|clause| clause == "up" || clause.starts_with("up("))
        {
            self.invalidate_live(
                env,
                Code::E0533,
                span,
                crate::ty::NarrowDropCause::OpenStateCall,
            );
        } else if call
            .state
            .iter()
            .any(|clause| clause == "mut" || clause == "^mut")
        {
            for argument in args
                .iter()
                .filter(|arg| matches!(arg.mode, Mode::Mut | Mode::Shared))
            {
                if argument.mode == Mode::Shared {
                    self.invalidate_live(
                        env,
                        Code::E0310,
                        span,
                        crate::ty::NarrowDropCause::AliasingMut,
                    );
                } else {
                    self.writes_place(env, argument.value, span);
                }
            }
        }
        let effects = if !call.effects.is_empty()
            && let Some(id) = def_id
            && let Some(specialized) = self.call_effects(id, &generics)
        {
            self.effect_applications.insert(span, specialized.clone());
            specialized
        } else {
            call.effects.clone()
        };
        if !env.shadow {
            env.effects_seen.extend(effects);
        }
        if let Some(known) = def_id {
            self.validate_generic_uses(env, known, &generics, span);
            if self.hir.intrinsic(known) == Some(ril_hir::Intrinsic::StringInspect) {
                if let Some(arg) = args.first()
                    && arg.mode != Mode::Plain
                {
                    let arg_span = ast.expr(arg.value).span;
                    let first = self.types.get(&arg_span).cloned().unwrap_or(Ty::Unknown);
                    if self.is_value_ty(env, &first) {
                        self.error(
                            Code::E0401,
                            arg_span,
                            "value-type argument cannot carry live authority",
                        );
                    } else if arg.mode != Mode::Ref {
                        self.error(
                            Code::E0406,
                            arg_span,
                            "String::inspect accepts plain or ref access",
                        );
                    }
                }
                self.inspection_scopes.insert(span, env.scope);
            }
            if self.hir.primitive_module(known) == Some("Array")
                && self.hir.definition(known).name.value == "sort"
                && let Some(arg0) = args.first()
            {
                let arg0_span = ast.expr(arg0.value).span;
                let mut receiver = self.types.get(&arg0_span).cloned().unwrap_or(Ty::Unknown);
                receiver = self.normalize(&receiver);
                if let Ty::Draft(inner) = receiver {
                    receiver = self.normalize(&inner);
                }
                if let Ty::Array(elem) = receiver {
                    let elem_ty = self.normalize(&elem.ty);
                    let orderable = matches!(
                        &elem_ty,
                        Ty::Int | Ty::F64 | Ty::Str | Ty::Bytes | Ty::Unknown | Ty::Infer(_)
                    ) || matches!(&elem_ty, Ty::Param(id) if env
                    .domains
                    .get(id)
                    .is_some_and(|dom| dom.iter().all(|t| matches!(
                        t,
                        Ty::Int | Ty::F64 | Ty::Str | Ty::Bytes
                    ))));
                    if !orderable {
                        self.error(Code::E0327, span, "Array::sort requires orderable elements");
                    }
                }
            }
            if self.hir.primitive_module(known) == Some("Set")
                && matches!(
                    self.hir.definition(known).name.value.as_str(),
                    "empty" | "from_array"
                )
                && let Some(elem) = self.normalize(&result).as_set(self.hir)
                && !self.eligible_key(env, elem, &mut HashSet::new())
            {
                self.error(
                    Code::E0328,
                    span,
                    "set element type does not support stable equality",
                );
            }
        }
        if !env.shadow && !generics.is_empty() {
            self.generic_arguments.insert(span, generics.clone());
        }
        let result =
            if (has_meta || !generics.is_empty()) && !env.shadow && env.phase == Phase::Runtime {
                let application = crate::ty::staging::Application {
                    span,
                    supplied: &used,
                    inputs: &metadata,
                };
                if let Some(id) = def_id {
                    self.specialize_meta_call(env, id, &generics, &application, &result)
                } else if let Expr::Closure { params, .. } = &callee.value {
                    self.specialize_meta_parameters(
                        env,
                        env.clone(),
                        callee.span,
                        params,
                        &application,
                        &result,
                    )
                } else {
                    result
                }
            } else {
                result
            };
        self.normalize(&result)
    }

    pub(super) fn wrap(
        &mut self,
        env: &mut Env,
        path: &syntax::Path,
        args: &[Argument],
        expected: Option<&Ty>,
        span: Span,
    ) -> Ty {
        if let Some(id) = self.resolve(path.span)
            && self.hir.definition(id).kind != DefinitionKind::Type
        {
            for arg in args {
                self.expr(env, arg.value, None);
            }
            self.error(
                Code::E0338,
                span,
                "'::(...)' construction is only valid for nominal or opaque wrapper types",
            );
            return Ty::Unknown;
        }
        let ty = self.constructor_type(env, path, expected);
        self.types.insert(path.span, ty.clone());
        self.nominal_constructor(env, ty, args, span)
    }

    fn nominal_constructor(&mut self, env: &mut Env, ty: Ty, args: &[Argument], span: Span) -> Ty {
        let Ty::Adt(adt) = &ty else {
            for arg in args {
                self.expr(env, arg.value, None);
            }
            if ty != Ty::Unknown {
                self.error(Code::E0338, span, "type is not a nominal wrapper");
            }
            return Ty::Unknown;
        };
        if matches!(adt.kind, AdtKind::Sum | AdtKind::OpaqueSum) {
            for arg in args {
                self.expr(env, arg.value, None);
            }
            self.error(
                Code::E0338,
                span,
                "sum types do not use nominal '::(...)' construction",
            );
            return Ty::Unknown;
        }
        if adt.kind == AdtKind::Foreign {
            for arg in args {
                self.expr(env, arg.value, None);
            }
            self.error(Code::E0907, span, "foreign nominal cannot be constructed");
            return Ty::Unknown;
        }
        if adt.kind == AdtKind::Opaque && adt.defining_scope != env.scope {
            for arg in args {
                self.expr(env, arg.value, None);
            }
            if self.hir.std_type(adt.definition) == Some(ril_hir::StdType::PanicReport) {
                self.error(
                    Code::E0301,
                    span,
                    "PanicReport has no accessible constructor",
                );
            } else {
                self.error(Code::E0308, span, "opaque constructor is sealed");
            }
            return Ty::Unknown;
        }
        let is_unit_nominal = self.hir.unit_constructor(adt.definition);
        let rep = self.representation(env, adt);
        if is_unit_nominal || rep.is_none() {
            for arg in args {
                self.expr(env, arg.value, None);
            }
            self.error(
                Code::E0338,
                span,
                "unit nominal type does not use '::(...)' wrap syntax",
            );
            return Ty::Unknown;
        }
        if let Some(Ty::Record(required, open)) = rep {
            if args.len() != 1 {
                for arg in args {
                    self.expr(env, arg.value, None);
                }
                self.error(Code::E0314, span, "invalid constructor payload arity");
                return ty;
            }
            let Some(arg) = args.first() else {
                return ty;
            };
            let arg_node = self.ast(env.file).expr(arg.value).clone();
            if arg.name.is_some() {
                self.error(
                    Code::E0339,
                    arg_node.span,
                    "positional constructor does not accept named arguments",
                );
            }
            if !matches!(arg.mode, Mode::Plain | Mode::Ref | Mode::Shared | Mode::New) {
                self.error(
                    Code::E0406,
                    arg_node.span,
                    "constructor argument has an unsupported access mode",
                );
            }
            if let syntax::Expr::Record { name: None, fields } = &arg_node.value {
                let inner_ty = self.record_literal_against_schema(
                    env,
                    fields,
                    required,
                    open,
                    true,
                    Some(&ty),
                    arg_node.span,
                );
                self.types.insert(arg_node.span, inner_ty);
            } else {
                let rep_ty = Ty::Record(required, open);
                self.expect(env, arg.value, &rep_ty);
            }
            return ty;
        }
        if let Some(Ty::Tuple(fields)) = &rep
            && let [arg] = args
            && fields.len() >= 2
        {
            let arg_span = self.ast(env.file).expr(arg.value).span;
            if arg.name.is_some() {
                self.error(
                    Code::E0339,
                    arg_span,
                    "positional constructor does not accept named arguments",
                );
            }
            if !matches!(arg.mode, Mode::Plain | Mode::Ref | Mode::Shared | Mode::New) {
                self.error(
                    Code::E0406,
                    arg_span,
                    "constructor argument has an unsupported access mode",
                );
            }
            let tuple_ty = Ty::Tuple(fields.clone());
            self.expect(env, arg.value, &tuple_ty);
            return ty;
        }
        if args.is_empty() && matches!(rep, Some(Ty::Unit)) {
            return ty;
        }
        let params = match rep {
            Some(Ty::Tuple(fields)) => fields.into_iter().map(|m| m.ty).collect(),
            Some(one) => vec![one],
            None => unreachable!(),
        };
        if args.len() != params.len() {
            self.error(Code::E0314, span, "invalid constructor payload arity");
        }
        let single = params.len() == 1;
        for (arg, param_ty) in args.iter().zip(params) {
            let arg_span = self.ast(env.file).expr(arg.value).span;
            if arg.name.is_some() {
                self.error(
                    Code::E0339,
                    arg_span,
                    "positional constructor does not accept named arguments",
                );
            }
            let allowed_mode = if single {
                matches!(arg.mode, Mode::Plain | Mode::Ref | Mode::Shared | Mode::New)
            } else {
                arg.mode == Mode::Plain
            };
            if !allowed_mode {
                self.error(
                    Code::E0406,
                    arg_span,
                    "constructor argument has an unsupported access mode",
                );
            }
            self.expect(env, arg.value, &param_ty);
            if matches!(arg.mode, Mode::Mut | Mode::Shared | Mode::Ref)
                && let Some(arg_ty) = self.types.get(&arg_span).cloned()
                && self.is_value_ty(env, &arg_ty)
            {
                self.error(
                    Code::E0401,
                    arg_span,
                    "value-type argument cannot carry live authority",
                );
            }
        }
        ty
    }

    pub(super) fn constructor_type(
        &mut self,
        env: &mut Env,
        path: &syntax::Path,
        expected: Option<&Ty>,
    ) -> Ty {
        if let Some(Ty::Adt(adt)) = expected
            && self.resolve(path.span) == Some(adt.definition)
            && path
                .segments
                .last()
                .is_some_and(|segment| segment.arguments.is_empty())
        {
            Ty::Adt(Arc::clone(adt))
        } else {
            self.named_type(env, path)
        }
    }

    fn check_tuple_payload(
        &mut self,
        env: &mut Env,
        arguments: &[Argument],
        parts: &[Ty],
        span: Span,
    ) -> bool {
        let [argument] = arguments else { return false };
        if parts.len() < 2 {
            return false;
        }
        let tuple = Ty::Tuple(parts.iter().cloned().map(Member::plain).collect());
        if argument.mode != Mode::Plain {
            self.error(
                Code::E0406,
                self.ast(env.file).expr(argument.value).span,
                "tuple payload must be plain",
            );
        }
        self.expect(env, argument.value, &tuple);
        self.tuple_payloads.insert(span, parts.len());
        true
    }
}
