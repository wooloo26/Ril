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
        match actual {
            Ty::Result(ok, error) => {
                if let Some(index) = env.inferred_return {
                    if !env.shadow {
                        self.closure_exits(index).errors.push(*error);
                    }
                } else if !matches!(&env.expected_return, Some(Ty::Result(_, target))
                    if self.fits(env, &error, target) || self.sum_subset(env, &error, target))
                {
                    self.error(
                        Code::E0713,
                        span,
                        "enclosing function cannot propagate this error type",
                    );
                }
                *ok
            }
            Ty::Option(ok) => {
                if let Some(index) = env.inferred_return {
                    if !env.shadow {
                        self.closure_exits(index).none = true;
                    }
                } else if !matches!(env.expected_return, Some(Ty::Option(_))) {
                    self.error(
                        Code::E0713,
                        span,
                        "enclosing function cannot propagate None",
                    );
                }
                *ok
            }
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
                let target = Ty::Option(Box::new(self.fresh()));
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
                let target = Ty::Result(Box::new(self.fresh()), Box::new(error));
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
                self.expect(&mut local, default, &ty);
            }
            parameters.push(Parameter {
                label: item.name.as_ref().map(|name| name.value.clone()),
                mode: item.mode,
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
        Ty::Callable(Arc::new(Callable {
            parameters,
            result,
            effects,
            open_effects: obligations.open_effects,
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
        let mut pending_meta = false;
        let (ty, generics) = if let Some(id) = def_id {
            let def = self.hir.definition(id);
            match def.kind {
                DefinitionKind::Primitive(phase) => {
                    if self.hir.primitive_module(id) == Some("Reflect")
                        && matches!(
                            def.name.value.as_str(),
                            "attrs" | "field_attrs" | "variant_attrs"
                        )
                        && let Some(path) = path
                    {
                        return self.reflect_call(env, path, args, expected, span);
                    }
                    if let Some(module @ ("Fiber" | "Channel")) = self.hir.primitive_module(id) {
                        let explicit = if module == "Channel"
                            && matches!(def.name.value.as_str(), "bounded" | "unbounded")
                            && let Some(segment) = path.and_then(|path| path.segments.last())
                            && let Some(argument) = segment.arguments.first()
                        {
                            if segment.arguments.len() > 1 {
                                self.error(
                                    Code::E0340,
                                    segment.name.span,
                                    "channel constructor takes one element type",
                                );
                            }
                            let ty = self.type_argument(env, argument);
                            if !self.is_sendable(env, &ty, &mut HashSet::new()) {
                                self.error(
                                    Code::E0301,
                                    span,
                                    "channel element type is not Sendable",
                                );
                            }
                            Some(crate::ty::concurrency::channel_pair(ty))
                        } else {
                            None
                        };
                        return self.concurrent_call(
                            env,
                            module,
                            &def.name.value,
                            args,
                            explicit.as_ref().or(expected),
                            span,
                        );
                    }
                    if !env.shadow
                        && phase == PrimitivePhase::Runtime
                        && env.phase != Phase::Runtime
                    {
                        self.error(
                            Code::E0810,
                            callee.span,
                            "runtime primitive called in static computation",
                        );
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
                    let ty = self.constructor_type(
                        env,
                        path.unwrap_or_else(|| ril_source::ice!("constructor without path")),
                        expected,
                    );
                    return self.nominal_constructor(env, ty, args, span);
                }
                DefinitionKind::Function => {
                    let is_stdlib = self.hir.is_stdlib_file(def.name.span.file);
                    pending_meta =
                        self.is_meta_fn(id) && env.phase == Phase::Runtime && !env.shadow;
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
            } else {
                self.expect(env, arg.value, &param_ty);
            }
            if matches!(arg.mode, Mode::Mut | Mode::Shared | Mode::Ref)
                && self.types.get(&arg_span).is_some_and(Ty::is_value)
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
                && !pending_meta
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
            || call
                .effects
                .iter()
                .any(|eff| !matches!(eff.as_str(), "io" | "fiber"))
            || call
                .state
                .iter()
                .any(|clause| clause == "up" || clause.starts_with("up("))
        {
            self.invalidate_live(env, Code::E0533);
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
                    self.invalidate_live(env, Code::E0310);
                } else {
                    self.writes_place(env, argument.value);
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
            if let Some(intrinsic) = self.hir.intrinsic(known) {
                match intrinsic {
                    ril_hir::Intrinsic::ArraySort => {
                        if let Some(arg0) = args.first() {
                            let arg0_span = ast.expr(arg0.value).span;
                            let mut receiver =
                                self.types.get(&arg0_span).cloned().unwrap_or(Ty::Unknown);
                            receiver = self.normalize(&receiver);
                            if let Ty::Draft(inner) = receiver {
                                receiver = self.normalize(&inner);
                            }
                            if let Ty::Array(elem) = receiver {
                                let elem_ty = self.normalize(&elem.ty);
                                let orderable = matches!(
                                    &elem_ty,
                                    Ty::Int
                                        | Ty::F64
                                        | Ty::Str
                                        | Ty::Bytes
                                        | Ty::Unknown
                                        | Ty::Infer(_)
                                ) || matches!(&elem_ty, Ty::Param(id) if env
                                .domains
                                .get(id)
                                .is_some_and(|dom| dom.iter().all(|t| matches!(
                                    t,
                                    Ty::Int | Ty::F64 | Ty::Str | Ty::Bytes
                                ))));
                                if !orderable {
                                    self.error(
                                        Code::E0327,
                                        span,
                                        "Array::sort requires orderable elements",
                                    );
                                }
                            }
                        }
                    }
                    ril_hir::Intrinsic::SetEmpty | ril_hir::Intrinsic::SetFromArray => {
                        if let Ty::Set(elem) = self.normalize(&result)
                            && !self.eligible_key(env, &elem, &mut HashSet::new())
                        {
                            self.error(
                                Code::E0328,
                                span,
                                "set element type does not support stable equality",
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
        if !env.shadow && !generics.is_empty() {
            self.generic_arguments.insert(span, generics.clone());
        }
        if pending_meta && let Some(id) = def_id {
            self.stage_static_call(env, id, args, span);
        }
        let result = if (has_meta || !generics.is_empty())
            && !env.shadow
            && !pending_meta
            && env.phase == Phase::Runtime
        {
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

    fn nominal_constructor(&mut self, env: &mut Env, ty: Ty, args: &[Argument], span: Span) -> Ty {
        let Ty::Adt(adt) = &ty else {
            if ty != Ty::Unknown {
                self.error(Code::E0338, span, "type is not a payload constructor");
            }
            return Ty::Unknown;
        };
        if adt.kind == AdtKind::Foreign {
            self.error(Code::E0907, span, "foreign nominal cannot be constructed");
            return Ty::Unknown;
        }
        if adt.kind == AdtKind::Opaque && adt.defining_scope != env.scope {
            if self.hir.std_type(adt.definition) == Some(ril_hir::StdType::PanicInfo) {
                self.error(Code::E0301, span, "PanicInfo has no accessible constructor");
            } else {
                self.error(Code::E0308, span, "opaque constructor is sealed");
            }
            return Ty::Unknown;
        }
        let params = match self.representation(env, adt) {
            Some(Ty::Unit | Ty::Record(..)) | None => {
                self.error(
                    Code::E0338,
                    span,
                    "unit and record types do not use payload call syntax",
                );
                return Ty::Unknown;
            }
            Some(Ty::Tuple(fields)) => fields.into_iter().map(|m| m.ty).collect(),
            Some(one) => vec![one],
        };
        if self.check_tuple_payload(env, args, &params, span) {
            return ty;
        }
        if args.len() != params.len() {
            self.error(Code::E0314, span, "invalid constructor payload arity");
        }
        let single = params.len() == 1;
        for (arg, ty) in args.iter().zip(params) {
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
            self.expect(env, arg.value, &ty);
            if matches!(arg.mode, Mode::Mut | Mode::Shared | Mode::Ref)
                && self.types.get(&arg_span).is_some_and(Ty::is_value)
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
