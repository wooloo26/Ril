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
        self.verify_fn_return_proofs(env, value, span);
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
        // Closures may be invoked after outer live/var bindings are mutated; wipe all outer live facts.
        local
            .refinements
            .options
            .retain(|p, _| !self.live.contains(&p.root));
        local.refinements.dbm.forget_matching(|a| match a {
            crate::ty::dbm::Atom::Val(p) | crate::ty::dbm::Atom::Len(p) => {
                self.live.contains(&p.root)
            }
            _ => false,
        });
        local.refinements.call_proofs.clear();
        if params.iter().any(|param| param.mode == Mode::Via) {
            local.mode_scope = Some(true);
        }
        if env.phase == Phase::Runtime && params.iter().any(|param| param.is_meta) {
            local.staging_owner = Some(span);
        }
        local.expected_return = expected_call.map(|sig| sig.result.clone());
        local.inferred_return = None;
        local.return_scope = Some(self.ast(env.file).expr(body).span);
        local.return_proofs.clear();
        local.active_handler_return_proofs = None;
        let pending_cb_proofs = std::mem::take(&mut local.pending_closure_param_proofs);
        let pending_handler = local.pending_handler_proofs.take();
        local.checking_fn_tail = false;
        local.active_defers.clear();
        let mut parameters = Vec::new();
        let mut closure_param_ids: Vec<Option<ril_hir::DefinitionId>> = Vec::new();
        for (index, item) in params.iter().enumerate() {
            for &guard in &item.guards {
                if self.hir.is_static_proof_guard(env.file, guard) {
                    self.error(
                        Code::E0534,
                        self.ast(env.file).expr(guard).span,
                        "anonymous closure parameters cannot carry static proofs",
                    );
                }
            }
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
                let mut ids = Vec::new();
                self.collect_pattern_defs(&local, pattern, &mut ids);
                closure_param_ids.push(if let [only] = ids.as_slice() {
                    Some(*only)
                } else {
                    None
                });
                for id in &ids {
                    if let Some(bound_ty) = self.bindings.get(id).cloned() {
                        self.seed_type_invariants(
                            &mut local,
                            &crate::ty::dbm::Place::local(*id),
                            &bound_ty,
                        );
                    }
                }
                if let [param_id] = ids.as_slice() {
                    for p in pending_cb_proofs.iter().filter(|p| p.cb_param_idx == index) {
                        if let Ok(lowered) = self.lower_type_fn(p.tf_id) {
                            let mut scratch = local.refinements.dbm.clone();
                            let mut arg_vals = Vec::with_capacity(1 + p.extra.len());
                            arg_vals.push(crate::ty::proofs::ProofArgVal::Place(
                                crate::ty::dbm::Place::local(*param_id),
                            ));
                            let mut ok = true;
                            for opt in &p.extra {
                                if let Some(e) = opt {
                                    if let Some(v) = self.eval_callee_guard_arg(
                                        env,
                                        &mut scratch,
                                        p.def_file,
                                        *e,
                                        &p.formal_to_caller,
                                    ) {
                                        arg_vals.push(v);
                                    } else {
                                        ok = false;
                                        break;
                                    }
                                } else {
                                    arg_vals.push(crate::ty::proofs::ProofArgVal::Const(0));
                                }
                            }
                            if ok
                                && let Some(pred) = self.instantiate_proof_pred(
                                    &local,
                                    &mut scratch,
                                    &lowered.pred,
                                    &arg_vals,
                                )
                            {
                                scratch.assume(&pred);
                                scratch.forget_temps();
                                local.refinements.dbm = scratch;
                            }
                        }
                    }
                }
            } else if let Some(name) = &item.name {
                self.define_name(name, ty.clone());
                let resolved = self.resolve(name.span);
                closure_param_ids.push(resolved);
                if let Some(id) = resolved {
                    self.seed_type_invariants(&mut local, &crate::ty::dbm::Place::local(id), &ty);
                }
            } else {
                closure_param_ids.push(None);
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
        if let Some(pending) = &pending_handler {
            self.seed_handler_closure_proofs(&mut local, pending, &closure_param_ids);
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
        let (effects, effect_vars) = if obligations.effects.is_empty() {
            let mut used: Vec<_> = local
                .effects_seen
                .difference(&env.effects_seen)
                .cloned()
                .collect();
            used.sort();
            let mut vars: Vec<_> = local
                .effect_vars_seen
                .difference(&env.effect_vars_seen)
                .copied()
                .collect();
            vars.sort();
            (used, vars)
        } else {
            let row = self.effect_row_from_paths(&mut local, &obligations.effects);
            (row.concrete, row.vars)
        };
        Ty::Callable(Arc::new(Callable {
            parameters,
            result,
            effects,
            effect_vars,
            effect_infers: Vec::new(),
            open_effects: obligations.open_effects,
            direct_open_effects: obligations.direct_open_effects,
            ..unknown_callable()
        }))
    }

    pub(super) fn call(
        &mut self,
        env: &mut Env,
        call_expr: ExprId,
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
                            let insert_span = Span::new(span.file, span.start, span.start);
                            let fix = ril_source::fix::Fix {
                                id: format!("E0810:meta_prefix:{}:{}", span.file.0, span.start),
                                title: "Insert `meta ` prefix".to_owned(),
                                safety: ril_source::fix::FixSafety::Safe,
                                kind: ril_source::fix::FixKind::SyntaxForm,
                                is_preferred: true,
                                is_organize_imports: false,
                                edits: vec![ril_source::fix::TextEdit::new(insert_span, "meta ")],
                                delta: None,
                            };
                            self.error_diag(
                                ril_source::diag::Diagnostic::error(
                                    Code::E0810,
                                    callee.span,
                                    "calling a meta fn in runtime code requires 'meta'",
                                )
                                .with_fix(fix),
                            );
                        }
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
                    let insert_span = Span::new(callee.span.file, callee.span.end, callee.span.end);
                    let fix = ril_source::fix::Fix {
                        id: format!(
                            "E0338:nominal_wrap:{}:{}",
                            callee.span.file.0, callee.span.end
                        ),
                        title: "Insert `::` for nominal wrapper construction".to_owned(),
                        safety: ril_source::fix::FixSafety::Safe,
                        kind: ril_source::fix::FixKind::SyntaxForm,
                        is_preferred: true,
                        is_organize_imports: false,
                        edits: vec![ril_source::fix::TextEdit::new(insert_span, "::")],
                        delta: None,
                    };
                    self.error_diag(
                        ril_source::diag::Diagnostic::error(
                            Code::E0338,
                            callee.span,
                            "nominal construction requires 'Name::(...)' syntax",
                        )
                        .with_fix(fix),
                    );
                    return Ty::Unknown;
                }
                DefinitionKind::Function => {
                    let is_stdlib = self.hir.is_stdlib_file(def.name.span.file);
                    if !env.shadow && self.is_meta_fn(id) && env.phase == Phase::Runtime {
                        let insert_span = Span::new(span.file, span.start, span.start);
                        let fix = ril_source::fix::Fix {
                            id: format!("E0810:meta_prefix:{}:{}", span.file.0, span.start),
                            title: "Insert `meta ` prefix".to_owned(),
                            safety: ril_source::fix::FixSafety::Safe,
                            kind: ril_source::fix::FixKind::SyntaxForm,
                            is_preferred: true,
                            is_organize_imports: false,
                            edits: vec![ril_source::fix::TextEdit::new(insert_span, "meta ")],
                            delta: None,
                        };
                        self.error_diag(
                            ril_source::diag::Diagnostic::error(
                                Code::E0810,
                                callee.span,
                                "calling a meta fn in runtime code requires 'meta'",
                            )
                            .with_fix(fix),
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
        let mut arg_by_formal: Vec<Option<ExprId>> = vec![None; call.parameters.len()];
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
            if let Some(slot) = arg_by_formal.get_mut(index) {
                *slot = Some(arg.value);
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
                // D6: if passing an anonymous closure to a HOF parameter whose `CallableType`
                // carries static parameter proofs, seed those proofs into the closure's entry DBM.
                if !env.shadow
                    && matches!(
                        self.ast(env.file).expr(arg.value).value,
                        Expr::Closure { .. }
                    )
                    && let Some(callee_id) = def_id
                    && let Some(stmt) = self.hir.definition(callee_id).stmt
                {
                    let def_file = self.hir.definition(callee_id).name.span.file;
                    if let ril_syntax::syntax::StmtKind::Function(fun) =
                        &self.ast(def_file).stmt(stmt).value.kind
                        && let Some(fp) = fun.signature.params.get(index)
                        && let Some(ty_id) = fp.ty
                        && let ril_syntax::syntax::Type::Callable(cb_sig) =
                            &self.ast(def_file).ty(ty_id).value
                    {
                        let cb_sig = (**cb_sig).clone();
                        let mut formal_to_caller = std::collections::HashMap::new();
                        for (fidx, fparam) in fun.signature.params.iter().enumerate() {
                            if let Some(fname) = &fparam.name
                                && let Some(fid) = self.resolve(fname.span)
                                && let Some(Some(caller_arg)) = arg_by_formal.get(fidx)
                            {
                                formal_to_caller.insert(fid, *caller_arg);
                            }
                        }
                        for (cb_idx, cb_param) in cb_sig.params.iter().enumerate() {
                            for (tf_id, extra, _) in self.param_static_proofs(def_file, cb_param) {
                                env.pending_closure_param_proofs.push(
                                    crate::ty::check::PendingClosureParamProof {
                                        cb_param_idx: cb_idx,
                                        tf_id,
                                        extra,
                                        def_file,
                                        formal_to_caller: formal_to_caller.clone(),
                                    },
                                );
                            }
                        }
                    }
                }
                self.expect(env, arg.value, &param_ty);
                env.pending_closure_param_proofs.clear();
            }
            if matches!(arg.mode, Mode::Mut | Mode::Shared | Mode::Ref)
                && let Some(arg_ty) = self.types.get(&arg_span).cloned()
            {
                let is_ctl = self.is_ctl_ty(env, &arg_ty);
                let is_linear_root = self.is_linear_root_ty(env, &arg_ty);
                let is_user_linear = is_linear_root && !is_ctl;
                if is_ctl {
                    self.error(
                        Code::E0401,
                        arg_span,
                        "ctl continuation cannot carry live authority",
                    );
                } else if is_user_linear && arg.mode == Mode::Shared {
                    self.error(
                        Code::E0401,
                        arg_span,
                        "linear type cannot carry shared ^mut authority",
                    );
                } else if !is_user_linear && self.is_value_ty(env, &arg_ty) {
                    self.error(
                        Code::E0401,
                        arg_span,
                        "value-type argument cannot carry live authority",
                    );
                }
            }
            let expected_arg_mode = if parameter.mode == Mode::New {
                Mode::Plain
            } else {
                parameter.mode
            };
            if !parameter.is_meta && parameter.mode != Mode::Via && expected_arg_mode != arg.mode {
                let code = if arg.mode == Mode::Plain {
                    Code::E0405
                } else {
                    Code::E0406
                };
                let mut diag = ril_source::diag::Diagnostic::error(
                    code,
                    arg_span,
                    "required explicit argument mode does not match",
                );
                let mode_fix = if arg.mode == Mode::Plain {
                    expected_arg_mode.as_str().map(|mode_str| {
                        let (edit_span, replacement) = if let Some(pipe_span) = arg.pipe_span {
                            (
                                Span::new(pipe_span.file, pipe_span.end, pipe_span.end),
                                format!(" {mode_str}"),
                            )
                        } else {
                            (
                                Span::new(arg_span.file, arg_span.start, arg_span.start),
                                format!("{mode_str} "),
                            )
                        };
                        ril_source::fix::Fix {
                            id: format!(
                                "{}:call_mode:{}:{}",
                                code.as_str(),
                                edit_span.file.0,
                                edit_span.start
                            ),
                            title: format!("Insert `{mode_str}` mode marker"),
                            safety: ril_source::fix::FixSafety::Safe,
                            kind: ril_source::fix::FixKind::CallSiteMode,
                            is_preferred: true,
                            is_organize_imports: false,
                            edits: vec![ril_source::fix::TextEdit::new(edit_span, replacement)],
                            delta: None,
                        }
                    })
                } else if let Some(mode_span) = arg.mode_span {
                    if let Some(expected_str) = expected_arg_mode.as_str() {
                        Some(ril_source::fix::Fix {
                            id: format!(
                                "{}:call_mode:{}:{}",
                                code.as_str(),
                                mode_span.file.0,
                                mode_span.start
                            ),
                            title: format!("Replace mode marker with `{expected_str}`"),
                            safety: ril_source::fix::FixSafety::Safe,
                            kind: ril_source::fix::FixKind::CallSiteMode,
                            is_preferred: true,
                            is_organize_imports: false,
                            edits: vec![ril_source::fix::TextEdit::new(mode_span, expected_str)],
                            delta: None,
                        })
                    } else {
                        let file_text = self.hir.file(mode_span.file).source_text();
                        let remove_end =
                            file_text
                                .get(mode_span.end..)
                                .map_or(mode_span.end, |rest| {
                                    let ws: usize = rest
                                        .bytes()
                                        .take_while(|b| *b == b' ' || *b == b'\t')
                                        .count();
                                    mode_span.end + ws
                                });
                        let remove_span = Span::new(mode_span.file, mode_span.start, remove_end);
                        Some(ril_source::fix::Fix {
                            id: format!(
                                "{}:call_mode:{}:{}",
                                code.as_str(),
                                remove_span.file.0,
                                remove_span.start
                            ),
                            title: "Remove unnecessary mode marker".to_owned(),
                            safety: ril_source::fix::FixSafety::Safe,
                            kind: ril_source::fix::FixKind::CallSiteMode,
                            is_preferred: true,
                            is_organize_imports: false,
                            edits: vec![ril_source::fix::TextEdit::new(remove_span, "")],
                            delta: None,
                        })
                    }
                } else {
                    None
                };
                if let Some(fix) = mode_fix {
                    diag = diag.with_fix(fix);
                }
                self.error_diag(diag);
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
        let is_len_preserving = def_id.is_some_and(|id| self.is_length_preserving_callee(id));
        let is_array_push_or_insert = def_id.is_some_and(|id| {
            matches!(
                self.hir.intrinsic(id),
                Some(ril_hir::Intrinsic::ArrayPush | ril_hir::Intrinsic::ArrayInsert)
            )
        });
        let is_array_pop_or_remove = def_id.is_some_and(|id| {
            matches!(
                self.hir.intrinsic(id),
                Some(
                    ril_hir::Intrinsic::ArrayPop
                        | ril_hir::Intrinsic::ArrayPopFront
                        | ril_hir::Intrinsic::ArrayRemove
                )
            )
        });
        let is_array_clear = def_id.is_some_and(|id| self.is_array_clear_callee(id));
        let is_map_insert = def_id.is_some_and(|id| {
            matches!(
                self.hir.intrinsic(id),
                Some(ril_hir::Intrinsic::MapInsert | ril_hir::Intrinsic::MapReplace)
            ) || self.is_set_stdlib_callee(id, "insert")
        });
        let is_map_remove = def_id.is_some_and(|id| {
            self.hir.intrinsic(id) == Some(ril_hir::Intrinsic::MapRemove)
                || self.is_set_stdlib_callee(id, "remove")
        });
        let is_map_pop_entry = def_id
            .is_some_and(|id| self.hir.intrinsic(id) == Some(ril_hir::Intrinsic::MapPopEntry));
        let is_map_clear = def_id.is_some_and(|id| {
            self.is_map_clear_callee(id) || self.is_set_stdlib_callee(id, "clear")
        });
        // 1. Check static parameter proofs on pre-call DBM (mapped by formal index!).
        if !env.shadow
            && let Some(id) = def_id
        {
            if let Some(ctl_proof) = env.ctl_resume_proofs.get(&id).cloned() {
                if let Some(Some(resume_arg)) = arg_by_formal.first() {
                    let arg_span = self.ast(env.file).expr(*resume_arg).span;
                    self.verify_op_return_proof_expr(
                        env,
                        &ctl_proof,
                        *resume_arg,
                        arg_span,
                        "ctl continuation resume value does not satisfy effect operation static proof",
                    );
                }
            } else if let Some((cb_file, cb_sig)) = env.callback_param_sigs.get(&id).cloned() {
                for (cb_idx, cb_param) in cb_sig.params.iter().enumerate() {
                    let Some(Some(subject_expr)) = arg_by_formal.get(cb_idx) else {
                        continue;
                    };
                    for (tf_id, extra, guard_span) in self.param_static_proofs(cb_file, cb_param) {
                        let arg_span = self.ast(env.file).expr(*subject_expr).span;
                        let mut scratch = env.refinements.dbm.clone();
                        let mut arg_vals = Vec::with_capacity(1 + extra.len());
                        arg_vals.push(crate::ty::proofs::ProofArgVal::Expr(*subject_expr));
                        for opt in extra {
                            if let Some(e) = opt {
                                arg_vals.push(crate::ty::proofs::ProofArgVal::Expr(e));
                            } else {
                                arg_vals.push(crate::ty::proofs::ProofArgVal::Const(0));
                            }
                        }
                        self.verify_proof_obligation_with_scratch_code(
                            env,
                            &mut scratch,
                            tf_id,
                            &arg_vals,
                            arg_span,
                            guard_span,
                            "callback argument does not satisfy static proof",
                            Code::E0323,
                        );
                    }
                }
            } else {
                self.check_call_param_proofs(env, id, &arg_by_formal, span);
            }
        }
        if !env.shadow
            && let Some(id) = def_id
            && self
                .hir
                .is_stdlib_file(self.hir.definition(id).name.span.file)
            && self.hir.primitive_module(id) == Some("Prelude")
            && self.hir.definition(id).name.value == "assert"
            && let Some(cond_arg) = args.first()
        {
            self.relate(env, cond_arg.value, true);
        }
        // 2. Sound call invalidation (including plain args containing writable/shared member schemas!).
        if call.is_ctl
            || call.open_effects
            || call.direct_open_effects
            || !call.effect_vars.is_empty()
            || !call.effect_infers.is_empty()
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
            for argument in args {
                if matches!(argument.mode, Mode::Mut | Mode::Shared) {
                    self.writes_place(env, argument.value, span);
                }
            }
        } else if call.state.iter().any(|clause| clause == "^mut")
            || call
                .parameters
                .iter()
                .any(|p| matches!(p.mode, Mode::Mut | Mode::Shared))
        {
            for argument in args {
                let arg_ty = self
                    .types
                    .get(&ast.expr(argument.value).span)
                    .cloned()
                    .map(|t| self.normalize(&t));
                let has_shared_schema = arg_ty
                    .as_ref()
                    .is_some_and(Ty::contains_shared_member_schema);
                let has_writable_schema = arg_ty
                    .as_ref()
                    .is_some_and(Ty::contains_writable_member_schema);
                if argument.mode == Mode::Shared
                    || (argument.mode == Mode::Plain && has_shared_schema)
                {
                    self.invalidate_live(
                        env,
                        Code::E0310,
                        span,
                        crate::ty::NarrowDropCause::AliasingMut,
                    );
                } else if argument.mode == Mode::Mut {
                    if is_array_push_or_insert {
                        self.note_array_push(env, argument.value, span);
                    } else if is_array_pop_or_remove {
                        self.note_array_pop(env, argument.value, span);
                    } else if is_array_clear {
                        self.note_array_clear(env, argument.value, span);
                    } else if is_map_insert
                        && arg_by_formal.first().copied().flatten() == Some(argument.value)
                    {
                        self.note_map_insert(
                            env,
                            argument.value,
                            arg_by_formal.get(1).copied().flatten(),
                            span,
                        );
                    } else if is_map_remove
                        && arg_by_formal.first().copied().flatten() == Some(argument.value)
                    {
                        self.note_map_remove(
                            env,
                            argument.value,
                            arg_by_formal.get(1).copied().flatten(),
                            span,
                        );
                    } else if is_map_pop_entry
                        && arg_by_formal.first().copied().flatten() == Some(argument.value)
                    {
                        self.note_map_pop_entry(env, argument.value, span);
                    } else if is_map_clear
                        && arg_by_formal.first().copied().flatten() == Some(argument.value)
                    {
                        self.note_map_clear(env, argument.value, span);
                    } else if is_len_preserving {
                        self.writes_place_preserving_len(env, argument.value, span);
                    } else {
                        self.writes_place(env, argument.value, span);
                    }
                } else if argument.mode == Mode::Plain && has_writable_schema {
                    self.writes_place(env, argument.value, span);
                }
            }
        }
        // 3. Seed return static proofs AFTER call invalidation!
        if !env.shadow
            && let Some(id) = def_id
        {
            self.seed_call_return_proofs(env, id, &arg_by_formal, call_expr);
        }
        let (effects, effect_vars) = if (!call.effects.is_empty() || !call.effect_vars.is_empty())
            && let Some(id) = def_id
            && let Some(row) = self.call_effect_row(id, &generics)
        {
            if !row.concrete.is_empty() {
                self.effect_applications.insert(span, row.concrete.clone());
            }
            if !row.vars.is_empty() {
                self.effect_var_applications.insert(span, row.vars.clone());
            }
            (row.concrete, row.vars)
        } else {
            let row = self.normalize_effect_row(&crate::ty::EffectRow {
                concrete: call.effects.clone(),
                vars: call.effect_vars.clone(),
                infers: call.effect_infers.clone(),
                open: call.open_effects,
                direct_open: call.direct_open_effects,
            });
            (row.concrete, row.vars)
        };
        if !env.shadow {
            env.effects_seen.extend(effects);
            env.effect_vars_seen.extend(effect_vars);
        }
        if !env.shadow
            && let Some(known) = def_id
            && let Some(stmt) = self.hir.definition(known).stmt
            && let ril_syntax::syntax::StmtKind::Function(fun) = &self
                .ast(self.hir.definition(known).name.span.file)
                .stmt(stmt)
                .value
                .kind
        {
            let eff_checks: Vec<_> = fun
                .generics
                .iter()
                .filter(|g| g.is_effect && g.direct_only)
                .filter_map(|g| self.resolve(g.name.span))
                .collect();
            for pid in eff_checks {
                if let Some(crate::ty::GenericValue::Effects(row)) = generics.get(&pid) {
                    let norm = self.normalize_effect_row(row);
                    let has_ctl = norm.open
                        || norm.concrete.iter().any(|e| self.effect_label_has_ctl(e))
                        || norm
                            .vars
                            .iter()
                            .any(|v| !self.hir.is_direct_effect_param(*v));
                    if has_ctl {
                        self.error(
                            Code::E0616,
                            span,
                            "callable using ctl effect cannot instantiate ': fn' effect row parameter",
                        );
                    }
                }
            }
        }
        if let Some(known) = def_id {
            self.validate_generic_uses(env, known, &generics, span);
            if self.hir.intrinsic(known) == Some(ril_hir::Intrinsic::StringInspect) {
                if let Some(arg) = args.first() {
                    let arg_span = ast.expr(arg.value).span;
                    let first = self.types.get(&arg_span).cloned().unwrap_or(Ty::Unknown);
                    if arg.mode == Mode::Plain {
                        if self.is_must_consume_ty(env, &first) {
                            self.error(
                                Code::E0405,
                                arg_span,
                                "String::inspect cannot consume a must-consume value; pass ref for borrowable linear types",
                            );
                        }
                    } else if self.is_ctl_ty(env, &first) {
                        self.error(
                            Code::E0401,
                            arg_span,
                            "ctl continuation cannot carry live authority",
                        );
                    } else if self.is_value_ty(env, &first) && !self.is_must_consume_ty(env, &first)
                    {
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
        self.finalize(&result)
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
        if adt.kind == AdtKind::Opaque && adt.defining_scope != env.scope {
            for arg in args {
                self.expr(env, arg.value, None);
            }
            if self.hir.std_type(adt.definition) == Some(ril_hir::StdType::PanicReport) {
                self.error(
                    Code::E0301,
                    span,
                    "Panic::Report has no accessible constructor",
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
        let has_invariants = self.has_type_invariants(adt.definition);
        if has_invariants
            && let Some(ref rep_ty) = rep
            && self.contains_live_member_schema_deep(env, rep_ty, &mut HashSet::new())
        {
            self.error(
                Code::E0356,
                span,
                "type with static invariant cannot be instantiated with mutable, var, ref, or live member storage",
            );
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
            if !matches!(arg.mode, Mode::Plain | Mode::Ref | Mode::Shared) {
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
            if has_invariants && !env.shadow {
                self.verify_type_invariants(
                    env,
                    adt,
                    crate::ty::proofs::ProofArgVal::Expr(arg.value),
                    span,
                );
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
            if !matches!(arg.mode, Mode::Plain | Mode::Ref | Mode::Shared) {
                self.error(
                    Code::E0406,
                    arg_span,
                    "constructor argument has an unsupported access mode",
                );
            }
            let tuple_ty = Ty::Tuple(fields.clone());
            self.expect(env, arg.value, &tuple_ty);
            if has_invariants && !env.shadow {
                self.verify_type_invariants(
                    env,
                    adt,
                    crate::ty::proofs::ProofArgVal::Expr(arg.value),
                    span,
                );
            }
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
            {
                let is_ctl = self.is_ctl_ty(env, &arg_ty);
                let is_linear_root = self.is_linear_root_ty(env, &arg_ty);
                let is_user_linear = is_linear_root && !is_ctl;
                if is_ctl {
                    self.error(
                        Code::E0401,
                        arg_span,
                        "ctl continuation cannot carry live authority",
                    );
                } else if is_user_linear && arg.mode == Mode::Shared {
                    self.error(
                        Code::E0401,
                        arg_span,
                        "linear type cannot carry shared ^mut authority",
                    );
                } else if !is_user_linear && self.is_value_ty(env, &arg_ty) {
                    self.error(
                        Code::E0401,
                        arg_span,
                        "value-type argument cannot carry live authority",
                    );
                }
            }
        }
        if has_invariants && !env.shadow && !args.is_empty() {
            let subject = if single && let Some(first) = args.first() {
                crate::ty::proofs::ProofArgVal::Expr(first.value)
            } else {
                crate::ty::proofs::ProofArgVal::TupleExprs(args.iter().map(|a| a.value).collect())
            };
            self.verify_type_invariants(env, adt, subject, span);
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
