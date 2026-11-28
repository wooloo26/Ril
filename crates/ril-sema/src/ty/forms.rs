mod instantiate;
mod resolve;

use std::collections::HashSet;

use ril_hir::{DefinitionId, DefinitionKind, GuardKind};
use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::{
    self, GenericArg, GenericParam, Member as Coordinate, Mode, StateKind, StmtKind, Type,
    TypeDecl, TypeDefinition, TypeKind, Variant,
};

use super::{
    AdtKind, Callable, GenericValue, Member, Parameter, Ty, Value,
    check::{Checker, Env, Phase, path_name, transform},
};

pub(in crate::ty) fn is_value_generic_param(param: &GenericParam) -> bool {
    param
        .name
        .value
        .starts_with(|c: char| c.is_ascii_lowercase() || c == '_')
}

pub(in crate::ty) fn partition_type_fn_params(
    params: &[GenericParam],
) -> (&[GenericParam], Option<&GenericParam>, &[GenericParam]) {
    let v = params
        .iter()
        .take_while(|p| is_value_generic_param(p))
        .count();
    if v == 0 {
        return (params, None, &[]);
    }
    let (value_params, type_params) = params.split_at(v);
    let Some((subject, trailing)) = value_params.split_first() else {
        return (type_params, None, &[]);
    };
    (type_params, Some(subject), trailing)
}

fn ty_mentions_any_param(ty: &Ty, params: &HashSet<DefinitionId>) -> bool {
    if params.is_empty() {
        return false;
    }
    let mut found = false;
    let _ = transform(ty, &mut |node| {
        if let Ty::Param(id) = node
            && params.contains(id)
        {
            found = true;
        }
        None
    });
    found
}

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

    pub(super) fn check_guard(
        &mut self,
        env: &mut Env,
        guard: syntax::ExprId,
        subject: &Ty,
        output: &Ty,
        is_return: bool,
    ) {
        let original_span = self.ast(env.file).expr(guard).span;
        match self.hir.classify_guard(env.file, guard) {
            GuardKind::StaticProof(id) => {
                self.check_static_proof_guard(env, guard, id, subject);
            }
            GuardKind::StaticProofPrimitive(id) => {
                let name = self.hir.definition(id).name.value.as_str();
                if matches!(name, "Reflects" | "Implies" | "Ensures") {
                    if !is_return {
                        self.error(
                            Code::E0306,
                            original_span,
                            format!("{name} is only valid on function return types"),
                        );
                        return;
                    }
                    if matches!(name, "Reflects" | "Implies")
                        && self.normalize(subject) != Ty::Bool
                        && self.normalize(subject) != Ty::Unknown
                    {
                        self.error(
                            Code::E0306,
                            original_span,
                            format!("{name} requires a bool return type"),
                        );
                    }
                    let ast = self.ast(env.file);
                    match &ast.expr(guard).value {
                        syntax::Expr::Call { .. } => {
                            self.error(
                                Code::E0306,
                                original_span,
                                format!(
                                    "{name} uses angle brackets `<...>` rather than call parentheses `(...)`"
                                ),
                            );
                        }
                        syntax::Expr::Path(path) => {
                            let valid = path.segments.last().is_some_and(|seg| {
                                matches!(seg.arguments.as_slice(), [GenericArg::Value(_)])
                                    || matches!(
                                        seg.arguments.as_slice(),
                                        [GenericArg::Type(ty_id)]
                                            if matches!(ast.ty(*ty_id).value, Type::Named(_))
                                    )
                            });
                            if !valid {
                                self.error(
                                    Code::E0314,
                                    original_span,
                                    format!(
                                        "{name} requires exactly one predicate argument in `<...>`"
                                    ),
                                );
                            }
                        }
                        _ => {
                            self.error(
                                Code::E0314,
                                original_span,
                                format!(
                                    "{name} requires exactly one predicate argument in `<...>`"
                                ),
                            );
                        }
                    }
                }
            }
            GuardKind::RuntimeFn(id) => {
                self.check_runtime_fn_guard(env, guard, id, subject, output);
            }
            GuardKind::Invalid => {
                self.error(
                    Code::E0306,
                    original_span,
                    "signature guard must be a function or proof type function",
                );
            }
        }
    }

    pub(in crate::ty) fn check_static_proof_guard(
        &mut self,
        env: &mut Env,
        guard: syntax::ExprId,
        id: DefinitionId,
        subject: &Ty,
    ) {
        let ast = self.ast(env.file);
        let original = ast.expr(guard);
        let span = original.span;
        let mut node = original;
        let mut pipe_ref = false;
        if let syntax::Expr::Unary { op, value } = &node.value
            && op.value == "ref"
        {
            pipe_ref = true;
            node = ast.expr(*value);
        }
        if pipe_ref {
            self.error(
                Code::E0406,
                span,
                "static proof guard does not take 'ref' mode prefix",
            );
        }
        if matches!(&node.value, syntax::Expr::Call { .. }) {
            self.error(
                Code::E0306,
                span,
                "static proof type functions use angle brackets `<...>` rather than call parentheses `(...)`",
            );
            return;
        }
        let syntax::Expr::Path(path) = &node.value else {
            return;
        };
        let angle_args: Vec<GenericArg> = path
            .segments
            .last()
            .map(|s| s.arguments.clone())
            .unwrap_or_default();
        self.check_static_proof_args(env, id, &angle_args, span, subject);
    }

    pub(in crate::ty) fn check_static_proof_args(
        &mut self,
        env: &mut Env,
        id: DefinitionId,
        angle_args: &[GenericArg],
        span: Span,
        subject: &Ty,
    ) {
        let def = self.hir.definition(id);
        let Some(stmt) = def.stmt else { return };
        let def_file = def.name.span.file;
        let def_scope = def.scope;
        let StmtKind::Type(decl) = &self.ast(def_file).stmt(stmt).value.kind else {
            self.error(Code::E0306, span, "static proof requires a type function");
            return;
        };
        let TypeDefinition::Function(tf_params, tf_body) = &decl.definition else {
            self.error(Code::E0306, span, "static proof requires a type function");
            return;
        };
        let tf_params = tf_params.clone();
        let tf_body = *tf_body;
        let (type_params, Some(subject_param), trailing_params) =
            partition_type_fn_params(&tf_params)
        else {
            self.error(
                Code::E0306,
                span,
                "static value proof requires a type function with a value subject parameter",
            );
            return;
        };
        let mut tf_env = Env::new(def_file, def_scope);
        tf_env.phase = Phase::TypeEval;
        tf_env.caller_scope = Some(env.effective_scope());
        tf_env.error_span = Some(span);

        // Style A `<...>` argument order: trailing value args first, followed by optional explicit type args.
        let value_arg_count = angle_args.len().min(trailing_params.len());
        let explicit_type_args = angle_args.get(value_arg_count..).unwrap_or(&[]);
        if explicit_type_args.len() > type_params.len() {
            self.error(Code::E0340, span, "too many arguments for static proof");
        }
        let mut subst = std::collections::HashMap::new();
        let mut type_param_ids = Vec::new();
        for (idx, tp) in type_params.iter().enumerate() {
            let Some(pid) = self.resolve(tp.name.span) else {
                continue;
            };
            let gv = if let Some(arg) = explicit_type_args.get(idx) {
                self.generic_argument(env, tp, arg, span)
            } else {
                GenericValue::Type(self.fresh())
            };
            subst.insert(pid, gv.clone());
            tf_env.generics.insert(pid, gv);
            type_param_ids.push((idx, pid));
        }

        // Bind subject type (if it depends on an uninferred trailing type param via a
        // type function like `InKey<C>`, `subject_param_ty` evaluates to `Ty::Unknown` here
        // and will be re-evaluated once trailing arguments resolve `tf_env.generics`).
        let subject_param_ty = subject_param
            .bound
            .first()
            .map(|&ty| self.type_expr(&mut tf_env, ty))
            .unwrap_or(Ty::Unknown);
        let subject_deferred = subject_param_ty == Ty::Unknown && !subject_param.bound.is_empty();
        if !subject_deferred {
            let expected_subject = super::check::substitute(&subject_param_ty, &subst);
            self.require(env, span, subject, &expected_subject);
        }

        // Bind trailing value arguments from `<...>`.
        for (idx, param) in trailing_params.iter().enumerate() {
            if let Some(arg) = angle_args.get(idx) {
                let GenericArg::Value(arg_expr) = arg else {
                    self.error(
                        Code::E0314,
                        span,
                        "expected value argument for static proof parameter",
                    );
                    continue;
                };
                let arg_span = self.ast(env.file).expr(*arg_expr).span;
                let param_ty = param
                    .bound
                    .first()
                    .map(|&ty| self.type_expr(&mut tf_env, ty))
                    .unwrap_or(Ty::Unknown);
                let expected_arg = super::check::substitute(&param_ty, &subst);
                let mut arg_env = env.clone();
                arg_env.shadow = true;
                arg_env.effects_seen.clear();
                let _ = self.expect(&mut arg_env, *arg_expr, &expected_arg);
                if !arg_env.effects_seen.is_empty() {
                    self.error(
                        Code::E0409,
                        arg_span,
                        "static proof argument expression must be pure",
                    );
                }
            } else if param.default.is_none() {
                self.error(Code::E0314, span, "missing required static proof argument");
            }
        }

        // Validate deduced type parameters (domain bounds & static checks like `T |> LenTarget`).
        for (idx, pid) in type_param_ids {
            let Some(tp) = type_params.get(idx) else {
                continue;
            };
            if let Some(GenericValue::Type(actual)) = subst.get(&pid) {
                let actual = self.normalize(actual);
                tf_env
                    .generics
                    .insert(pid, GenericValue::Type(actual.clone()));
                if matches!(actual, Ty::Infer(_)) {
                    self.error(
                        Code::E0344,
                        span,
                        format!(
                            "could not infer type parameter {} of static proof {}",
                            tp.name.value, def.name.value
                        ),
                    );
                    continue;
                }
                let prev_open = tf_env.allow_open_record;
                tf_env.allow_open_record = true;
                let domain: Vec<_> = tp
                    .bound
                    .iter()
                    .map(|&ty| self.type_expr(&mut tf_env, ty))
                    .collect();
                tf_env.allow_open_record = prev_open;
                let allowed = domain.is_empty()
                    || domain
                        .iter()
                        .any(|ty| matches!(ty, Ty::Unknown | Ty::Mode | Ty::TypeValue(None)))
                    || match &actual {
                        Ty::Param(actual_id) => env.domains.get(actual_id).is_some_and(|ad| {
                            ad.iter()
                                .all(|a| domain.iter().any(|ok| self.fits(env, a, ok)))
                        }),
                        _ => domain.iter().any(|ok| self.fits(env, &actual, ok)),
                    };
                if !allowed {
                    self.error(
                        Code::E0306,
                        span,
                        format!(
                            "{} does not satisfy the domain of {}",
                            actual.display(self.hir),
                            tp.name.value
                        ),
                    );
                }
                self.validate_static_checks(&mut tf_env, tp, &GenericValue::Type(actual), span);
            }
        }
        if subject_deferred {
            let subject_param_ty = subject_param
                .bound
                .first()
                .map(|&ty| self.type_expr(&mut tf_env, ty))
                .unwrap_or(Ty::Unknown);
            if subject_param_ty != Ty::Unknown {
                self.require(env, span, subject, &subject_param_ty);
            }
        }

        // Validate that the Type Function body returns only `<()>` / `<never>`.
        let mut seen = HashSet::new();
        self.check_static_proof_shape(id, def_file, tf_body, span, &mut seen);
    }

    fn check_static_proof_shape(
        &mut self,
        tf_id: DefinitionId,
        file: ril_source::span::FileId,
        expr: syntax::ExprId,
        report_span: Span,
        seen: &mut HashSet<DefinitionId>,
    ) {
        if !seen.insert(tf_id) {
            return;
        }
        // Ensure the type function's statement has been typechecked so `self.types` is populated.
        if let Some(stmt) = self.hir.definition(tf_id).stmt {
            let body_span = self.ast(file).expr(expr).span;
            if !self.types.contains_key(&body_span) {
                let def = self.hir.definition(tf_id);
                let mut check_env = Env::new(def.name.span.file, def.scope);
                self.statement(&mut check_env, stmt, false);
            }
        }
        self.check_proof_return_branches(file, expr, report_span, seen);
    }

    fn check_proof_return_branches(
        &mut self,
        file: ril_source::span::FileId,
        expr: syntax::ExprId,
        report_span: Span,
        seen: &mut HashSet<DefinitionId>,
    ) {
        let ast = self.ast(file);
        let node = ast.expr(expr);
        match &node.value {
            syntax::Expr::Block { statements, .. } => {
                if let Some(&last) = statements.last()
                    && let StmtKind::Expr(tail) = ast.stmt(last).value.kind
                {
                    self.check_proof_return_branches(file, tail, report_span, seen);
                }
            }
            syntax::Expr::If { yes, no, .. } => {
                let then_b = *yes;
                let else_b = *no;
                self.check_proof_return_branches(file, then_b, report_span, seen);
                if let Some(eb) = else_b {
                    self.check_proof_return_branches(file, eb, report_span, seen);
                }
            }
            syntax::Expr::Match { arms, .. } => {
                let bodies: Vec<_> = arms.iter().map(|a| a.body).collect();
                for body in bodies {
                    self.check_proof_return_branches(file, body, report_span, seen);
                }
            }
            syntax::Expr::Quote(ty_id) => match &ast.ty(*ty_id).value {
                Type::Unit => {}
                Type::Named(path)
                    if matches!(
                        path.segments.as_slice(),
                        [seg] if seg.name.value == "never" && seg.arguments.is_empty()
                    ) => {}
                Type::Named(path) => {
                    if let Some(target_id) = self.resolve(path.span)
                        && let Some(stmt) = self.hir.definition(target_id).stmt
                        && let StmtKind::Type(decl) = &self
                            .ast(self.hir.definition(target_id).name.span.file)
                            .stmt(stmt)
                            .value
                            .kind
                        && let TypeDefinition::Function(_, target_body) = decl.definition
                    {
                        let target_file = self.hir.definition(target_id).name.span.file;
                        self.check_static_proof_shape(
                            target_id,
                            target_file,
                            target_body,
                            report_span,
                            seen,
                        );
                    } else {
                        self.error(
                            Code::E0306,
                            report_span,
                            "static value proof must return <()> or <never>",
                        );
                    }
                }
                _ => {
                    self.error(
                        Code::E0306,
                        report_span,
                        "static value proof must return <()> or <never>",
                    );
                }
            },
            _ => {
                let ty = self
                    .types
                    .get(&node.span)
                    .cloned()
                    .map(|t| self.normalize(&t));
                match ty {
                    Some(Ty::Never | Ty::Unknown | Ty::TypeValue(None)) => {}
                    Some(Ty::TypeValue(Some(inner)))
                        if matches!(*inner, Ty::Unit | Ty::Never | Ty::Unknown) => {}
                    _ => {
                        self.error(
                            Code::E0306,
                            report_span,
                            "static value proof must return <()> or <never>",
                        );
                    }
                }
            }
        }
    }

    fn check_runtime_fn_guard(
        &mut self,
        env: &mut Env,
        guard: syntax::ExprId,
        id: DefinitionId,
        subject: &Ty,
        output: &Ty,
    ) {
        let ast = self.ast(env.file);
        let original = ast.expr(guard);
        let mut node = original;
        if let syntax::Expr::Unary { op, value } = &node.value
            && op.value == "ref"
        {
            node = ast.expr(*value);
        }
        let mut extra_args: Vec<syntax::Argument> = Vec::new();
        if let syntax::Expr::Call { callee, args } = &node.value {
            extra_args = args.clone();
            node = ast.expr(*callee);
        }
        let _ = node;
        let signature = self.declare_function(id);
        let mut fresh_generics = std::collections::HashMap::new();
        if let Some(stmt) = self.hir.definition(id).stmt
            && let StmtKind::Function(fun) = &self
                .ast(self.hir.definition(id).name.span.file)
                .stmt(stmt)
                .value
                .kind
        {
            for param in &fun.generics {
                if let Some(pid) = self.resolve(param.name.span) {
                    fresh_generics.insert(pid, GenericValue::Type(self.fresh()));
                }
            }
        }
        if signature.open_effects
            || signature.open_state
            || !signature.effects.is_empty()
            || !signature.state.is_empty()
        {
            self.error(Code::E0409, original.span, "signature guard must be pure");
        }
        let expected_extra = signature.parameters.len().saturating_sub(1);
        let required_extra = signature
            .parameters
            .iter()
            .skip(1)
            .filter(|p| !p.optional)
            .count();
        if extra_args.len() < required_extra || extra_args.len() > expected_extra {
            self.error(
                Code::E0314,
                original.span,
                "signature guard argument count does not match",
            );
        }
        if let Some(first_param) = signature.parameters.first() {
            let expected_subject = super::check::substitute(&first_param.ty, &fresh_generics);
            self.require(env, original.span, subject, &expected_subject);
        }
        for (arg, param) in extra_args.iter().zip(signature.parameters.iter().skip(1)) {
            let expected_arg = super::check::substitute(&param.ty, &fresh_generics);
            self.expect(env, arg.value, &expected_arg);
        }
        let guard_result = super::check::substitute(&signature.result, &fresh_generics);
        let compatible = if let Some(inner) = guard_result.as_option(self.hir)
            && *inner == Ty::Unit
        {
            output.is_option(self.hir)
        } else if let Some((ok, err)) = guard_result.as_result(self.hir)
            && *ok == Ty::Unit
        {
            output.as_result(self.hir).is_some_and(|(_, expected)| {
                self.fits(env, err, expected) || self.sum_subset(env, err, expected)
            })
        } else if guard_result == Ty::Unknown {
            return;
        } else {
            self.error(
                Code::E0712,
                original.span,
                "signature guard must return fallible unit",
            );
            return;
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
        // Pass 1: register non-value (type/mode) parameter domains first so leading
        // value parameters (Style A) may reference trailing type parameters.
        for param in params {
            if is_value_generic_param(param) {
                continue;
            }
            if let Some(id) = self.resolve(param.name.span)
                && !env.generics.contains_key(&id)
            {
                let prev_open = env.allow_open_record;
                env.allow_open_record = true;
                let domain: Vec<_> = param
                    .bound
                    .iter()
                    .map(|&ty| self.type_expr(env, ty))
                    .collect();
                env.allow_open_record = prev_open;
                if !domain.is_empty() {
                    env.domains.insert(id, domain);
                }
            }
        }
        // Pass 2: resolve value parameter types.
        for param in params {
            if !is_value_generic_param(param) {
                continue;
            }
            if let Some(id) = self.resolve(param.name.span) {
                let ty = param
                    .bound
                    .first()
                    .map(|&ty| self.type_expr(env, ty))
                    .unwrap_or(Ty::Unknown);
                self.bindings.insert(id, ty);
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
        // 2-pass parameter resolution so proof-typed parameters (e.g., `k: In(m)` or
        // `i: InBounds(xs)`) can reference sibling parameters even when declared earlier.
        let enclosing = env.mode_scope.take();
        let mut resolved_tys: Vec<Option<Ty>> = vec![None; signature.params.len()];
        let mut saved_bindings: Vec<(DefinitionId, Option<Ty>)> = Vec::new();
        for (idx, param) in signature.params.iter().enumerate() {
            if let Some(ty_id) = param.ty {
                let is_proof_ty = self.bare_proof_type_info(env.file, ty_id).is_some();
                if !is_proof_ty {
                    let prev_open = env.allow_open_record;
                    env.allow_open_record = named;
                    let resolved = self.type_expr(env, ty_id);
                    env.allow_open_record = prev_open;
                    if let Some(name) = &param.name
                        && let Some(pid) = self.resolve(name.span)
                    {
                        let prev = self.bindings.insert(pid, resolved.clone());
                        saved_bindings.push((pid, prev));
                    }
                    if let Some(slot) = resolved_tys.get_mut(idx) {
                        *slot = Some(resolved);
                    }
                }
            }
        }
        for (idx, param) in signature.params.iter().enumerate() {
            if resolved_tys.get(idx).and_then(Option::as_ref).is_some() {
                continue;
            }
            let resolved = if let Some(ty_id) = param.ty {
                if let Some((tf_id, angle_args, span)) = self.bare_proof_type_info(env.file, ty_id)
                {
                    self.static_proof_subject_type(env, tf_id, &angle_args, span)
                        .unwrap_or_else(|| {
                            self.error(
                                Code::E0544,
                                span,
                                "static proof does not uniquely determine the parameter type",
                            );
                            Ty::Unknown
                        })
                } else {
                    Ty::Unknown
                }
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
            if let Some(name) = &param.name
                && let Some(pid) = self.resolve(name.span)
            {
                let prev = self.bindings.insert(pid, resolved.clone());
                saved_bindings.push((pid, prev));
            }
            if let Some(slot) = resolved_tys.get_mut(idx) {
                *slot = Some(resolved);
            }
        }
        let params: Vec<_> = signature
            .params
            .iter()
            .zip(resolved_tys)
            .map(|(param, ty_opt)| {
                let ty = ty_opt.unwrap_or(Ty::Unknown);
                if param.is_meta {
                    self.declare_meta_key(env, param);
                }
                let is_ctl = self.is_ctl_ty(env, &ty);
                let is_linear_root = self.is_linear_root_ty(env, &ty);
                let is_user_linear = is_linear_root && !is_ctl;
                if matches!(param.mode, Mode::Ref | Mode::Mut | Mode::Shared)
                    && (is_ctl
                        || (is_user_linear && param.mode == Mode::Shared)
                        || (!is_user_linear && self.is_value_ty(env, &ty)))
                {
                    let span = param.name.as_ref().map_or_else(
                        || self.ast(env.file).ty(signature.result).span,
                        |name| name.span,
                    );
                    self.error(
                        Code::E0401,
                        span,
                        if is_ctl {
                            "ctl continuation is linear and cannot carry an access mode"
                        } else if is_user_linear {
                            "linear type cannot carry shared ^mut access"
                        } else {
                            "value-type parameter cannot carry live access"
                        },
                    );
                }
                if param.mode == Mode::New && is_linear_root {
                    let span = param.name.as_ref().map_or_else(
                        || self.ast(env.file).ty(signature.result).span,
                        |name| name.span,
                    );
                    self.error(
                        Code::E0411,
                        span,
                        if is_ctl {
                            "ctl continuation is linear and does not use new mode"
                        } else {
                            "linear type does not use new mode"
                        },
                    );
                }
                if param.mode == Mode::Via && (self.is_value_only_ty(env, &ty) || is_linear_root) {
                    let span = param.name.as_ref().map_or_else(
                        || {
                            param.ty.map_or_else(
                                || self.ast(env.file).ty(signature.result).span,
                                |ty| self.ast(env.file).ty(ty).span,
                            )
                        },
                        |name| name.span,
                    );
                    self.error(
                        Code::E0550,
                        span,
                        if is_ctl {
                            "via is invalid on a mode-free ctl continuation parameter"
                        } else if is_user_linear {
                            "via is invalid on a linear parameter"
                        } else {
                            "via is redundant on a value-type parameter"
                        },
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
        let result = if let Some((tf_id, angle_args, span)) =
            self.bare_proof_type_info(env.file, signature.result)
        {
            self.static_proof_subject_type(env, tf_id, &angle_args, span)
                .unwrap_or_else(|| {
                    self.error(
                        Code::E0544,
                        span,
                        "static proof does not uniquely determine the return type",
                    );
                    Ty::Unknown
                })
        } else {
            self.type_expr(env, signature.result)
        };
        for (pid, prev) in saved_bindings.into_iter().rev() {
            if let Some(old) = prev {
                self.bindings.insert(pid, old);
            } else {
                self.bindings.remove(&pid);
            }
        }
        env.mode_scope = enclosing;
        let effects = signature
            .obligations
            .effects
            .iter()
            .map(|path| self.effect_label(env, path))
            .collect();
        let mut state = Vec::new();
        for clause in &signature.obligations.state {
            let name = match clause.kind {
                StateKind::Share => "^mut",
                StateKind::Capture => "capture",
                StateKind::Environment => "up",
                StateKind::Return => "return",
            };
            if clause.bindings.is_empty() {
                state.push(name.into());
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
                state.push(format!("{name}({bindings})"));
            }
        }
        if !named && signature.is_ctl && env.phase != Phase::Runtime && !env.shadow {
            self.error(
                Code::E0810,
                self.ast(env.file).ty(signature.result).span,
                "ctl(...) continuation types are prohibited in static evaluation",
            );
        }
        if matches!(signature.result_mode, Mode::New | Mode::Ref | Mode::Shared)
            && self.is_linear_root_ty(env, &result)
        {
            self.error(
                Code::E0546,
                self.ast(env.file).ty(signature.result).span,
                "linear type cannot carry a return access mode",
            );
        }
        let callable = Callable {
            is_ctl: !named && signature.is_ctl,
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

    pub(in crate::ty) fn bare_proof_type_info(
        &self,
        file: ril_source::span::FileId,
        ty_id: syntax::TypeId,
    ) -> Option<(DefinitionId, Vec<GenericArg>, Span)> {
        let node = self.ast(file).ty(ty_id);
        let Type::Named(path) = &node.value else {
            return None;
        };
        let id = self.resolve(path.span)?;
        let def = self.hir.definition(id);
        let stmt = def.stmt?;
        let def_file = def.name.span.file;
        let StmtKind::Type(decl) = &self.ast(def_file).stmt(stmt).value.kind else {
            return None;
        };
        let TypeDefinition::Function(tf_params, _) = &decl.definition else {
            return None;
        };
        let (_, Some(_), _) = partition_type_fn_params(tf_params) else {
            return None;
        };
        let angle_args = path
            .segments
            .last()
            .map(|s| s.arguments.clone())
            .unwrap_or_default();
        Some((id, angle_args, node.span))
    }

    fn guard_parameter(&mut self, env: &Env, guard: syntax::ExprId) -> Ty {
        let ast = self.ast(env.file);
        let mut node = ast.expr(guard);
        if let syntax::Expr::Unary { op, value } = &node.value
            && op.value == "ref"
        {
            node = ast.expr(*value);
        }
        if let syntax::Expr::Call { callee, .. } = &node.value {
            node = ast.expr(*callee);
        }
        let node_span = node.span;
        match self.hir.classify_guard(env.file, guard) {
            GuardKind::RuntimeFn(id) => {
                let call = self.declare_function(id);
                if let Some(param) = call.parameters.first() {
                    return param.ty.clone();
                }
            }
            GuardKind::StaticProof(id) => {
                let angle_args: Vec<GenericArg> = match &node.value {
                    syntax::Expr::Path(path) => path
                        .segments
                        .last()
                        .map(|s| s.arguments.clone())
                        .unwrap_or_default(),
                    _ => Vec::new(),
                };
                if let Some(inferred) =
                    self.static_proof_subject_type(env, id, &angle_args, node_span)
                {
                    return inferred;
                }
            }
            _ => {}
        }
        self.error(
            Code::E0544,
            node_span,
            "first guard does not determine the parameter type",
        );
        Ty::Unknown
    }

    pub(in crate::ty) fn static_proof_subject_type(
        &mut self,
        env: &Env,
        id: DefinitionId,
        angle_args: &[GenericArg],
        span: Span,
    ) -> Option<Ty> {
        if !self.resolving.insert(id) {
            return None;
        }
        let result = (|| {
            let def = self.hir.definition(id);
            let stmt = def.stmt?;
            let def_file = def.name.span.file;
            let StmtKind::Type(decl) = &self.ast(def_file).stmt(stmt).value.kind else {
                return None;
            };
            let TypeDefinition::Function(tf_params, _) = &decl.definition else {
                return None;
            };
            let tf_params = tf_params.clone();
            let (type_params, Some(subject_param), trailing_params) =
                partition_type_fn_params(&tf_params)
            else {
                return None;
            };
            let mut tf_env = Env::new(def_file, def.scope);
            tf_env.phase = Phase::TypeEval;
            tf_env.caller_scope = Some(env.effective_scope());
            let mut caller_env = env.clone();
            caller_env.shadow = true;
            let value_arg_count = angle_args.len().min(trailing_params.len());
            let explicit_type_args = angle_args.get(value_arg_count..).unwrap_or(&[]);
            let mut subst = std::collections::HashMap::new();
            let mut type_param_ids = Vec::new();
            for (idx, tp) in type_params.iter().enumerate() {
                let Some(pid) = self.resolve(tp.name.span) else {
                    continue;
                };
                let gv = if let Some(arg) = explicit_type_args.get(idx) {
                    self.generic_argument(&mut caller_env, tp, arg, span)
                } else {
                    GenericValue::Type(self.fresh())
                };
                subst.insert(pid, gv.clone());
                tf_env.generics.insert(pid, gv);
                type_param_ids.push(pid);
            }
            // Match trailing value arguments (e.g., `m` in `In<m>` or `xs` in `InBounds<xs>`)
            // so trailing type parameters like `C` in `In = \key: InKey<C>, c: C, C` can be deduced.
            for (idx, param) in trailing_params.iter().enumerate() {
                if let Some(GenericArg::Value(arg_expr)) = angle_args.get(idx) {
                    let param_ty = param
                        .bound
                        .first()
                        .map(|&ty| self.type_expr(&mut tf_env, ty))
                        .unwrap_or(Ty::Unknown);
                    let expected_arg = super::check::substitute(&param_ty, &subst);
                    let mut arg_env = caller_env.clone();
                    arg_env.shadow = true;
                    let _ = self.expect(&mut arg_env, *arg_expr, &expected_arg);
                }
            }
            let mut unbound = HashSet::new();
            for pid in type_param_ids {
                if let Some(GenericValue::Type(actual)) = subst.get(&pid) {
                    let norm = self.normalize(actual);
                    if matches!(norm, Ty::Infer(_)) {
                        unbound.insert(pid);
                    } else {
                        tf_env.generics.insert(pid, GenericValue::Type(norm));
                    }
                }
            }
            let ty = subject_param
                .bound
                .first()
                .map(|&t| self.type_expr(&mut tf_env, t))?;
            let ty = self.normalize(&ty);
            if ty == Ty::Unknown
                || matches!(ty, Ty::Infer(_))
                || ty_mentions_any_param(&ty, &unbound)
            {
                None
            } else {
                Some(ty)
            }
        })();
        self.resolving.remove(&id);
        result
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
                    let variant_name = match field {
                        Coordinate::Name(name) => Some(name.value.clone()),
                        Coordinate::Computed(expr) => {
                            let mut meta_env = env.clone();
                            meta_env.phase = Phase::MetaValue;
                            match self.eval_root(&meta_env, *expr, false) {
                                Some(Value::Str(s)) => Some(s),
                                Some(_) => {
                                    self.error(
                                        Code::E0324,
                                        span,
                                        "sum variant projection requires a string variant name",
                                    );
                                    return Ty::Unknown;
                                }
                                None => None,
                            }
                        }
                        Coordinate::Index(_) => None,
                    };
                    if let Some(variant_name) = variant_name {
                        let variants = self.sum_variants(adt);
                        if let Some(payload) = variants.get(&variant_name) {
                            return match payload.as_slice() {
                                [] => Ty::Unit,
                                [one] => one.clone(),
                                many => {
                                    Ty::Tuple(many.iter().cloned().map(Member::plain).collect())
                                }
                            };
                        }
                        self.error(
                            Code::E0336,
                            span,
                            format!("unknown sum variant {variant_name}"),
                        );
                        return Ty::Unknown;
                    }
                }
                _ => {}
            }
        }
        let coordinate = match field {
            Coordinate::Name(name) => Some(Value::Str(name.value.clone())),
            Coordinate::Index(name) => name.value.parse().ok().map(Value::Int),
            Coordinate::Computed(expr) => {
                let mut meta_env = env.clone();
                meta_env.phase = Phase::MetaValue;
                self.eval_root(&meta_env, *expr, false)
            }
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
            matches!(def.kind, DefinitionKind::Primitive(_)) && def.name.value == "KeyOf"
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

    pub(in crate::ty) fn is_must_consume_ty(&mut self, env: &Env, ty: &Ty) -> bool {
        self.is_must_consume_ty_inner(env, ty)
    }

    fn is_must_consume_ty_inner(&mut self, env: &Env, ty: &Ty) -> bool {
        match self.normalize(ty) {
            Ty::Callable(c) => c.is_ctl,
            Ty::Array(member) => self.is_must_consume_ty_inner(env, &member.ty),
            Ty::Map(key, member) => {
                self.is_must_consume_ty_inner(env, &key)
                    || self.is_must_consume_ty_inner(env, &member.ty)
            }
            Ty::Tuple(items) => items
                .iter()
                .any(|item| self.is_must_consume_ty_inner(env, &item.ty)),
            Ty::Record(fields, _) => fields
                .values()
                .any(|field| self.is_must_consume_ty_inner(env, &field.ty)),
            Ty::Adt(adt) => {
                if adt.is_linear {
                    return true;
                }
                if !self.must_consume_active.insert(adt.definition) {
                    return false;
                }
                let result = if matches!(adt.kind, AdtKind::Sum | AdtKind::OpaqueSum) {
                    self.sum_variants(&adt)
                        .values()
                        .flatten()
                        .any(|payload| self.is_must_consume_ty_inner(env, payload))
                } else {
                    self.representation(env, &adt)
                        .is_some_and(|rep| self.is_must_consume_ty_inner(env, &rep))
                };
                self.must_consume_active.remove(&adt.definition);
                result
            }
            _ => false,
        }
    }

    pub(super) fn eligible_key(
        &mut self,
        env: &Env,
        ty: &Ty,
        seen: &mut HashSet<DefinitionId>,
    ) -> bool {
        let immutable = |m: &Member| m.mode == super::MemberMode::PLAIN;
        match self.normalize(ty) {
            Ty::F64 | Ty::Callable(_) | Ty::Draft(_) | Ty::TypeValue(_) => false,
            Ty::Array(member) => immutable(&member) && self.eligible_key(env, &member.ty, seen),
            Ty::Map(key, member) => {
                immutable(&member)
                    && self.eligible_key(env, &key, seen)
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
            Ty::Adt(adt) if seen.insert(adt.definition) => {
                let result = if adt.is_linear {
                    false
                } else if matches!(adt.kind, AdtKind::Sum | AdtKind::OpaqueSum) {
                    let extensible = self.hir.definition(adt.definition).stmt.is_some_and(|s| {
                        let def = self.hir.definition(adt.definition);
                        matches!(
                            &self.ast(def.name.span.file).stmt(s).value.kind,
                            StmtKind::Type(decl)
                                if matches!(&decl.definition, TypeDefinition::Sum(variants)
                                    if variants.iter().any(|v| matches!(v, Variant::Extensible)))
                        )
                    });
                    !extensible
                        && self
                            .sum_variants(&adt)
                            .values()
                            .flatten()
                            .all(|payload| self.eligible_key(env, payload, seen))
                } else {
                    self.representation(env, &adt)
                        .is_none_or(|ty| self.eligible_key(env, &ty, seen))
                };
                seen.remove(&adt.definition);
                result
            }
            _ => true,
        }
    }

    pub(super) fn meta_exportable(
        &mut self,
        env: &Env,
        ty: &Ty,
        seen: &mut HashSet<DefinitionId>,
    ) -> bool {
        match self.normalize(ty) {
            Ty::Callable(_) | Ty::Draft(_) | Ty::TypeValue(_) => false,
            Ty::Array(member) => {
                !matches!(member.mode.mode, Mode::Mut | Mode::Shared | Mode::Ref)
                    && self.meta_exportable(env, &member.ty, seen)
            }
            Ty::Map(key, member) => {
                !matches!(member.mode.mode, Mode::Mut | Mode::Shared | Mode::Ref)
                    && self.meta_exportable(env, &key, seen)
                    && self.meta_exportable(env, &member.ty, seen)
            }
            Ty::Record(fields, _) => fields.values().all(|member| {
                !matches!(member.mode.mode, Mode::Mut | Mode::Shared | Mode::Ref)
                    && self.meta_exportable(env, &member.ty, seen)
            }),
            Ty::Tuple(items) => items
                .iter()
                .all(|member| self.meta_exportable(env, &member.ty, seen)),
            Ty::Adt(adt) => {
                if adt.is_linear {
                    return false;
                }
                if !seen.insert(adt.definition) {
                    return true;
                }
                let result = if matches!(adt.kind, AdtKind::Sum | AdtKind::OpaqueSum) {
                    self.sum_variants(&adt)
                        .values()
                        .flatten()
                        .all(|payload| self.meta_exportable(env, payload, seen))
                } else {
                    self.representation(env, &adt)
                        .is_none_or(|ty| self.meta_exportable(env, &ty, seen))
                };
                seen.remove(&adt.definition);
                result
            }
            _ => true,
        }
    }
}
