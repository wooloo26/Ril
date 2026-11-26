use std::{
    collections::{BTreeMap, HashMap, HashSet},
    sync::Arc,
};

use ril_hir::{DefinitionId, DefinitionKind};
use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::{self, GenericArg, GenericParam, StmtKind, Type, TypeDefinition};

use crate::ty::{
    Adt, AdtKind, GenericValue, Ty, Value,
    check::{Checker, Env, Phase},
    value::static_argument,
};

impl Checker<'_> {
    pub(in crate::ty) fn type_arguments(
        &mut self,
        env: &mut Env,
        id: DefinitionId,
        params: &[GenericParam],
        args: &[GenericArg],
        span: Span,
    ) -> (Vec<GenericValue>, Env) {
        let def = self.hir.definition(id);
        let mut local = Env::new(def.name.span.file, def.scope);
        local.sendable_guards = env.sendable_guards.clone();
        local.domains = env.domains.clone();
        if args.len() > params.len() {
            self.error(Code::E0340, span, "too many generic arguments");
        }
        let mut values = Vec::new();
        for (index, param) in params.iter().enumerate() {
            let value = if let Some(arg) = args.get(index) {
                self.generic_argument(env, param, arg, span)
            } else if let Some(default) = &param.default {
                self.generic_argument(&mut local, param, default, span)
            } else {
                self.error(
                    Code::E0340,
                    span,
                    format!("missing generic argument {}", param.name.value),
                );
                GenericValue::Type(Ty::Unknown)
            };
            if let Some(param) = self.resolve(param.name.span) {
                local.generics.insert(param, value.clone());
            }
            self.validate_static_checks(&mut local, param, &value, span);
            values.push(value);
        }
        (values, local)
    }

    pub(in crate::ty) fn generic_argument(
        &mut self,
        env: &mut Env,
        param: &GenericParam,
        arg: &GenericArg,
        span: Span,
    ) -> GenericValue {
        if param
            .name
            .value
            .starts_with(|c: char| c.is_ascii_lowercase() || c == '_')
        {
            let evaluated = match arg {
                GenericArg::Value(expr) => self.eval_root(env, *expr, true),
                GenericArg::Type(ty) => {
                    let expects_type_value = param.bound.first().is_some_and(|&bound| {
                        matches!(&self.ast(param.name.span.file).ty(bound).value,
                            Type::Named(path) if path.segments.last().is_some_and(|seg| seg.name.value == "Type"))
                    });
                    if expects_type_value {
                        Some(Value::Type(Box::new(self.type_expr(env, *ty))))
                    } else {
                        None
                    }
                }
                GenericArg::Mode(_) => None,
            };
            if let Some(data) = evaluated {
                GenericValue::Data(static_argument(data))
            } else {
                self.error(
                    Code::E0323,
                    span,
                    "value parameter requires a static value of its declared kind",
                );
                GenericValue::Data(Value::Unit)
            }
        } else if let GenericArg::Mode(mode) = arg {
            GenericValue::Mode(self.member_mode(env, mode))
        } else {
            GenericValue::Type(self.type_argument(env, arg))
        }
    }

    pub(in crate::ty) fn type_argument(&mut self, env: &mut Env, arg: &GenericArg) -> Ty {
        if let GenericArg::Type(ty) = arg {
            self.type_expr(env, *ty)
        } else {
            let span = match arg {
                GenericArg::Value(expr) => self.ast(env.file).expr(*expr).span,
                GenericArg::Mode(_) => self
                    .ast(env.file)
                    .items
                    .first()
                    .map_or(Span::new(env.file, 0, 0), |&id| {
                        self.ast(env.file).stmt(id).span
                    }),
                GenericArg::Type(_) => ril_source::ice!("type argument was already handled"),
            };
            self.error(Code::E0306, span, "type parameter requires type syntax");
            Ty::Unknown
        }
    }

    pub(in crate::ty) fn instantiate_adt(&self, adt: &Adt) -> Env {
        let def = self.hir.definition(adt.definition);
        let mut env = Env::new(def.name.span.file, def.scope);
        if let Some(stmt) = def.stmt
            && let StmtKind::Type(decl) = &self.ast(env.file).stmt(stmt).value.kind
        {
            for (param, arg) in decl.generics.iter().zip(&adt.arguments) {
                if let Some(id) = self.resolve(param.name.span) {
                    env.generics.insert(id, arg.clone());
                }
            }
        }
        env
    }

    pub(in crate::ty) fn unwrap_wrapper(&mut self, env: &Env, ty: &Ty) -> Ty {
        let mut cur = self.normalize(ty);
        let mut active: Vec<Arc<Adt>> = Vec::new();
        loop {
            if let Ty::Param(id) = &cur
                && let Some(GenericValue::Type(specialized)) = env.generics.get(id)
                && *specialized != cur
            {
                cur = self.normalize(specialized);
                continue;
            }
            let Ty::Adt(adt) = &cur else {
                break;
            };
            if !matches!(adt.kind, AdtKind::Nominal | AdtKind::Opaque) {
                break;
            }
            if active
                .iter()
                .rev()
                .find(|outer| outer.definition == adt.definition)
                .is_some_and(|outer| !crate::ty::nested_type_argument(outer, adt))
            {
                break;
            }
            active.push(Arc::clone(adt));
            if self.hir.unit_constructor(adt.definition) {
                return Ty::Unit;
            }
            let Some(rep) = self.representation(env, adt) else {
                break;
            };
            cur = self.normalize(&rep);
        }
        cur
    }

    pub(in crate::ty) fn is_value_ty(&mut self, env: &Env, ty: &Ty) -> bool {
        self.unwrap_wrapper(env, ty).is_primitive_value()
    }

    pub(in crate::ty) fn is_value_only_ty(&mut self, env: &Env, ty: &Ty) -> bool {
        let unwrapped = self.unwrap_wrapper(env, ty);
        if unwrapped.is_primitive_value() {
            return true;
        }
        if let Ty::Param(id) = unwrapped
            && let Some(dom) = env.domains.get(&id).cloned()
        {
            return !dom.is_empty() && dom.iter().all(|t| self.is_value_ty(env, t));
        }
        false
    }

    pub(in crate::ty) fn parameter_callable_mode(
        &mut self,
        env: &Env,
        param: &crate::ty::Parameter,
    ) -> ril_syntax::syntax::Mode {
        let is_value = self.is_value_ty(env, &param.ty);
        param.callable_mode_with(is_value)
    }

    pub(in crate::ty) fn representation(&mut self, _env: &Env, adt: &Adt) -> Option<Ty> {
        let mut scope = self.instantiate_adt(adt);
        let def = self.hir.definition(adt.definition);
        let stmt = def.stmt?;
        let StmtKind::Type(decl) = &self.ast(scope.file).stmt(stmt).value.kind else {
            return None;
        };
        match decl.definition {
            TypeDefinition::Data(ty) => {
                self.nominal_fields(&mut scope, decl);
                let rep = self.type_expr(&mut scope, ty);
                (rep != Ty::Adt(Arc::new(adt.clone()))).then_some(rep)
            }
            TypeDefinition::Opaque if adt.kind == AdtKind::Nominal => Some(Ty::Unit),
            _ => None,
        }
    }

    pub(in crate::ty) fn validate_generic_uses(
        &mut self,
        caller: &Env,
        id: DefinitionId,
        supplied: &HashMap<DefinitionId, GenericValue>,
        span: Span,
    ) {
        let def = self.hir.definition(id);
        let Some(stmt) = def.stmt else { return };
        let StmtKind::Function(function) = &self.ast(def.name.span.file).stmt(stmt).value.kind
        else {
            return;
        };
        let mut local = Env::new(def.name.span.file, def.scope);
        local.caller_scope = Some(caller.effective_scope());
        local.error_span = Some(caller.error_span.unwrap_or(span));
        local.generics.clone_from(supplied);
        for param in &function.generics {
            let Some(definition) = self.resolve(param.name.span) else {
                continue;
            };
            if let Some(argument) = supplied.get(&definition) {
                self.validate_static_checks(&mut local, param, argument, span);
            }
            if let Some(GenericValue::Type(actual)) = supplied.get(&definition) {
                let actual = self.normalize(actual);
                local.allow_open_record = true;
                let domain: Vec<_> = param
                    .bound
                    .iter()
                    .map(|&ty| self.type_expr(&mut local, ty))
                    .collect();
                local.allow_open_record = false;
                let allowed = domain.is_empty()
                    || domain
                        .iter()
                        .any(|ty| matches!(ty, Ty::Unknown | Ty::Mode | Ty::TypeValue(None)))
                    || match actual {
                        Ty::Param(id) => caller.domains.get(&id).is_some_and(|actual_domain| {
                            actual_domain.iter().all(|actual| {
                                domain
                                    .iter()
                                    .any(|allowed| self.fits(caller, actual, allowed))
                            })
                        }),
                        Ty::Infer(_) => true,
                        _ => domain
                            .iter()
                            .any(|allowed| self.fits(caller, &actual, allowed)),
                    };
                if !allowed {
                    self.error(
                        Code::E0306,
                        span,
                        format!(
                            "{} does not satisfy the domain of {}",
                            actual.display(self.hir),
                            param.name.value
                        ),
                    );
                } else if matches!(actual, Ty::Infer(_))
                    && !param
                        .name
                        .value
                        .starts_with(|c: char| c.is_ascii_lowercase())
                {
                    self.error(
                        Code::E0344,
                        span,
                        format!("could not infer generic parameter {}", param.name.value),
                    );
                }
            }
        }
    }

    fn validate_static_checks(
        &mut self,
        env: &mut Env,
        parameter: &GenericParam,
        value: &GenericValue,
        span: Span,
    ) {
        let value = match value {
            GenericValue::Type(ty) => GenericValue::Type(self.normalize(ty)),
            value => value.clone(),
        };
        if env.shadow
            || matches!(
                value,
                GenericValue::Type(Ty::Param(_) | Ty::Infer(_) | Ty::Unknown)
            )
        {
            return;
        }
        for check in &parameter.guards {
            self.apply_static_check(env, check, &value, span);
        }
    }

    pub(in crate::ty) fn specialize_meta_call(
        &mut self,
        caller: &Env,
        target: DefinitionId,
        generics: &HashMap<DefinitionId, GenericValue>,
        application: &crate::ty::staging::Application<'_>,
        result: &Ty,
    ) -> Ty {
        let def = self.hir.definition(target);
        let Some(stmt) = def.stmt else {
            return result.clone();
        };
        let StmtKind::Function(function) = &self.ast(def.name.span.file).stmt(stmt).value.kind
        else {
            return result.clone();
        };
        let mut local = Env::new(def.name.span.file, def.scope);
        local.generics = generics
            .iter()
            .map(|(&id, arg)| {
                let arg = match arg {
                    GenericValue::Type(ty) => GenericValue::Type(self.normalize(ty)),
                    value => value.clone(),
                };
                (id, arg)
            })
            .collect();
        self.specialize_meta_parameters(
            caller,
            local,
            def.name.span,
            &function.signature.params,
            application,
            result,
        )
    }

    pub(in crate::ty) fn specialize_meta_parameters(
        &mut self,
        caller: &Env,
        mut local: Env,
        target: Span,
        parameters: &[syntax::Parameter],
        application: &crate::ty::staging::Application<'_>,
        result: &Ty,
    ) -> Ty {
        use crate::ty::staging::{MetaCall, StaticBinding, StaticInput};
        let span = application.span;
        local.phase = Phase::TypeEval;
        let callee = local.clone();
        let mut bindings = Vec::new();
        let mut aliases = BTreeMap::new();
        for (index, parameter) in parameters.iter().enumerate().filter(|(_, p)| p.is_meta) {
            let input = application.inputs.get(&index).cloned().or_else(|| {
                if application.supplied.get(index) != Some(&true)
                    && let Some(default) = parameter.default
                {
                    self.stage_static_argument(&local, default, false)
                } else {
                    None
                }
            });
            let Some(input) = input else { continue };
            let name = parameter
                .name
                .as_ref()
                .and_then(|name| self.resolve(name.span));
            if let StaticInput::Ready(value) = &input {
                if let Some(id) = name {
                    local.generics.insert(id, GenericValue::Data(value.clone()));
                }
            } else if let StaticInput::Supplied(expr) = &input
                && let Some(id) = name
                && let syntax::Expr::Path(path) = &self.ast(caller.file).expr(*expr).value
                && let Some(source) = self.resolve(path.span)
                && caller.meta_keys.contains_key(&source)
            {
                aliases.insert(id, source);
            }
            bindings.push(StaticBinding {
                name,
                guards: parameter.guards.clone(),
                input,
            });
        }
        let uses_deferred_inputs = bindings
            .iter()
            .any(|binding| !matches!(binding.input, StaticInput::Ready(_)));
        let abstract_types = local.generics.values().any(
            |value| matches!(value, GenericValue::Type(ty) if ty.has_unresolved_static_type()),
        );
        let needs_specialization = uses_deferred_inputs
            || abstract_types && bindings.iter().any(|binding| !binding.guards.is_empty());
        if !needs_specialization {
            for binding in &bindings {
                if let StaticInput::Ready(value) = &binding.input {
                    self.check_meta_input(&mut local, &binding.guards, value, span);
                }
            }
        }
        self.meta_calls.insert(
            span,
            MetaCall {
                caller: caller.clone(),
                callee,
                bindings,
                target,
                needs_specialization,
            },
        );
        let result = self.specialize_projections(&mut local, &self.normalize(result), span);
        crate::ty::check::transform(&result, &mut |ty| match ty {
            Ty::Projection(base, key) => aliases
                .get(key)
                .map(|&source| Ty::Projection(base.clone(), source)),
            _ => None,
        })
    }

    pub(in crate::ty) fn apply_static_check(
        &mut self,
        env: &mut Env,
        path: &syntax::Path,
        input: &GenericValue,
        span: Span,
    ) {
        let Some(check) = self.resolve(path.span) else {
            return;
        };
        let def = self.hir.definition(check);
        if matches!(def.kind, DefinitionKind::Primitive(_)) {
            if let GenericValue::Type(ty) = input {
                let ty = self.normalize(ty);
                if def.name.value == "Sendable" && !self.is_sendable(env, &ty, &mut HashSet::new())
                {
                    self.error(Code::E0301, span, "type does not satisfy Sendable");
                }
            }
            if self.prelude_key(path)
                && let GenericValue::Data(key) = input
                && let Some(arg) = path
                    .segments
                    .last()
                    .and_then(|segment| segment.arguments.first())
            {
                let target = self.type_argument(env, arg);
                if !self.has_key(env, &target, key) {
                    self.error(
                        Code::E0323,
                        span,
                        "invalid coordinate for the statically checked type",
                    );
                }
            }
            return;
        }
        let Some(stmt) = def.stmt else { return };
        let file = def.name.span.file;
        let StmtKind::Type(declaration) = &self.ast(file).stmt(stmt).value.kind else {
            self.error(
                Code::E0306,
                path.span,
                "static check requires a type function",
            );
            return;
        };
        let TypeDefinition::Function(parameters, body) = &declaration.definition else {
            self.error(
                Code::E0306,
                path.span,
                "static check requires a type function",
            );
            return;
        };
        let Some((first, parameters)) = parameters.split_first() else {
            self.error(
                Code::E0340,
                path.span,
                "static check requires an input parameter",
            );
            return;
        };
        let arguments = path
            .segments
            .last()
            .map_or(&[][..], |segment| segment.arguments.as_slice());
        if arguments.len() > parameters.len() {
            self.error(Code::E0340, path.span, "too many static check arguments");
            return;
        }
        let call_span = env.error_span.unwrap_or(span);
        let mut local = Env::new(file, def.scope);
        local.phase = Phase::TypeEval;
        local.caller_scope = Some(env.effective_scope());
        local.error_span = Some(call_span);
        local.domains = env.domains.clone();
        if let Some(id) = self.resolve(first.name.span) {
            local.generics.insert(id, input.clone());
        }
        for (index, parameter) in parameters.iter().enumerate() {
            let value = if let Some(argument) = arguments.get(index) {
                self.generic_argument(env, parameter, argument, span)
            } else if let Some(default) = &parameter.default {
                self.generic_argument(&mut local, parameter, default, span)
            } else {
                self.error(Code::E0340, path.span, "missing static check argument");
                return;
            };
            if let Some(id) = self.resolve(parameter.name.span) {
                local.generics.insert(id, value);
            }
        }
        if u64::try_from(self.stack.len()).unwrap_or(u64::MAX) >= self.budget.min(256) {
            self.error(
                Code::E0811,
                span,
                "static checks exceeded the evaluation budget",
            );
            return;
        }
        self.stack.push(check);
        let result = self.eval_root_at(&local, *body, true, call_span);
        self.stack.pop();
        let Some(result) = result else { return };
        let Value::Type(ty) = result else {
            self.error(Code::E0306, span, "static check must return a type value");
            return;
        };
        match input {
            GenericValue::Type(actual) if *actual == *ty && *ty != Ty::Never => {}
            GenericValue::Type(_) => self.error(Code::E0301, span, "type rejected by static check"),
            _ if *ty == Ty::Unit => {}
            _ if *ty == Ty::Never => {
                self.error(Code::E0323, span, "value rejected by static check");
            }
            _ => self.error(
                Code::E0306,
                span,
                "static value check must return <()> or <never>",
            ),
        }
    }

    pub(in crate::ty) fn call_argument_types(
        &mut self,
        env: &mut Env,
        id: DefinitionId,
        args: &[GenericArg],
        span: Span,
    ) -> HashMap<DefinitionId, GenericValue> {
        let def = self.hir.definition(id);
        let mut generics = HashMap::new();
        if let Some(stmt) = def.stmt
            && let StmtKind::Function(fun) = &self.ast(def.name.span.file).stmt(stmt).value.kind
        {
            if args.len() > fun.generics.len() {
                self.error(Code::E0340, span, "too many generic arguments");
            }
            for (index, param) in fun.generics.iter().enumerate() {
                if let Some(id) = self.resolve(param.name.span) {
                    let argument = match args.get(index) {
                        Some(arg) => self.generic_argument(env, param, arg, span),
                        None => GenericValue::Type(self.fresh()),
                    };
                    generics.insert(id, argument);
                }
            }
        }
        generics
    }
}
