use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use ril_hir::{DefinitionId, DefinitionKind};
use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::{self, Function, Mode, StmtId, StmtKind, TypeDefinition, Variant};

use super::{Checker, Env, Phase, substitute, transform, unknown_callable};
use crate::ty::{AdtKind, Callable, GenericValue, Ty, Value};

impl Checker<'_> {
    pub(in crate::ty) fn declare_function(&mut self, id: DefinitionId) -> Arc<Callable> {
        if let Some(value) = self.callables.get(&id) {
            return Arc::clone(value);
        }
        let def = self.hir.definition(id);
        let Some(stmt) = def.stmt else {
            return Arc::new(unknown_callable());
        };
        let file = def.name.span.file;
        let ast = self.ast(file);
        let StmtKind::Function(function) = &ast.stmt(stmt).value.kind else {
            return Arc::new(unknown_callable());
        };
        if !self.resolving.insert(id) {
            return Arc::new(unknown_callable());
        }
        let mut env = Env::new(file, def.scope);
        if function.is_meta {
            env.phase = Phase::MetaValue;
        }
        if let Some(parameter) = function
            .generics
            .iter()
            .find(|param| param.default.is_some())
        {
            self.error(
                Code::E0317,
                parameter.name.span,
                "function generic parameters cannot have defaults",
            );
        }
        self.generic_env(&mut env, &function.generics);
        let call = Arc::new(self.callable(&mut env, &function.signature, true));
        if self.exposes_type(&Ty::Callable(Arc::clone(&call)), |id| {
            let def = self.hir.definition(id);
            def.name.span.file == file
                && def
                    .stmt
                    .is_some_and(|stmt| function.helpers.contains(&stmt))
        }) {
            self.error(
                Code::E0315,
                function.name.span,
                "local type escapes in the callable signature",
            );
        }
        self.callables.insert(id, Arc::clone(&call));
        self.bindings.insert(id, Ty::Callable(Arc::clone(&call)));
        self.resolving.remove(&id);
        call
    }

    pub(in crate::ty) fn function(&mut self, env: &Env, fun: &Function) {
        let Some(id) = self.resolve(fun.name.span) else {
            return;
        };
        if !self.checked.insert(id) {
            return;
        }
        let mut local = env.clone();
        local.phase = if fun.is_meta {
            Phase::MetaValue
        } else {
            Phase::Runtime
        };
        if !fun.is_meta
            && (!fun.generics.is_empty() || fun.signature.params.iter().any(|param| param.is_meta))
        {
            local.staging_owner = Some(fun.name.span);
        }
        self.generic_env(&mut local, &fun.generics);
        let call = self.declare_function(id);
        local.mode_scope = Some(call.has_via_inputs() || env.mode_scope == Some(true));
        let span = fun.name.span;
        if fun.is_meta {
            if call.result.contains_type_value() {
                self.error(Code::E0812, span, "meta fn cannot return a type value");
            }
            if matches!(call.result, Ty::Callable(_) | Ty::Draft(_)) {
                self.error(
                    Code::E0816,
                    span,
                    "meta fn cannot export a callable or resource",
                );
            }
            if call.open_effects
                || call.open_state
                || !call.effects.is_empty()
                || !call.state.is_empty()
            {
                self.error(Code::E0813, span, "meta fn must be pure");
            }
        } else if call.result.contains_type_value() {
            self.error(
                Code::E0816,
                span,
                "runtime callable cannot return type values",
            );
        }
        local.expected_return = Some(call.result.clone());
        local.inferred_return = None;
        for (index, (p, ty)) in fun
            .signature
            .params
            .iter()
            .zip(&call.parameters)
            .enumerate()
        {
            if let Some(name) = &p.name {
                self.define_name(name, ty.ty.clone());
                if p.is_meta {
                    self.declare_meta_key(&mut local, p);
                }
                if p.mode != Mode::Plain
                    && let Some(id) = self.resolve(name.span)
                {
                    self.live.insert(id);
                }
            }
            if let Some(default) = p.default {
                let span = self.ast(local.file).expr(default).span;
                let referenced: HashSet<_> =
                    self.hir.references_within(span).map(|(_, id)| id).collect();
                for (position, formal) in fun.signature.params.iter().enumerate() {
                    if formal
                        .name
                        .as_ref()
                        .and_then(|name| self.resolve(name.span))
                        .is_some_and(|id| referenced.contains(&id))
                    {
                        if position >= index {
                            self.error(
                                Code::E0408,
                                span,
                                "default reads its own or a subsequent parameter",
                            );
                        } else if matches!(
                            formal.mode,
                            Mode::Mut | Mode::Shared | Mode::New | Mode::Via
                        ) {
                            self.error(Code::E0409, span, "default reads live writable state");
                        }
                    }
                }
                self.check_pure_default(&local, default, &ty.ty);
            }
        }
        for &helper in &fun.helpers {
            let mut helper_env = env.clone();
            self.statement(&mut helper_env, helper, false);
        }
        for &guard in fun
            .signature
            .params
            .iter()
            .filter(|parameter| !parameter.is_meta)
            .flat_map(|p| &p.guards)
            .chain(&fun.signature.guards)
        {
            self.check_guard(&local, guard, &call.result);
        }
        if let Some(body) = fun.body {
            local.return_scope = Some(self.ast(local.file).expr(body).span);
            self.expect(&mut local, body, &call.result);
        }
    }

    pub(in crate::ty) fn statement(&mut self, env: &mut Env, item: StmtId, tail: bool) -> Ty {
        let node = self.ast(env.file).stmt(item);
        for &attribute in &node.value.attrs {
            self.metadata(env, attribute);
        }
        match &node.value.kind {
            StmtKind::Binding {
                pattern,
                ty,
                value,
                fallback,
                is_meta,
                storage,
                ..
            } => {
                let mut env_meta;
                let local = if *is_meta {
                    env_meta = env.clone();
                    env_meta.phase = Phase::MetaValue;
                    &mut env_meta
                } else {
                    env
                };
                let expect = ty.map(|ty| self.type_expr(local, ty));
                let inferred = match (value, &expect) {
                    (Some(expr), Some(ty)) => self.receive(local, *expr, ty),
                    (Some(expr), None) => self.expr(local, *expr, None),
                    (None, Some(ty)) => ty.clone(),
                    (None, None) => Ty::Unknown,
                };
                if let Some(fallback) = fallback {
                    let otherwise = self.expr(local, *fallback, None);
                    if otherwise != Ty::Never && otherwise != Ty::Unknown {
                        self.error(
                            Code::E0321,
                            self.ast(local.file).expr(*fallback).span,
                            "let else must transfer control",
                        );
                    }
                }
                let inferred = expect.unwrap_or(inferred);
                if fallback.is_none()
                    && !matches!(
                        self.ast(local.file).pattern(*pattern).value,
                        syntax::Pattern::Wildcard
                    )
                    && !matches!(inferred, Ty::Unknown | Ty::Never)
                {
                    let shape = self.pattern_shape(local, *pattern, &inferred);
                    if self.useful(local, &[shape], crate::ty::coverage::Shape::Any, &inferred) {
                        self.error(
                            Code::E0345,
                            self.ast(local.file).pattern(*pattern).span,
                            "binding pattern can fail; add let else",
                        );
                    } else if self.pattern_names(local, *pattern).is_empty() {
                        self.error(
                            Code::E0309,
                            self.ast(local.file).pattern(*pattern).span,
                            "binding pattern introduces no names",
                        );
                    }
                }
                if inferred.contains_type_value() && (*is_meta || local.phase == Phase::Runtime) {
                    self.error(
                        Code::E0816,
                        node.span,
                        "type values cannot escape into runtime or meta let storage",
                    );
                } else if *is_meta && matches!(inferred, Ty::Callable(_) | Ty::Draft(_)) {
                    self.error(
                        Code::E0816,
                        node.span,
                        "callable or resource cannot escape a static root",
                    );
                } else if *is_meta && let Some(value) = value {
                    self.eval_root(local, *value, true);
                }
                self.pattern(local, *pattern, &inferred);
                if (storage.variable || storage.mode != Mode::Plain)
                    && let syntax::Pattern::Binding(_, name) =
                        &self.ast(local.file).pattern(*pattern).value
                    && let Some(id) = self.resolve(name.span)
                {
                    self.live.insert(id);
                }
                if !storage.variable
                    && storage.mode == Mode::Plain
                    && ty.is_none()
                    && value.is_some_and(|value| {
                        matches!(
                            self.ast(local.file).expr(value).value,
                            syntax::Expr::Closure { .. }
                        )
                    })
                    && let syntax::Pattern::Binding(_, name) =
                        &self.ast(local.file).pattern(*pattern).value
                    && let Some(definition) = self.resolve(name.span)
                    && self.hir.definition(definition).kind == DefinitionKind::Local
                {
                    self.schemes.insert(definition);
                }
            }
            StmtKind::Expr(expr) => {
                let ty = self.expr(env, *expr, None);
                if !tail && env.shadow && ty.is_result() {
                    self.error(Code::E0720, node.span, "fallible result must be inspected");
                }
                return ty;
            }
            StmtKind::Function(fun) => self.function(env, fun),
            StmtKind::Sub { name, items } => {
                if let Some(id) = self.resolve(name.span)
                    && let DefinitionKind::Namespace(scope) = self.hir.definition(id).kind
                {
                    let mut sub = Env::new(env.file, scope);
                    for &item in items {
                        self.statement(&mut sub, item, false);
                    }
                }
            }
            StmtKind::Type(decl) => {
                let mut local = env.clone();
                self.validate_defaults(&local, &decl.generics);
                self.generic_env(&mut local, &decl.generics);
                self.nominal_fields(&mut local, decl);
                match &decl.definition {
                    TypeDefinition::Data(ty) => {
                        let representation = self.type_expr(&mut local, *ty);
                        if decl.kind == ril_syntax::syntax::TypeKind::Nominal
                            && let Some(id) = self.resolve(decl.name.span)
                        {
                            self.nominal_layouts.insert(id, representation);
                        }
                    }
                    TypeDefinition::Sum(_) if decl.generics.is_empty() => {
                        if let Some(id) = self.resolve(decl.name.span)
                            && let Ty::Adt(adt) = self.adt(id, decl, Vec::new())
                        {
                            self.sum_variants(&adt);
                        }
                    }
                    TypeDefinition::Sum(variants) => {
                        for variant in variants {
                            match variant {
                                Variant::Constructor { payload, .. } => {
                                    for &ty in payload.iter().flatten() {
                                        self.type_expr(&mut local, ty);
                                    }
                                }
                                Variant::Spread(ty) => {
                                    self.type_expr(&mut local, *ty);
                                }
                                Variant::Extensible => {}
                            }
                        }
                    }
                    TypeDefinition::Function(params, body) => {
                        local.phase = Phase::TypeEval;
                        local.checking_type_template = true;
                        self.validate_defaults(&local, params);
                        self.generic_env(&mut local, params);
                        let ty = self.expr(&mut local, *body, None);
                        self.require(
                            &local,
                            self.ast(local.file).expr(*body).span,
                            &ty,
                            &Ty::TypeValue(None),
                        );
                    }
                    TypeDefinition::Opaque => {}
                }
            }
            StmtKind::Effect { operations, .. } => {
                for &operation in operations {
                    self.statement(env, operation, false);
                }
            }
            StmtKind::With(handlers) => {
                for handler in handlers {
                    if let Some(operation) = self.resolve(handler.operation.span)
                        && self.hir.operation_effect(operation).is_some()
                    {
                        let mut expected = (*self.declare_function(operation)).clone();
                        let bindings = self.operation_instance(env, operation, &handler.operation);
                        for parameter in &mut expected.parameters {
                            parameter.label = None;
                            parameter.ty = substitute(&parameter.ty, &bindings);
                        }
                        expected.result = substitute(&expected.result, &bindings);
                        expected.open_effects = true;
                        expected.open_state = true;
                        self.expect(env, handler.value, &Ty::Callable(Arc::new(expected)));
                    } else {
                        self.expr(env, handler.value, None);
                    }
                }
            }
            StmtKind::Import(_) | StmtKind::Error => {}
        }
        Ty::Unit
    }

    pub(in crate::ty) fn metadata(
        &mut self,
        env: &Env,
        expression: syntax::ExprId,
    ) -> Option<(Ty, Value)> {
        let span = self.ast(env.file).expr(expression).span;
        if !self.active_metadata.insert(span) {
            self.error(Code::E0811, span, "recursive metadata evaluation");
            return None;
        }
        let mut local = env.clone();
        local.phase = Phase::MetaValue;
        let ty = self.expr(&mut local, expression, None);
        let ty = self.normalize(&ty);
        let mut invalid = false;
        transform(&ty, &mut |part| {
            invalid |= matches!(
                part,
                Ty::Callable(_)
                    | Ty::Draft(_)
                    | Ty::Scope
                    | Ty::Task(_)
                    | Ty::Sender(_)
                    | Ty::Receiver(_)
            ) || matches!(part, Ty::Adt(adt) if adt.kind == AdtKind::Foreign);
            None
        });
        let result = if ty.contains_type_value() {
            self.error(Code::E0812, span, "type value in metadata");
            None
        } else if invalid {
            self.error(Code::E0816, span, "invalid static metadata value");
            None
        } else {
            self.eval_root(&local, expression, true)
                .map(|value| (ty, value))
        };
        self.active_metadata.remove(&span);
        result
    }

    pub(in crate::ty) fn def_type(
        &mut self,
        env: &mut Env,
        id: DefinitionId,
        span: Span,
        callee: bool,
    ) -> Ty {
        let def = self.hir.definition(id);
        match def.kind {
            DefinitionKind::Function => {
                let call = self.declare_function(id);
                if !callee
                    && (self.is_meta_fn(id)
                        || call.parameters.iter().any(|parameter| parameter.is_meta))
                {
                    self.error(
                        Code::E0810,
                        span,
                        "meta fn requires direct saturated application",
                    );
                }
                Ty::Callable(call)
            }
            DefinitionKind::Local | DefinitionKind::Generic => {
                if let Some(GenericValue::Type(ty)) = env.generics.get(&id) {
                    return ty.clone();
                }
                let ty = self.bindings.get(&id).cloned().unwrap_or(Ty::Unknown);
                if self.schemes.contains(&id) {
                    self.instantiate(&ty)
                } else {
                    ty
                }
            }
            DefinitionKind::Constant => {
                if let Some(ty) = self.bindings.get(&id) {
                    return ty.clone();
                }
                let Some(stmt) = def.stmt else {
                    return Ty::Unknown;
                };
                if !self.constants.insert(id) {
                    self.error(Code::E0207, span, "recursive initialization");
                    return Ty::Unknown;
                }
                self.statement(&mut Env::new(def.name.span.file, def.scope), stmt, false);
                self.constants.remove(&id);
                self.bindings.get(&id).cloned().unwrap_or(Ty::Unknown)
            }
            DefinitionKind::Variant(_) => self.variant(env, id, None, span),
            DefinitionKind::Type | DefinitionKind::Sum(_) if callee => Ty::Unknown,
            DefinitionKind::Type | DefinitionKind::Sum(_) => {
                if self.hir.unit_constructor(id)
                    && let Some(stmt) = def.stmt
                    && let StmtKind::Type(decl) =
                        &self.ast(def.name.span.file).stmt(stmt).value.kind
                {
                    return self.adt(id, decl, Vec::new());
                }
                self.error(Code::E0319, span, "bare type in value expression");
                Ty::Unknown
            }
            DefinitionKind::Primitive(_) => {
                if let Some(stmt) = def.stmt
                    && matches!(
                        self.ast(def.name.span.file).stmt(stmt).value.kind,
                        StmtKind::Function(_)
                    )
                {
                    let call = self.declare_function(id);
                    if !callee && self.is_meta_fn(id) {
                        self.error(
                            Code::E0810,
                            span,
                            "meta fn requires direct saturated application",
                        );
                    }
                    return Ty::Callable(call);
                }
                self.primitive_type(env, &def.name.value, span, callee)
            }
            _ => Ty::Unknown,
        }
    }

    fn instantiate(&mut self, ty: &Ty) -> Ty {
        let mut variables = HashMap::new();
        let ty = self.normalize(ty);
        transform(&ty, &mut |value| match value {
            Ty::Infer(id) => Some(variables.entry(*id).or_insert_with(|| self.fresh()).clone()),
            _ => None,
        })
    }

    pub(in crate::ty) fn is_meta_fn(&self, id: DefinitionId) -> bool {
        let def = self.hir.definition(id);
        def.stmt.is_some_and(|stmt| {
            matches!(&self.ast(def.name.span.file).stmt(stmt).value.kind, StmtKind::Function(fun) if fun.is_meta)
        })
    }
}
