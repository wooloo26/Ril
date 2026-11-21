use std::{
    collections::{BTreeMap, HashMap, HashSet},
    sync::Arc,
};

use ril_base::{
    diag::{Code, Diagnostic},
    span::{FileId, Span},
};
use ril_frontend::{
    hir::{DefinitionId, DefinitionKind, Program, Resolution, ScopeId},
    syntax::{
        self, Ast, Function, Mode, Name, StmtId, StmtKind, Storage, TypeDefinition, TypeKind,
        Variant,
    },
};

use super::{
    AdtKind, Callable, GenericValue, Member, MemberMode, Parameter, Ty, TypedProgram, Value,
};

pub(super) const DEFAULT_BUDGET: u64 = 10_000;

pub(super) fn check(hir: Program, budget: Option<u64>) -> Result<TypedProgram, Vec<Diagnostic>> {
    let mut ck = Checker {
        hir: &hir,
        diagnostics: Vec::new(),
        types: HashMap::new(),
        bindings: HashMap::new(),
        callables: BTreeMap::new(),
        static_values: HashMap::new(),
        next_infer: 0,
        substitutions: HashMap::new(),
        resolving: HashSet::new(),
        checked: HashSet::new(),
        constants: HashSet::new(),
        stack: Vec::new(),
        budget: budget.unwrap_or(DEFAULT_BUDGET),
    };
    for (id, def) in hir.definitions() {
        if def.kind == DefinitionKind::Function && def.stmt.is_some() {
            ck.declare_function(id);
        }
    }
    for file in hir.files() {
        let scope = hir.module_scope(file.id);
        let mut env = Env::new(file.id, scope);
        for &item in &file.ast.items {
            ck.statement(&mut env, item, false);
        }
    }
    if !ck.diagnostics.is_empty() {
        return Err(ck.diagnostics);
    }
    let types = std::mem::take(&mut ck.types)
        .into_iter()
        .map(|(span, ty)| (span, ck.normalize(&ty)))
        .collect();
    let bindings = std::mem::take(&mut ck.bindings)
        .into_iter()
        .map(|(id, ty)| (id, ck.normalize(&ty)))
        .collect();
    let Checker {
        callables,
        static_values,
        ..
    } = ck;
    Ok(TypedProgram {
        hir,
        types,
        bindings,
        callables,
        static_values,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Phase {
    Runtime,
    MetaValue,
    TypeEval,
}

#[derive(Clone)]
pub(super) struct Env {
    pub(super) file: FileId,
    pub(super) scope: ScopeId,
    pub(super) phase: Phase,
    pub(super) generics: HashMap<DefinitionId, GenericValue>,
    pub(super) domains: HashMap<DefinitionId, Vec<Ty>>,
    pub(super) expected_return: Option<Ty>,
    pub(super) shadow: bool,
    pub(super) effects_seen: HashSet<String>,
}

impl Env {
    pub(super) fn new(file: FileId, scope: ScopeId) -> Self {
        Self {
            file,
            scope,
            phase: Phase::Runtime,
            generics: HashMap::new(),
            domains: HashMap::new(),
            expected_return: None,
            shadow: false,
            effects_seen: HashSet::new(),
        }
    }
}

pub(super) struct Checker<'a> {
    pub(super) hir: &'a Program,
    pub(super) diagnostics: Vec<Diagnostic>,
    pub(super) types: HashMap<Span, Ty>,
    pub(super) bindings: HashMap<DefinitionId, Ty>,
    pub(super) callables: BTreeMap<DefinitionId, Arc<Callable>>,
    pub(super) static_values: HashMap<Span, Value>,
    next_infer: u32,
    substitutions: HashMap<u32, Ty>,
    pub(super) resolving: HashSet<DefinitionId>,
    checked: HashSet<DefinitionId>,
    constants: HashSet<DefinitionId>,
    pub(super) stack: Vec<DefinitionId>,
    pub(super) budget: u64,
}

impl<'a> Checker<'a> {
    pub(super) fn ast(&self, file: FileId) -> &'a Ast {
        &self.hir.file(file).ast
    }

    pub(super) fn error(&mut self, code: Code, span: Span, message: impl Into<String>) {
        let diagnostic = Diagnostic::error(code, span, message);
        if !self.diagnostics.iter().any(|existing| {
            existing.code == diagnostic.code && existing.primary == diagnostic.primary
        }) {
            self.diagnostics.push(diagnostic);
        }
    }

    pub(super) fn resolve(&self, span: Span) -> Option<DefinitionId> {
        match self.hir.resolve(span) {
            Some(Resolution::Definition(def)) => Some(def),
            _ => None,
        }
    }

    pub(super) fn fresh(&mut self) -> Ty {
        let id = self.next_infer;
        self.next_infer += 1;
        Ty::Infer(id)
    }

    pub(super) fn normalize(&self, ty: &Ty) -> Ty {
        if let Ty::Infer(var) = ty
            && let Some(replace) = self.substitutions.get(var)
        {
            return self.normalize(replace);
        }
        transform(ty, &mut |ty| {
            if matches!(ty, Ty::Infer(var) if self.substitutions.contains_key(var)) {
                Some(self.normalize(ty))
            } else {
                None
            }
        })
    }

    pub(super) fn member_mode(&self, env: &Env, storage: &Storage) -> MemberMode {
        if let Some(path) = &storage.mode_path
            && let Some(id) = self.resolve(path.span)
            && let Some(GenericValue::Mode(mode)) = env.generics.get(&id)
        {
            return *mode;
        }
        MemberMode {
            variable: storage.variable,
            mode: storage.mode,
        }
    }

    fn bind_variable(&mut self, id: u32, ty: &Ty) -> bool {
        let mut occurs = false;
        transform(ty, &mut |found| {
            occurs |= *found == Ty::Infer(id);
            None
        });
        if !occurs {
            self.substitutions.insert(id, ty.clone());
        }
        !occurs
    }

    pub(super) fn fits(&mut self, env: &Env, actual: &Ty, expected: &Ty) -> bool {
        let actual = self.normalize(actual);
        let expected = self.normalize(expected);
        if actual == expected
            || matches!(actual, Ty::Unknown | Ty::Never)
            || matches!(expected, Ty::Unknown)
        {
            return true;
        }
        match (&actual, &expected) {
            (Ty::Infer(var), _) => self.bind_variable(*var, &expected),
            (_, Ty::Infer(var)) => self.bind_variable(*var, &actual),
            (Ty::Param(id), _) => env
                .generics
                .get(id)
                .and_then(|arg| match arg {
                    GenericValue::Type(ty) => Some(ty),
                    _ => None,
                })
                .is_some_and(|found| found != &actual && self.fits(env, found, &expected)),
            (_, Ty::Param(id)) => env
                .generics
                .get(id)
                .and_then(|arg| match arg {
                    GenericValue::Type(ty) => Some(ty),
                    _ => None,
                })
                .is_some_and(|found| found != &expected && self.fits(env, &actual, found)),
            (Ty::Option(a), Ty::Option(b))
            | (Ty::Set(a), Ty::Set(b))
            | (Ty::Draft(a), Ty::Draft(b)) => self.fits(env, a, b),
            (Ty::Result(ao, ae), Ty::Result(bo, be)) => {
                self.fits(env, ao, bo) && self.fits(env, ae, be)
            }
            (Ty::TypeValue(Some(_)), Ty::TypeValue(None)) => true,
            (Ty::Array(a), Ty::Array(b)) => self.member_fits(env, a, b),
            (Ty::Map(ak, a), Ty::Map(bk, b)) => {
                self.fits(env, ak, bk) && self.member_fits(env, a, b)
            }
            (Ty::Tuple(a), Ty::Tuple(b)) => {
                a.len() == b.len() && a.iter().zip(b).all(|(a, b)| self.member_fits(env, a, b))
            }
            (Ty::Record(a, a_open), Ty::Record(b, b_open)) => {
                (*b_open || !a_open && a.len() == b.len())
                    && b.iter()
                        .all(|(name, b)| a.get(name).is_some_and(|a| self.member_fits(env, a, b)))
            }
            (Ty::Callable(a), Ty::Callable(b)) => self.callable_fits(env, a, b),
            (Ty::Adt(adt), _) if adt.kind == AdtKind::Opaque && adt.defining_scope == env.scope => {
                self.representation(env, adt)
                    .is_some_and(|ty| self.fits(env, &ty, &expected))
            }
            (_, Ty::Adt(adt)) if adt.kind == AdtKind::Opaque && adt.defining_scope == env.scope => {
                self.representation(env, adt)
                    .is_some_and(|ty| self.fits(env, &actual, &ty))
            }
            _ => false,
        }
    }

    fn member_fits(&mut self, env: &Env, a: &Member, b: &Member) -> bool {
        (a.mode == b.mode || b.mode.mode == Mode::Via) && self.fits(env, &a.ty, &b.ty)
    }

    fn callable_fits(&mut self, env: &Env, actual: &Callable, expected: &Callable) -> bool {
        actual.parameters.len() == expected.parameters.len()
            && (expected.open_effects
                || !actual.open_effects
                    && actual
                        .effects
                        .iter()
                        .all(|effect| expected.effects.contains(effect)))
            && (expected.open_state
                || !actual.open_state
                    && actual
                        .state
                        .iter()
                        .all(|clause| expected.state.contains(clause)))
            && (actual.result_mode == expected.result_mode || expected.result_mode == Mode::Infer)
            && actual
                .parameters
                .iter()
                .zip(&expected.parameters)
                .all(|(a, b)| {
                    (a.mode == b.mode || b.mode == Mode::Via)
                        && b.label
                            .as_ref()
                            .is_none_or(|name| a.label.as_ref() == Some(name))
                        && self.fits(env, &b.ty, &a.ty)
                })
            && self.fits(env, &actual.result, &expected.result)
    }

    pub(super) fn require(&mut self, env: &Env, span: Span, actual: &Ty, expected: &Ty) -> bool {
        if self.fits(env, actual, expected) {
            return true;
        }
        let actual = self.normalize(actual);
        let expected = self.normalize(expected);
        let code = if matches!((&actual, &expected), (Ty::Adt(a), Ty::Adt(b)) if a.definition != b.definition
            && a.kind == AdtKind::Nominal && b.kind == AdtKind::Nominal)
        {
            Code::E0305
        } else {
            Code::E0301
        };
        self.error(
            code,
            span,
            format!(
                "expected {}, found {}",
                expected.display(self.hir),
                actual.display(self.hir)
            ),
        );
        false
    }

    pub(super) fn join(&mut self, env: &Env, span: Span, one: Ty, two: Ty) -> Ty {
        if matches!(one, Ty::Never) {
            two
        } else if matches!(two, Ty::Never) || self.fits(env, &two, &one) {
            self.normalize(&one)
        } else if self.fits(env, &one, &two) {
            self.normalize(&two)
        } else if env.phase == Phase::TypeEval
            && matches!((&one, &two), (Ty::TypeValue(_), Ty::TypeValue(_)))
        {
            Ty::TypeValue(None)
        } else {
            self.error(
                Code::E0351,
                span,
                format!(
                    "branch types {} and {} cannot join",
                    one.display(self.hir),
                    two.display(self.hir)
                ),
            );
            Ty::Unknown
        }
    }

    pub(super) fn define_name(&mut self, name: &Name, ty: Ty) {
        if let Some(id) = self.resolve(name.span) {
            self.bindings.insert(id, ty);
        }
    }

    pub(super) fn declare_function(&mut self, id: DefinitionId) -> Arc<Callable> {
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
        self.generic_env(&mut env, &function.generics);
        let call = Arc::new(self.callable(&mut env, &function.signature, true));
        self.callables.insert(id, Arc::clone(&call));
        self.bindings.insert(id, Ty::Callable(Arc::clone(&call)));
        self.resolving.remove(&id);
        call
    }

    pub(super) fn function(&mut self, env: &Env, fun: &Function) {
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
        self.generic_env(&mut local, &fun.generics);
        let call = self.declare_function(id);
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
        for (p, ty) in fun.signature.params.iter().zip(&call.parameters) {
            if let Some(name) = &p.name {
                self.define_name(name, ty.ty.clone());
            }
            if let Some(default) = p.default {
                self.expect(&mut local, default, &ty.ty);
            }
        }
        if let Some(body) = fun.body {
            self.expect(&mut local, body, &call.result);
        }
    }

    pub(super) fn statement(&mut self, env: &mut Env, item: StmtId, tail: bool) -> Ty {
        let node = self.ast(env.file).stmt(item);
        for &attribute in &node.value.attrs {
            let mut local = env.clone();
            local.phase = Phase::MetaValue;
            let ty = self.expr(&mut local, attribute, None);
            if ty.contains_type_value() {
                self.error(
                    Code::E0812,
                    self.ast(env.file).expr(attribute).span,
                    "type value in metadata",
                );
            } else if matches!(ty, Ty::Callable(_) | Ty::Draft(_)) {
                self.error(
                    Code::E0816,
                    self.ast(env.file).expr(attribute).span,
                    "invalid static metadata value",
                );
            } else {
                self.eval_root(&local, attribute, true);
            }
        }
        match &node.value.kind {
            StmtKind::Binding {
                pattern,
                ty,
                value,
                fallback,
                is_meta,
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
                    (Some(expr), Some(ty)) => self.expect(local, *expr, ty),
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
                self.generic_env(&mut local, &decl.generics);
                match &decl.definition {
                    TypeDefinition::Data(ty) => {
                        self.type_expr(&mut local, *ty);
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
                    self.expr(env, handler.value, None);
                }
            }
            StmtKind::Import(_) => {}
        }
        Ty::Unit
    }

    pub(super) fn def_type(
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
                if !callee && self.is_meta_fn(id) {
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
                self.bindings.get(&id).cloned().unwrap_or(Ty::Unknown)
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
                let primitive = def.stmt.and_then(|item| {
                    match &self.ast(def.name.span.file).stmt(item).value.kind {
                        StmtKind::Type(decl)
                            if decl.kind == TypeKind::Nominal
                                && matches!(decl.definition, TypeDefinition::Opaque) =>
                        {
                            Some(Ty::Adt(Arc::new(super::Adt {
                                definition: id,
                                kind: AdtKind::Nominal,
                                defining_scope: def.scope,
                                visibility: def.visibility,
                                arguments: Vec::new(),
                            })))
                        }
                        _ => None,
                    }
                });
                if let Some(ty) = primitive {
                    ty
                } else {
                    self.error(Code::E0319, span, "bare type in value expression");
                    Ty::Unknown
                }
            }
            DefinitionKind::Primitive(_) => self.primitive_type(env, &def.name.value, span, callee),
            _ => Ty::Unknown,
        }
    }

    pub(super) fn is_meta_fn(&self, id: DefinitionId) -> bool {
        let def = self.hir.definition(id);
        def.stmt.is_some_and(|stmt| {
            matches!(&self.ast(def.name.span.file).stmt(stmt).value.kind, StmtKind::Function(fun) if fun.is_meta)
        })
    }
}

pub(super) fn substitute(ty: &Ty, generics: &HashMap<DefinitionId, GenericValue>) -> Ty {
    transform(ty, &mut |ty| {
        if let Ty::Param(id) = ty
            && let Some(GenericValue::Type(ty)) = generics.get(id)
        {
            Some(ty.clone())
        } else {
            None
        }
    })
}

pub(super) fn transform(ty: &Ty, f: &mut impl FnMut(&Ty) -> Option<Ty>) -> Ty {
    if let Some(replaced) = f(ty) {
        return replaced;
    }
    let wrap = |t, f: &mut _| Box::new(transform(t, f));
    let member = |m: &Member, f: &mut _| Member {
        mode: m.mode,
        ty: transform(&m.ty, f),
    };
    match ty {
        Ty::Adt(adt) => Ty::Adt(Arc::new(super::Adt {
            arguments: adt
                .arguments
                .iter()
                .map(|arg| match arg {
                    GenericValue::Type(ty) => GenericValue::Type(transform(ty, f)),
                    arg => arg.clone(),
                })
                .collect(),
            ..(**adt).clone()
        })),
        Ty::Tuple(items) => Ty::Tuple(items.iter().map(|item| member(item, f)).collect()),
        Ty::Record(items, open) => Ty::Record(
            items
                .iter()
                .map(|(name, item)| (name.clone(), member(item, f)))
                .collect(),
            *open,
        ),
        Ty::Array(item) => Ty::Array(Box::new(member(item, f))),
        Ty::Map(key, item) => Ty::Map(wrap(key, f), Box::new(member(item, f))),
        Ty::Set(item) => Ty::Set(wrap(item, f)),
        Ty::Option(item) => Ty::Option(wrap(item, f)),
        Ty::Result(ok, err) => Ty::Result(wrap(ok, f), wrap(err, f)),
        Ty::Draft(ty) => Ty::Draft(wrap(ty, f)),
        Ty::TypeValue(Some(ty)) => Ty::TypeValue(Some(wrap(ty, f))),
        Ty::Callable(call) => Ty::Callable(Arc::new(Callable {
            result: transform(&call.result, f),
            parameters: call
                .parameters
                .iter()
                .map(|p| Parameter {
                    ty: transform(&p.ty, f),
                    ..p.clone()
                })
                .collect(),
            ..(**call).clone()
        })),
        _ => ty.clone(),
    }
}

pub(super) fn unknown_callable() -> Callable {
    Callable {
        parameters: Vec::new(),
        result: Ty::Unknown,
        result_mode: Mode::Plain,
        effects: Vec::new(),
        open_effects: false,
        state: Vec::new(),
        open_state: false,
    }
}

pub(super) fn path_name(path: &syntax::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.name.value.as_str())
        .collect::<Vec<_>>()
        .join("::")
}
