use std::{
    collections::{BTreeMap, HashMap, HashSet},
    sync::Arc,
};

use ril_base::{diag::Code, span::Span};
use ril_frontend::{
    hir::{DefinitionId, DefinitionKind},
    parser::FileKind,
    syntax::{
        self, FieldTail, GenericArg, GenericParam, Member as Coordinate, Mode, StateKind, StmtKind,
        Type, TypeDecl, TypeDefinition, TypeId, TypeKind, Variant,
    },
};

use super::{
    Adt, AdtKind, Callable, GenericValue, Member, Parameter, Ty, Value,
    check::{Checker, Env, Phase, path_name, unknown_callable},
    value::static_argument,
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
                self.fits(env, err, expected) || self.sum_subset(err, expected)
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
        let effects = signature
            .obligations
            .effects
            .iter()
            .map(path_name)
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
        Callable {
            parameters: params,
            result,
            result_mode: signature.result_mode,
            effects,
            open_effects: signature.obligations.open_effects,
            state,
            open_state: signature.obligations.open_state,
        }
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

    pub(super) fn type_expr(&mut self, env: &mut Env, id: TypeId) -> Ty {
        let node = self.ast(env.file).ty(id);
        let ty = match &node.value {
            Type::Named(path) => self.named_type(env, path),
            Type::Unit => Ty::Unit,
            Type::Tuple(items) => Ty::Tuple(
                items
                    .iter()
                    .map(|(mode, ty)| self.member(env, mode, *ty))
                    .collect(),
            ),
            Type::Array(mode, item) => Ty::Array(Box::new(self.member(env, mode, *item))),
            Type::Map(key, mode, item) => {
                let key = self.type_expr(env, *key);
                if !self.eligible_key(env, &key, &mut HashSet::new()) {
                    self.error(
                        Code::E0328,
                        node.span,
                        "map key type does not support stable equality",
                    );
                }
                Ty::Map(Box::new(key), Box::new(self.member(env, mode, *item)))
            }
            Type::Result(ok, err) => Ty::Result(
                Box::new(self.type_expr(env, *ok)),
                Box::new(self.type_expr(env, *err)),
            ),
            Type::Option(item) => Ty::Option(Box::new(self.type_expr(env, *item))),
            Type::Record { fields, tail } => {
                let mut map = BTreeMap::new();
                let nominal = env.nominal_fields == Some(node.span);
                for field in fields {
                    let member = self.member(env, &field.storage, field.ty);
                    if !field.attrs.is_empty() && !nominal {
                        self.error(
                            Code::E0708,
                            field.name.span,
                            "metadata requires a nominal root field",
                        );
                    }
                    if let Some(default) = field.default {
                        if !nominal {
                            self.error(
                                Code::E0359,
                                field.name.span,
                                "default requires a nominal root field",
                            );
                        } else if member.mode.mode != Mode::Plain
                            || field.storage.mode_path.is_some()
                        {
                            self.error(
                                Code::E0404,
                                field.name.span,
                                "field defaults require plain access",
                            );
                        }
                        self.check_pure_default(env, default, &member.ty);
                    }
                    self.define_name(&field.name, member.ty.clone());
                    map.insert(field.name.value.clone(), member);
                }
                let mut open = tail.is_some();
                if let Some(FieldTail::Named(name)) = tail
                    && let Some(tail) = self.resolve(name.span).and_then(|id| env.generics.get(&id))
                {
                    match tail {
                        GenericValue::Type(Ty::Record(other, remains_open)) => {
                            open = *remains_open;
                            for (field, member) in other {
                                if let std::collections::btree_map::Entry::Vacant(slot) =
                                    map.entry(field.clone())
                                {
                                    slot.insert(member.clone());
                                } else {
                                    self.error(
                                        Code::E0212,
                                        name.span,
                                        format!("record tail repeats field {field}"),
                                    );
                                }
                            }
                        }
                        GenericValue::Type(Ty::Unknown | Ty::Param(_)) => {}
                        _ => self.error(
                            Code::E0306,
                            name.span,
                            "row tail requires a structural record type",
                        ),
                    }
                }
                Ty::Record(map, open)
            }
            Type::Callable(signature) => {
                Ty::Callable(Arc::new(self.callable(env, signature, false)))
            }
            Type::TypeOf(expr) => {
                let mut shadow = env.clone();
                shadow.shadow = true;
                let ty = self.expr(&mut shadow, *expr, None);
                self.normalize(&ty)
            }
            Type::Unquote(expr) => {
                let mut local = env.clone();
                local.phase = Phase::TypeEval;
                if let Some(Value::Type(ty)) = self.eval_root(&local, *expr, false) {
                    *ty
                } else {
                    let ty = self.expr(&mut local, *expr, None);
                    if let Ty::TypeValue(Some(ty)) = ty {
                        *ty
                    } else {
                        self.require(&local, node.span, &ty, &Ty::TypeValue(None));
                        Ty::Unknown
                    }
                }
            }
            Type::Project { base, field } => {
                let ty = self.type_expr(env, *base);
                self.project(env, field, &ty, node.span, true)
            }
            Type::Mapped {
                storage,
                pattern,
                iterable,
                field,
            } => {
                let Some(Value::Array(values)) = self.eval_root(env, *iterable, true) else {
                    return Ty::Unknown;
                };
                let mut fields = BTreeMap::new();
                for item in values {
                    let mut local = env.clone();
                    self.map_static_bindings(&mut local, *pattern, &item);
                    let member = self.member(&mut local, storage, *field);
                    let key = match item {
                        Value::Str(key) => Some(key),
                        Value::Tuple(items) => items.into_iter().find_map(|item| match item {
                            Value::Str(name) => Some(name),
                            _ => None,
                        }),
                        _ => None,
                    };
                    if let Some(key) = key {
                        fields.insert(key, member);
                    } else {
                        self.error(Code::E0341, node.span, "mapped record keys must be strings");
                    }
                }
                Ty::Record(fields, false)
            }
            Type::PatternBinding(_) | Type::PatternWildcard | Type::PatternLiteral(_) => {
                Ty::Unknown
            }
        };
        self.types.insert(node.span, ty.clone());
        ty
    }

    fn member(&mut self, env: &mut Env, mode: &syntax::Storage, ty: TypeId) -> Member {
        let typed = self.type_expr(env, ty);
        let mode = self.member_mode(env, mode);
        if typed.is_value() && matches!(mode.mode, Mode::Mut | Mode::Shared | Mode::Ref) {
            self.error(
                Code::E0356,
                self.ast(env.file).ty(ty).span,
                "value-type members cannot carry live access",
            );
        }
        Member { mode, ty: typed }
    }

    pub(super) fn named_type(&mut self, env: &mut Env, path: &syntax::Path) -> Ty {
        let Some(last) = path.segments.last() else {
            return Ty::Unknown;
        };
        match last.name.value.as_str() {
            "bool" => return Ty::Bool,
            "int" => return Ty::Int,
            "f64" => return Ty::F64,
            "str" => return Ty::Str,
            "bytes" => return Ty::Bytes,
            "never" => return Ty::Never,
            _ => {}
        }
        let resolved = self.resolve(path.span);
        if let Some(def) = resolved
            && matches!(self.hir.primitive_module(def), Some("Fiber" | "Channel"))
        {
            if last.name.value == "Scope" {
                return Ty::Scope;
            }
            let parameter = last
                .arguments
                .first()
                .map(|arg| self.type_argument(env, arg))
                .unwrap_or(Ty::Unknown);
            return match last.name.value.as_str() {
                "Task" => Ty::Task(Box::new(parameter)),
                "Sender" => Ty::Sender(Box::new(parameter)),
                "Receiver" => Ty::Receiver(Box::new(parameter)),
                "ChannelPair" => super::concurrency::channel_pair(parameter),
                _ => Ty::Unknown,
            };
        }
        if path.segments.len() == 1
            && resolved.is_none_or(|id| {
                matches!(self.hir.definition(id).kind, DefinitionKind::Primitive(_))
            })
        {
            let mut args = last.arguments.iter();
            let mut ty_arg = || {
                args.next()
                    .map(|arg| self.type_argument(env, arg))
                    .unwrap_or(Ty::Unknown)
            };
            match last.name.value.as_str() {
                "Option" => return Ty::Option(Box::new(ty_arg())),
                "Result" => {
                    let ok = ty_arg();
                    let err = ty_arg();
                    return Ty::Result(Box::new(ok), Box::new(err));
                }
                "Set" => {
                    let key = ty_arg();
                    if !self.eligible_key(env, &key, &mut HashSet::new()) {
                        self.error(
                            Code::E0328,
                            path.span,
                            "set element type does not support stable equality",
                        );
                    }
                    return Ty::Set(Box::new(key));
                }
                "Type" => {
                    return Ty::TypeValue((!last.arguments.is_empty()).then(|| Box::new(ty_arg())));
                }
                "Draft" => return Ty::Draft(Box::new(ty_arg())),
                "MemberMode" => return Ty::Mode,
                _ => {}
            }
        }
        let Some(id) = resolved else {
            return Ty::Unknown;
        };
        let def = self.hir.definition(id);
        if def.kind == DefinitionKind::Generic {
            return env
                .generics
                .get(&id)
                .and_then(|arg| match arg {
                    GenericValue::Type(ty) => Some(ty.clone()),
                    _ => None,
                })
                .unwrap_or(Ty::Param(id));
        }
        let Some(stmt) = def.stmt else {
            return Ty::Unknown;
        };
        let StmtKind::Type(decl) = &self.ast(def.name.span.file).stmt(stmt).value.kind else {
            self.error(
                Code::E0306,
                path.span,
                format!("{} does not denote a type", last.name.value),
            );
            return Ty::Unknown;
        };
        let params = if let TypeDefinition::Function(params, _) = &decl.definition {
            params.as_slice()
        } else {
            decl.generics.as_slice()
        };
        let (arguments, mut local) =
            self.type_arguments(env, id, params, &last.arguments, path.span);
        match &decl.definition {
            TypeDefinition::Data(body) if decl.kind == TypeKind::Alias => {
                if !self.resolving.insert(id) {
                    self.error(Code::E0313, path.span, "cyclic transparent type alias");
                    return Ty::Unknown;
                }
                let ty = self.type_expr(&mut local, *body);
                self.resolving.remove(&id);
                ty
            }
            TypeDefinition::Function(_, body) => {
                if arguments
                    .iter()
                    .any(|v| matches!(v, GenericValue::Type(Ty::Param(_))))
                {
                    return Ty::Unknown;
                }
                if u64::try_from(self.stack.len()).unwrap_or(u64::MAX) >= self.budget.min(256) {
                    self.error(
                        Code::E0811,
                        path.span,
                        "type application exceeded the static step budget",
                    );
                    return Ty::Unknown;
                }
                self.stack.push(id);
                local.phase = Phase::TypeEval;
                let value = self.eval_root(&local, *body, true);
                self.stack.pop();
                match value {
                    Some(Value::Type(ty)) => *ty,
                    Some(_) => {
                        self.error(
                            Code::E0306,
                            path.span,
                            "type function must produce a type value",
                        );
                        Ty::Unknown
                    }
                    None => Ty::Unknown,
                }
            }
            _ => self.adt(id, decl, arguments),
        }
    }

    pub(super) fn adt(
        &self,
        id: DefinitionId,
        decl: &TypeDecl,
        arguments: Vec<GenericValue>,
    ) -> Ty {
        let def = self.hir.definition(id);
        let kind = if self.hir.file(def.name.span.file).kind == FileKind::Foreign
            && matches!(decl.kind, TypeKind::Opaque | TypeKind::Nominal)
        {
            AdtKind::Foreign
        } else {
            match (&decl.definition, decl.kind) {
                (TypeDefinition::Sum(_), TypeKind::Opaque) => AdtKind::OpaqueSum,
                (TypeDefinition::Sum(_), _) => AdtKind::Sum,
                (_, TypeKind::Opaque) => AdtKind::Opaque,
                _ => AdtKind::Nominal,
            }
        };
        Ty::Adt(Arc::new(Adt {
            definition: id,
            kind,
            defining_scope: def.scope,
            visibility: def.visibility,
            arguments,
        }))
    }

    fn type_arguments(
        &mut self,
        env: &mut Env,
        id: DefinitionId,
        params: &[GenericParam],
        args: &[GenericArg],
        span: Span,
    ) -> (Vec<GenericValue>, Env) {
        let def = self.hir.definition(id);
        let mut local = Env::new(def.name.span.file, def.scope);
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
            values.push(value);
        }
        (values, local)
    }

    pub(super) fn generic_argument(
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
                    Code::E0306,
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

    pub(super) fn type_argument(&mut self, env: &mut Env, arg: &GenericArg) -> Ty {
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
                GenericArg::Type(_) => ril_base::ice!("type argument was already handled"),
            };
            self.error(Code::E0306, span, "type parameter requires type syntax");
            Ty::Unknown
        }
    }

    pub(super) fn instantiate_adt(&self, adt: &Adt) -> Env {
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

    pub(super) fn representation(&mut self, _env: &Env, adt: &Adt) -> Option<Ty> {
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

    pub(super) fn variant(
        &mut self,
        env: &mut Env,
        id: DefinitionId,
        expected: Option<&Ty>,
        span: Span,
    ) -> Ty {
        let def = self.hir.definition(id);
        let DefinitionKind::Variant(parent) = def.kind else {
            return Ty::Unknown;
        };
        let owner = self.hir.definition(parent);
        let Some(stmt) = owner.stmt else {
            return Ty::Unknown;
        };
        let StmtKind::Type(decl) = &self.ast(owner.name.span.file).stmt(stmt).value.kind else {
            return Ty::Unknown;
        };
        let TypeDefinition::Sum(variants) = &decl.definition else {
            return Ty::Unknown;
        };
        let adt = if let Some(Ty::Adt(known)) = expected
            && known.definition == parent
        {
            Ty::Adt(Arc::clone(known))
        } else {
            let args = decl
                .generics
                .iter()
                .map(|_| GenericValue::Type(self.fresh()))
                .collect();
            self.adt(parent, decl, args)
        };
        let Ty::Adt(value) = &adt else {
            return Ty::Unknown;
        };
        if value.kind == AdtKind::OpaqueSum && env.scope != value.defining_scope {
            self.error(Code::E0308, span, "opaque sum constructors are sealed");
            return Ty::Unknown;
        }
        let mut local = self.instantiate_adt(value);
        for variant in variants {
            if let Variant::Constructor { name, payload, .. } = variant
                && name.value == def.name.value
            {
                return if let Some(payload) = payload {
                    let params = payload
                        .iter()
                        .map(|&ty| Parameter {
                            label: None,
                            ty: self.type_expr(&mut local, ty),
                            mode: Mode::Plain,
                            optional: false,
                            is_meta: false,
                        })
                        .collect();
                    Ty::Callable(Arc::new(Callable {
                        parameters: params,
                        result: adt,
                        result_mode: Mode::New,
                        ..unknown_callable()
                    }))
                } else {
                    adt
                };
            }
        }
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
                use num_traits::ToPrimitive as _;
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
                if !matches!(field, Coordinate::Computed(expr)
                    if matches!(&self.ast(env.file).expr(*expr).value, syntax::Expr::Path(path)
                        if self.resolve(path.span).is_some_and(|id| env.generics.contains_key(&id))))
                {
                    self.error(Code::E0324, span, "projection coordinate must be static");
                }
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

    fn eligible_key(&mut self, env: &Env, ty: &Ty, seen: &mut HashSet<DefinitionId>) -> bool {
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

    pub(super) fn validate_generic_uses(
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
        local.generics.clone_from(supplied);
        for param in &function.generics {
            let Some(definition) = self.resolve(param.name.span) else {
                continue;
            };
            if let Some(GenericValue::Type(actual)) = supplied.get(&definition) {
                let actual = self.normalize(actual);
                let domain: Vec<_> = param
                    .bound
                    .iter()
                    .map(|&ty| self.type_expr(&mut local, ty))
                    .collect();
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
                        Code::E0301,
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

    pub(super) fn call_argument_types(
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
