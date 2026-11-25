use std::{
    collections::{BTreeMap, HashSet},
    sync::Arc,
};

use ril_hir::{BuiltinSum, DefinitionId, DefinitionKind};
use ril_source::{diag::Code, span::Span};
use ril_syntax::{
    lexer::{Word, word_kind},
    parser::FileKind,
    syntax::{
        self, FieldTail, Mode, StmtKind, Type, TypeDecl, TypeDefinition, TypeId, TypeKind, Variant,
    },
};

use crate::ty::{
    Adt, AdtKind, Callable, GenericValue, Member, Parameter, Ty, Value,
    check::{Checker, Env, Phase, unknown_callable},
};

impl Checker<'_> {
    pub(in crate::ty) fn type_expr(&mut self, env: &mut Env, id: TypeId) -> Ty {
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
                    } else {
                        for &attribute in &field.attrs {
                            self.metadata(env, attribute);
                        }
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
            } => self.mapped_record(env, storage, *pattern, *iterable, *field, node.span),
            Type::PatternBinding(_) | Type::PatternWildcard | Type::PatternLiteral(_) => {
                Ty::Unknown
            }
        };
        self.types.insert(node.span, ty.clone());
        ty
    }

    fn mapped_record(
        &mut self,
        env: &Env,
        storage: &syntax::Storage,
        pattern: syntax::PatternId,
        iterable: syntax::ExprId,
        field: TypeId,
        span: Span,
    ) -> Ty {
        let Some(iterable) = self.eval_root(env, iterable, !env.checking_type_template) else {
            return Ty::Unknown;
        };
        let items: Vec<_> = match iterable {
            Value::Array(items) => items,
            Value::Str(text) => text.chars().map(|ch| Value::Str(ch.to_string())).collect(),
            Value::Map(entries) => entries
                .into_iter()
                .map(|(key, value)| Value::Tuple(vec![key, value]))
                .collect(),
            _ => {
                self.error(
                    Code::E0341,
                    span,
                    "mapped record requires an iterable of coordinates",
                );
                return Ty::Unknown;
            }
        };
        let inferred_mode = storage.mode_path.as_ref().is_some_and(|path| {
            path.segments
                .last()
                .is_some_and(|part| word_kind(&part.name.value) == Some(Word::Value))
        });
        let mut fields = BTreeMap::new();
        for item in items {
            let key = match (&item, inferred_mode) {
                (Value::Str(key), false) => Some(key),
                (Value::Tuple(parts), true) => match parts.as_slice() {
                    [Value::Mode(_), Value::Str(key)] => Some(key),
                    _ => None,
                },
                _ => None,
            };
            let Some(key) = key else {
                self.error(
                    Code::E0341,
                    span,
                    "mapped record coordinate has the wrong shape",
                );
                continue;
            };
            if word_kind(key) != Some(Word::Value) {
                self.error(
                    Code::E0815,
                    span,
                    "mapped record key is not a valid field label",
                );
                continue;
            }
            let mut local = env.clone();
            self.map_static_bindings(&mut local, pattern, &item);
            let member = self.member(&mut local, storage, field);
            if fields.insert(key.clone(), member).is_some() {
                self.error(Code::E0210, span, "duplicate mapped record field");
            }
        }
        Ty::Record(fields, false)
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

    pub(in crate::ty) fn named_type(&mut self, env: &mut Env, path: &syntax::Path) -> Ty {
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
        if let Some(kind) = resolved.and_then(|id| self.hir.builtin_sum(id)) {
            if last.arguments.len() != usize::from(kind.has_parameter()) {
                self.error(Code::E0340, path.span, "incorrect number of type arguments");
            }
            let element = last
                .arguments
                .first()
                .map(|arg| self.type_argument(env, arg));
            return self.builtin_sum_type(kind, element);
        }
        if let Some(def) = resolved
            && matches!(self.hir.primitive_module(def), Some("Fiber" | "Channel"))
            && matches!(self.hir.definition(def).kind, DefinitionKind::Primitive(_))
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
                "ChannelPair" => crate::ty::concurrency::channel_pair(parameter),
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
                "PanicInfo" => return Ty::PanicInfo,
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

    pub(in crate::ty) fn adt(
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

    pub(in crate::ty) fn builtin_sum_type(&self, kind: BuiltinSum, element: Option<Ty>) -> Ty {
        let definition = self.hir.builtin_sum_id(kind);
        let def = self.hir.definition(definition);
        Ty::Adt(Arc::new(Adt {
            definition,
            kind: AdtKind::Sum,
            defining_scope: def.scope,
            visibility: def.visibility,
            arguments: if kind.has_parameter() {
                vec![GenericValue::Type(element.unwrap_or(Ty::Unknown))]
            } else {
                Vec::new()
            },
        }))
    }

    pub(in crate::ty) fn variant(
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
        if let Some(kind) = self.hir.builtin_sum(parent) {
            let result = if let Some(Ty::Adt(target)) = expected
                && target.definition == parent
            {
                Ty::Adt(Arc::clone(target))
            } else {
                let element = kind.has_parameter().then(|| self.fresh());
                self.builtin_sum_type(kind, element)
            };
            let Ty::Adt(adt) = &result else {
                return Ty::Unknown;
            };
            let payload = self
                .sum_variants(adt)
                .remove(&def.name.value)
                .unwrap_or_default();
            if payload.is_empty() {
                return result;
            }
            return Ty::Callable(Arc::new(Callable {
                parameters: payload
                    .into_iter()
                    .map(|ty| Parameter {
                        label: None,
                        mode: Mode::Plain,
                        ty,
                        optional: false,
                        is_meta: false,
                    })
                    .collect(),
                result,
                result_mode: Mode::New,
                ..unknown_callable()
            }));
        }
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
}
