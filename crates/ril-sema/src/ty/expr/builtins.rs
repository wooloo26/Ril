use std::sync::Arc;

use ril_hir::StdType;
use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::{self, Argument, Expr, Mode};

use crate::ty::{
    Adt, AdtKind, Callable, GenericValue, Member, Parameter, Ty,
    check::{Checker, Env, unknown_callable},
};

#[derive(Default)]
struct CloneProof {
    active: Vec<Arc<Adt>>,
    unresolved: bool,
}

impl Checker<'_> {
    pub(in crate::ty) fn primitive_type(
        &mut self,
        _env: &Env,
        name: &str,
        span: Span,
        callee: bool,
    ) -> Ty {
        match name {
            "bool" | "int" | "f64" | "str" | "bytes" | "never" | "Type" | "Set" | "Derived"
            | "Nominal" | "KeyOf"
                if !callee =>
            {
                self.error(Code::E0319, span, "type value requires angle quotation");
                Ty::Unknown
            }
            _ => Ty::Unknown,
        }
    }

    fn check_derive_root(&mut self, env: &Env, ty: &Ty, span: Span) {
        let mut ty = self.normalize(ty);
        if self.is_must_consume_ty(env, &ty) {
            self.error(
                Code::E0536,
                span,
                "derive cannot operate on a must-consume type",
            );
            return;
        }
        if self.is_value_ty(env, &ty) {
            self.error(
                Code::E0536,
                span,
                "derive requires a shared-object snapshot",
            );
            return;
        }
        let mut active: Vec<Arc<Adt>> = Vec::new();
        while let Ty::Adt(adt) = &ty {
            if matches!(adt.kind, AdtKind::Opaque | AdtKind::OpaqueSum)
                && adt.defining_scope != env.scope
                && self.hir.std_type(adt.definition) != Some(StdType::Set)
            {
                self.error(Code::E0308, span, "opaque representation is sealed");
                return;
            }
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
            let Some(representation) = self.representation(env, adt) else {
                break;
            };
            ty = self.normalize(&representation);
        }
        if ty.is_primitive_value() || matches!(ty, Ty::Callable(_) | Ty::Draft(_)) {
            self.error(
                Code::E0536,
                span,
                "derive requires a shared-object snapshot",
            );
        }
    }

    pub(in crate::ty) fn check_clone(&mut self, env: &Env, ty: &Ty, span: Span, can_defer: bool) {
        let mut proof = CloneProof::default();
        if self.nonclonable(env, ty, true, &mut proof) || proof.unresolved && !can_defer {
            self.error(Code::E0301, span, "clone requires a clonable shared object");
        } else if proof.unresolved {
            self.pending_clone_checks
                .push((env.clone(), ty.clone(), span));
        }
    }

    fn nonclonable(&mut self, env: &Env, ty: &Ty, root: bool, proof: &mut CloneProof) -> bool {
        let ty = self.normalize(ty);
        if root && (ty.is_primitive_value() || matches!(ty, Ty::Callable(_))) {
            return true;
        }
        match ty {
            Ty::Draft(_) | Ty::TypeValue(_) | Ty::Mode => true,
            Ty::Callable(c) if c.is_ctl => true,
            Ty::Param(id) => {
                // A type match can select one type from the declared domain.
                if let Some(GenericValue::Type(ty)) = env.generics.get(&id)
                    && *ty != Ty::Param(id)
                {
                    return self.nonclonable(env, ty, root, proof);
                }
                env.domains.get(&id).is_none_or(|domain| {
                    domain
                        .iter()
                        .any(|ty| self.nonclonable(env, ty, root, proof))
                })
            }
            Ty::Projection(..) => true,
            Ty::Infer(_) => {
                proof.unresolved = true;
                false
            }
            Ty::Adt(adt) => {
                if adt.is_linear {
                    return true;
                }
                if proof
                    .active
                    .iter()
                    .rev()
                    .find(|outer| outer.definition == adt.definition)
                    .is_some_and(|outer| !crate::ty::nested_type_argument(outer, &adt))
                {
                    return false;
                }
                proof.active.push(Arc::clone(&adt));
                let invalid = match adt.kind {
                    AdtKind::Sum | AdtKind::OpaqueSum => self
                        .sum_variants(&adt)
                        .values()
                        .flatten()
                        .any(|ty| self.nonclonable(env, ty, false, proof)),
                    _ => self
                        .representation(env, &adt)
                        .is_some_and(|ty| self.nonclonable(env, &ty, root, proof)),
                };
                proof.active.pop();
                invalid
            }
            Ty::Tuple(items) => items
                .iter()
                .any(|item| self.nonclonable(env, &item.ty, false, proof)),
            Ty::Record(_, true) => true,
            Ty::Record(fields, false) => fields
                .values()
                .any(|field| self.nonclonable(env, &field.ty, false, proof)),
            Ty::Array(item) => self.nonclonable(env, &item.ty, false, proof),
            Ty::Map(key, item) => {
                self.nonclonable(env, &key, false, proof)
                    || self.nonclonable(env, &item.ty, false, proof)
            }
            _ => false,
        }
    }

    pub(super) fn primitive_call(
        &mut self,
        env: &mut Env,
        name: &str,
        args: &[Argument],
        expected: Option<&Ty>,
        span: Span,
    ) -> Ty {
        if name == "derive"
            && let [base, update] = args
        {
            let base = self.expr(env, base.value, expected);
            self.check_derive_root(env, &base, span);
            let callback = Ty::Callable(Arc::new(Callable {
                parameters: vec![Parameter {
                    label: None,
                    mode: Mode::Mut,
                    ty: Ty::Draft(Box::new(base.clone())),
                    optional: false,
                    is_meta: false,
                }],
                result: Ty::Unit,
                result_mode: Mode::Infer,
                open_state: true,
                open_effects: true,
                ..unknown_callable()
            }));
            self.expect(env, update.value, &callback);
            return base;
        }
        let context_arg = if name == "clone" { expected } else { None };
        let mut types = Vec::new();
        for arg in args {
            types.push(self.expr(env, arg.value, context_arg));
        }
        let first = types.first().cloned().unwrap_or(Ty::Unknown);
        let arity = match name {
            "len" | "clone" | "inner" | "fields" | "sum_tags" | "recover" | "unwind_ctl" => {
                Some(1..=1)
            }
            "has_default" | "derive" => Some(2..=2),
            _ => None,
        };
        if arity.is_some_and(|range| !range.contains(&args.len())) {
            self.error(
                Code::E0314,
                span,
                format!("invalid argument count for {name}"),
            );
        }
        match name {
            "len" => {
                if let Some(arg) = args.first()
                    && arg.mode != Mode::Plain
                {
                    let arg_span = self.ast(env.file).expr(arg.value).span;
                    if self.is_value_ty(env, &first) {
                        self.error(
                            Code::E0401,
                            arg_span,
                            "value-type argument cannot carry live authority",
                        );
                    } else if arg.mode != Mode::Ref {
                        self.error(Code::E0406, arg_span, "len accepts plain or ref access");
                    }
                }
                let len_target = match &first {
                    Ty::Draft(inner) => inner.as_ref(),
                    other => other,
                };
                if !matches!(
                    len_target,
                    Ty::Str | Ty::Bytes | Ty::Array(_) | Ty::Map(..) | Ty::Unknown | Ty::Param(_)
                ) && !len_target.is_set(self.hir)
                {
                    self.error(
                        Code::E0301,
                        span,
                        "len requires text, bytes, or a collection",
                    );
                }
                Ty::Int
            }
            "clone" => {
                self.check_clone(env, &first, span, true);
                first
            }
            "unwind_ctl" => {
                if let Some(arg) = args.first() {
                    let arg_span = self.ast(env.file).expr(arg.value).span;
                    if arg.mode != Mode::Plain {
                        self.error(
                            Code::E0406,
                            arg_span,
                            "unwind_ctl takes a plain ctl(...) continuation without an access mode",
                        );
                    }
                    let norm = self.normalize(&first);
                    if !matches!(&norm, Ty::Callable(c) if c.is_ctl)
                        && !matches!(norm, Ty::Unknown | Ty::Infer(_))
                    {
                        self.error(
                            Code::E0301,
                            arg_span,
                            "unwind_ctl requires a ctl(...) continuation",
                        );
                    }
                }
                Ty::Unit
            }
            "inner" => {
                let first_is_ctl = self.is_ctl_ty(env, &first);
                let first_is_linear = self.is_linear_root_ty(env, &first);
                let first_is_user_linear = first_is_linear && !first_is_ctl;
                if let Some(arg) = args.first()
                    && matches!(arg.mode, Mode::Ref | Mode::Mut | Mode::Shared)
                {
                    let arg_span = self.ast(env.file).expr(arg.value).span;
                    if first_is_ctl {
                        self.error(
                            Code::E0401,
                            arg_span,
                            "ctl continuation cannot carry live authority",
                        );
                    } else if first_is_user_linear && arg.mode == Mode::Shared {
                        self.error(
                            Code::E0401,
                            arg_span,
                            "linear type cannot carry shared ^mut authority",
                        );
                    } else if !first_is_user_linear && self.is_value_ty(env, &first) {
                        self.error(
                            Code::E0401,
                            arg_span,
                            "value-type argument cannot carry live authority",
                        );
                    }
                }
                let is_draft = matches!(first, Ty::Draft(_));
                let target = match &first {
                    Ty::Draft(wrapped) => wrapped.as_ref(),
                    other => other,
                };
                let inner_ty = match target {
                    Ty::Adt(adt)
                        if adt.kind == AdtKind::Opaque && adt.defining_scope != env.scope =>
                    {
                        self.error(Code::E0308, span, "opaque representation is sealed");
                        Ty::Unknown
                    }
                    Ty::Adt(adt) if matches!(adt.kind, AdtKind::Nominal | AdtKind::Opaque) => {
                        self.representation(env, adt).unwrap_or(Ty::Unknown)
                    }
                    Ty::Unknown | Ty::Param(_) | Ty::Infer(_) => Ty::Unknown,
                    _ => {
                        self.error(Code::E0301, span, "inner requires a nominal wrapper");
                        Ty::Unknown
                    }
                };
                if let Some(arg) = args.first()
                    && matches!(arg.mode, Mode::Ref | Mode::Mut)
                    && self.is_must_consume_ty(env, &inner_ty)
                {
                    self.error(
                        Code::E0548,
                        span,
                        "cannot unwrap a must-consume payload through ref or mut access",
                    );
                }
                if is_draft && inner_ty != Ty::Unknown {
                    Ty::Draft(Box::new(inner_ty))
                } else {
                    inner_ty
                }
            }
            "fields" => {
                let key = if let Ty::TypeValue(Some(ty)) = first {
                    match self.normalize(&ty) {
                        Ty::Record(..) => Ty::Str,
                        Ty::Tuple(_) | Ty::Unit => Ty::Int,
                        Ty::Adt(adt)
                            if matches!(adt.kind, AdtKind::Opaque | AdtKind::OpaqueSum)
                                && adt.defining_scope != env.scope =>
                        {
                            self.error(Code::E0308, span, "opaque representation is sealed");
                            Ty::Unknown
                        }
                        Ty::Adt(adt) => match self.representation(env, &adt) {
                            Some(Ty::Record(..)) => Ty::Str,
                            Some(Ty::Tuple(_) | Ty::Unit) => Ty::Int,
                            _ => {
                                self.error(
                                    Code::E0358,
                                    span,
                                    "fields requires a tuple or record type",
                                );
                                Ty::Unknown
                            }
                        },
                        Ty::Param(_) | Ty::Unknown | Ty::Infer(_) => Ty::Unknown,
                        _ => {
                            self.error(Code::E0358, span, "fields requires a tuple or record type");
                            Ty::Unknown
                        }
                    }
                } else {
                    Ty::Unknown
                };
                Ty::Array(Box::new(Member::plain(Ty::Tuple(vec![
                    Member::plain(Ty::Mode),
                    Member::plain(key),
                ]))))
            }
            "sum_tags" => {
                if let Ty::TypeValue(Some(ty)) = first {
                    match self.normalize(&ty) {
                        Ty::Adt(adt)
                            if adt.kind == AdtKind::OpaqueSum
                                && adt.defining_scope != env.scope =>
                        {
                            self.error(Code::E0308, span, "opaque representation is sealed");
                        }
                        Ty::Adt(adt) if matches!(adt.kind, AdtKind::Sum | AdtKind::OpaqueSum) => {
                            let def = self.hir.definition(adt.definition);
                            let extensible = def.stmt.is_some_and(|item| {
                                matches!(
                                    &self.ast(def.name.span.file).stmt(item).value.kind,
                                    syntax::StmtKind::Type(decl)
                                        if matches!(&decl.definition, syntax::TypeDefinition::Sum(vs)
                                            if vs.iter().any(|v| matches!(v, syntax::Variant::Extensible)))
                                )
                            });
                            if extensible && !self.hir.same_package(def.scope, env.scope) {
                                self.error(
                                    Code::E0308,
                                    span,
                                    "extensible sum variants are sealed outside their defining package",
                                );
                            }
                        }
                        Ty::Param(_) | Ty::Unknown | Ty::Infer(_) => {}
                        _ => {
                            self.error(Code::E0301, span, "sum_tags requires a sum type");
                        }
                    }
                }
                Ty::Array(Box::new(Member::plain(Ty::Str)))
            }
            "has_default" => {
                if let Ty::TypeValue(Some(ty)) = &first {
                    match self.normalize(ty) {
                        Ty::Adt(adt)
                            if matches!(adt.kind, AdtKind::Opaque | AdtKind::OpaqueSum)
                                && adt.defining_scope != env.scope =>
                        {
                            self.error(Code::E0308, span, "opaque representation is sealed");
                        }
                        Ty::Record(..) | Ty::Param(_) | Ty::Unknown | Ty::Infer(_) => {}
                        Ty::Adt(adt)
                            if matches!(self.representation(env, &adt), Some(Ty::Record(..))) => {}
                        _ => {
                            self.error(
                                Code::E0358,
                                span,
                                "Reflect::has_default requires a record type",
                            );
                        }
                    }
                }
                if let Some(key_ty) = types.get(1) {
                    self.require(env, span, key_ty, &Ty::Str);
                }
                Ty::Bool
            }
            "derive" => first,
            "recover" => match self.normalize(&first) {
                Ty::Callable(call) if call.parameters.is_empty() => {
                    if args.first().is_some_and(|arg| {
                        !matches!(
                            self.ast(env.file).expr(arg.value).value,
                            Expr::Closure { .. }
                        )
                    }) && (call.open_effects || !call.effects.is_empty())
                    {
                        self.error(
                            Code::E0608,
                            span,
                            "panic action requires a closed empty effect set",
                        );
                    }
                    self.make_result(
                        call.result.clone(),
                        self.std_adt(StdType::PanicError, Vec::new()),
                    )
                }
                Ty::Callable(_) => {
                    self.error(
                        Code::E0314,
                        span,
                        "Panic::recover action must take zero arguments",
                    );
                    Ty::Unknown
                }
                Ty::Unknown | Ty::Infer(_) | Ty::Never => Ty::Unknown,
                _ => {
                    self.error(
                        Code::E0338,
                        span,
                        "Panic::recover requires a zero-argument callable",
                    );
                    Ty::Unknown
                }
            },
            _ => Ty::Unknown,
        }
    }
}
