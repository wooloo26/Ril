use std::{collections::HashSet, sync::Arc};

use ril_base::{diag::Code, span::Span};
use ril_frontend::{
    hir::{BuiltinSum, TextBuiltin},
    syntax::{self, Argument, Expr, Mode},
};

use crate::ty::{
    Adt, AdtKind, Callable, GenericValue, Member, Parameter, Ty,
    check::{Checker, Env, Phase, unknown_callable},
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
            "Some" | "Ok" | "Err" => {
                let payload = self.fresh();
                let result = match name {
                    "Some" => Ty::Option(Box::new(payload.clone())),
                    "Ok" => Ty::Result(Box::new(payload.clone()), Box::new(self.fresh())),
                    _ => Ty::Result(Box::new(self.fresh()), Box::new(payload.clone())),
                };
                Ty::Callable(Arc::new(Callable {
                    parameters: vec![Parameter {
                        label: None,
                        mode: Mode::Plain,
                        ty: payload,
                        optional: false,
                        is_meta: false,
                    }],
                    result,
                    result_mode: Mode::New,
                    ..unknown_callable()
                }))
            }
            "Let" => Ty::Mode,
            "Var" | "Mut" | "Ref" | "SharedMut" | "VarMut" | "VarRef" | "VarSharedMut" => Ty::Mode,
            "bool" | "int" | "f64" | "str" | "bytes" | "never" | "Type" | "PanicInfo"
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
        let mut opened = HashSet::new();
        while let Ty::Adt(adt) = &ty {
            if matches!(adt.kind, AdtKind::Opaque | AdtKind::OpaqueSum)
                && adt.defining_scope != env.scope
            {
                self.error(Code::E0308, span, "opaque representation is sealed");
                return;
            }
            if adt.kind != AdtKind::Opaque || !opened.insert(adt.definition) {
                break;
            }
            let Some(representation) = self.representation(env, adt) else {
                break;
            };
            ty = self.normalize(&representation);
        }
        if ty.is_value()
            || matches!(
                &ty,
                Ty::Adt(adt) if adt.kind == AdtKind::Foreign
            )
            || matches!(
                ty,
                Ty::Callable(_)
                    | Ty::PanicInfo
                    | Ty::Draft(_)
                    | Ty::Scope
                    | Ty::Task(_)
                    | Ty::Sender(_)
                    | Ty::Receiver(_)
            )
        {
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
        if root && (ty.is_value() || matches!(ty, Ty::Callable(_))) {
            return true;
        }
        match ty {
            Ty::Draft(_)
            | Ty::Scope
            | Ty::Task(_)
            | Ty::Sender(_)
            | Ty::Receiver(_)
            | Ty::TypeValue(_)
            | Ty::Mode => true,
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
                if adt.kind == AdtKind::Foreign {
                    return true;
                }
                if proof
                    .active
                    .iter()
                    .rev()
                    .find(|outer| outer.definition == adt.definition)
                    .is_some_and(|outer| !Self::nested_type_argument(outer, &adt))
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
                        .is_some_and(|ty| self.nonclonable(env, &ty, false, proof)),
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
            Ty::Result(ok, error) => {
                self.nonclonable(env, &ok, false, proof)
                    || self.nonclonable(env, &error, false, proof)
            }
            Ty::Set(item) | Ty::Option(item) => self.nonclonable(env, &item, false, proof),
            _ => false,
        }
    }

    fn nested_type_argument(outer: &Adt, inner: &Adt) -> bool {
        // A finite type argument may use the same constructor. Following
        // that argument is distinct from expanding a recursive definition.
        outer.arguments.iter().any(|argument| {
            let GenericValue::Type(ty) = argument else {
                return false;
            };
            let mut nested = false;
            crate::ty::check::transform(ty, &mut |part| {
                nested |= matches!(part, Ty::Adt(application) if application.as_ref() == inner);
                None
            });
            nested
        })
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
        if name == "None" {
            self.error(Code::E0338, span, "unit constructor is not callable");
            return Ty::Unknown;
        }
        let context_arg = match (name, expected) {
            ("clone", expected) => expected,
            ("Some", Some(Ty::Option(ty)))
            | ("Ok", Some(Ty::Result(ty, _)))
            | ("Err", Some(Ty::Result(_, ty))) => Some(ty.as_ref()),
            _ => None,
        };
        let mut types = Vec::new();
        for arg in args {
            types.push(self.expr(env, arg.value, context_arg));
        }
        let first = types
            .first()
            .cloned()
            .unwrap_or(if matches!(name, "Some" | "Ok" | "Err") {
                Ty::Unit
            } else {
                Ty::Unknown
            });
        let arity = match name {
            "panic" | "print" | "println" | "len" | "clone" | "inner" | "inspect" | "type_name"
            | "coords" | "variants" | "to_f64" | "to_int" | "trunc" | "absorb_panic"
            | "panic_message" => Some(1..=1),
            "Some" | "Ok" | "Err" => Some(0..=1),
            "assert" => Some(1..=2),
            "has_default" | "contains" | "push" | "derive" => Some(2..=2),
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
            "read" | "write" => {
                self.require(env, span, &first, &Ty::Str);
                if name == "write"
                    && let Some(content) = types.get(1)
                {
                    self.require(env, span, content, &Ty::Str);
                }
                if !env.shadow {
                    env.effects_seen.insert("io".into());
                }
                Ty::Result(
                    Box::new(if name == "read" { Ty::Str } else { Ty::Unit }),
                    Box::new(Ty::Str),
                )
            }
            "Some" => Ty::Option(Box::new(first)),
            "Ok" => Ty::Result(
                Box::new(first),
                expected
                    .and_then(|ty| match ty {
                        Ty::Result(_, err) => Some(err.clone()),
                        _ => None,
                    })
                    .unwrap_or_else(|| Box::new(self.fresh())),
            ),
            "Err" => Ty::Result(
                expected
                    .and_then(|ty| match ty {
                        Ty::Result(ok, _) => Some(ok.clone()),
                        _ => None,
                    })
                    .unwrap_or_else(|| Box::new(self.fresh())),
                Box::new(first),
            ),
            "panic" | "print" | "println" => {
                self.require(env, span, &first, &Ty::Str);
                if name == "panic" {
                    Ty::Never
                } else {
                    if !env.shadow {
                        env.effects_seen.insert("io".into());
                    }
                    Ty::Unit
                }
            }
            "assert" => {
                self.require(env, span, &first, &Ty::Bool);
                if let Some(message) = types.get(1) {
                    self.require(env, span, message, &Ty::Str);
                }
                Ty::Unit
            }
            "len" => {
                if !matches!(
                    first,
                    Ty::Str
                        | Ty::Bytes
                        | Ty::Array(_)
                        | Ty::Map(..)
                        | Ty::Set(_)
                        | Ty::Unknown
                        | Ty::Param(_)
                ) {
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
            "inner" => match if let Ty::Draft(wrapped) = &first {
                wrapped
            } else {
                &first
            } {
                Ty::Adt(adt) if adt.kind == AdtKind::Foreign => {
                    self.error(Code::E0907, span, "foreign representation is sealed");
                    Ty::Unknown
                }
                Ty::Adt(adt) if adt.kind == AdtKind::Nominal => {
                    self.representation(env, adt).unwrap_or(Ty::Unknown)
                }
                Ty::Unknown => Ty::Unknown,
                _ => {
                    self.error(Code::E0301, span, "inner requires a nominal wrapper");
                    Ty::Unknown
                }
            },
            "to_f64" => {
                self.require(env, span, &first, &Ty::Int);
                Ty::F64
            }
            "to_int" | "trunc" | "convert" => {
                self.require(env, span, &first, &Ty::F64);
                Ty::Option(Box::new(Ty::Int))
            }
            "coords" => {
                let key = if let Ty::TypeValue(Some(ty)) = first {
                    match *ty {
                        Ty::Record(..) => Ty::Str,
                        Ty::Tuple(_) => Ty::Int,
                        Ty::Adt(adt) if adt.kind == AdtKind::Foreign => {
                            self.error(Code::E0907, span, "foreign representation is sealed");
                            Ty::Unknown
                        }
                        Ty::Adt(adt)
                            if matches!(adt.kind, AdtKind::Opaque | AdtKind::OpaqueSum)
                                && adt.defining_scope != env.scope =>
                        {
                            self.error(Code::E0308, span, "opaque representation is sealed");
                            Ty::Unknown
                        }
                        Ty::Adt(adt)
                            if matches!(self.representation(env, &adt), Some(Ty::Record(..))) =>
                        {
                            Ty::Str
                        }
                        Ty::Param(_) | Ty::Unknown => Ty::Unknown,
                        _ => {
                            self.error(Code::E0358, span, "coords requires a tuple or record type");
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
            "variants" => Ty::Array(Box::new(Member::plain(Ty::Str))),
            "contains" | "has_default" => Ty::Bool,
            "type_name" => Ty::Str,
            "inspect" => {
                self.inspection_scopes.insert(span, env.scope);
                Ty::Str
            }
            "panic_message" => {
                self.require(env, span, &first, &Ty::PanicInfo);
                Ty::Str
            }
            "PanicInfo" => {
                self.error(Code::E0301, span, "PanicInfo has no accessible constructor");
                Ty::Unknown
            }
            "push" => {
                let target = if let Ty::Draft(inner) = &first {
                    inner.as_ref()
                } else {
                    &first
                };
                match self.normalize(target) {
                    Ty::Array(member) => {
                        if let Some(item) = types.get(1) {
                            self.require(env, span, item, &member.ty);
                        }
                    }
                    Ty::Unknown | Ty::Infer(_) | Ty::Param(_) => {}
                    _ => self.error(Code::E0301, span, "Array::push requires an array"),
                }
                Ty::Unit
            }
            "derive" => first,
            "absorb_panic" => match first {
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
                    Ty::Result(
                        Box::new(call.result.clone()),
                        Box::new(self.builtin_sum_type(BuiltinSum::PanicError, None)),
                    )
                }
                _ => Ty::Unknown,
            },
            _ => Ty::Unknown,
        }
    }

    pub(super) fn text_call(
        &mut self,
        env: &mut Env,
        builtin: TextBuiltin,
        args: &[Argument],
        span: Span,
    ) -> Ty {
        use TextBuiltin::*;
        let option = |ty| Ty::Option(Box::new(ty));
        let int_array = || Ty::Array(Box::new(Member::plain(Ty::Int)));
        let (inputs, output) = match builtin {
            Join => (
                vec![Ty::Array(Box::new(Member::plain(Ty::Str))), Ty::Str],
                Ty::Str,
            ),
            StartsWith | EndsWith => (vec![Ty::Str, Ty::Str], Ty::Bool),
            ScalarAt => (vec![Ty::Str, Ty::Int], option(Ty::Int)),
            ByteAt => (vec![Ty::Bytes, Ty::Int], option(Ty::Int)),
            Scalars => (vec![Ty::Str], int_array()),
            ToArray => (vec![Ty::Bytes], int_array()),
            FromScalars => (vec![int_array()], option(Ty::Str)),
            FromArray => (vec![int_array()], option(Ty::Bytes)),
            EncodeUtf8 => (vec![Ty::Str], Ty::Bytes),
            DecodeUtf8 => (vec![Ty::Bytes], option(Ty::Str)),
        };
        let Some(order) = builtin.argument_order(
            args.iter()
                .map(|arg| arg.name.as_ref().map(|label| label.value.as_str())),
        ) else {
            self.error(
                Code::E0314,
                span,
                "text arguments do not match the primitive's parameters",
            );
            return output;
        };
        let mut written_types = vec![(None, false); args.len()];
        for (index, (written, expected)) in order.into_iter().zip(inputs).enumerate() {
            let allows_live_arg = index == 0 && matches!(builtin, Join | FromScalars | FromArray);
            if let Some(slot) = written_types.get_mut(written) {
                *slot = (Some(expected), allows_live_arg);
            }
        }
        for (arg, (ty, allows_live_arg)) in args.iter().zip(written_types) {
            if let Some(ty) = ty {
                self.expect(env, arg.value, &ty);
            }
            if !(arg.mode == Mode::Plain || allows_live_arg) {
                self.error(
                    Code::E0406,
                    self.ast(env.file).expr(arg.value).span,
                    "text primitive argument mode does not match",
                );
            }
        }
        output
    }

    pub(super) fn reflect_call(
        &mut self,
        env: &mut Env,
        path: &syntax::Path,
        args: &[Argument],
        expected: Option<&Ty>,
        span: Span,
    ) -> Ty {
        let Some(member) = path.segments.last() else {
            return Ty::Unknown;
        };
        let arity = if member.name.value == "attrs" { 1 } else { 2 };
        if args.len() != arity {
            self.error(Code::E0314, span, "incorrect metadata query arity");
            return Ty::Unknown;
        }
        if member.arguments.len() > 2 {
            self.error(
                Code::E0340,
                span,
                "metadata query takes target and attribute types",
            );
        }
        let target = Ty::TypeValue(
            member
                .arguments
                .first()
                .map(|arg| Box::new(self.type_argument(env, arg))),
        );
        if let Some(value) = args.first() {
            self.expect(env, value.value, &target);
        }
        if let Some(key) = args.get(1) {
            self.expect(env, key.value, &Ty::Str);
        }
        let attribute = member
            .arguments
            .get(1)
            .map(|arg| self.type_argument(env, arg))
            .or_else(|| match expected {
                Some(Ty::Array(member)) => Some(member.ty.clone()),
                _ => None,
            });
        let Some(attribute) = attribute else {
            self.error(
                Code::E0344,
                span,
                "metadata query requires an attribute type",
            );
            return Ty::Unknown;
        };
        let result = Ty::Array(Box::new(Member::plain(attribute)));
        self.types.insert(span, result.clone());
        if env.phase == Phase::Runtime && !env.shadow {
            self.eval_metadata_root(env, path, args, span);
        }
        result
    }
}
