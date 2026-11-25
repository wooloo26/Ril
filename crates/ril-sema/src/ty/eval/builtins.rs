use num_bigint::BigInt;
use num_traits::{FromPrimitive, Signed, ToPrimitive};
use ril_hir::{DefinitionId, TextBuiltin};
use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::{self, ExprId, StmtKind, Type, TypeDefinition, Variant};

use super::{Eval, Signal, defect, integer, none, nonstatic};
use crate::ty::{
    Adt, AdtKind, Ty, Value,
    check::{Checker, Env},
    value::ieee_equal,
};

pub(super) fn eval_text(builtin: TextBuiltin, args: &[Value], span: Span) -> Eval {
    use TextBuiltin::*;
    let option = |value: Option<Value>| {
        value.map_or_else(none, |value| Value::Tag("Some".into(), vec![value]))
    };
    match (builtin, args) {
        (Join, [Value::Array(parts), Value::Str(separator)]) => {
            let parts = parts
                .iter()
                .map(|part| match part {
                    Value::Str(text) => Ok(text.as_str()),
                    _ => Err(nonstatic(span)),
                })
                .collect::<Eval<Vec<_>>>()?;
            Ok(Value::Str(parts.join(separator)))
        }
        (StartsWith, [Value::Str(text), Value::Str(pattern)]) => {
            Ok(Value::Bool(text.starts_with(pattern)))
        }
        (EndsWith, [Value::Str(text), Value::Str(pattern)]) => {
            Ok(Value::Bool(text.ends_with(pattern)))
        }
        (ScalarAt, [Value::Str(text), Value::Int(index)]) => Ok(option(
            index
                .to_usize()
                .and_then(|index| text.chars().nth(index))
                .map(|scalar| Value::Int(u32::from(scalar).into())),
        )),
        (ByteAt, [Value::Bytes(bytes), Value::Int(index)]) => Ok(option(
            index
                .to_usize()
                .and_then(|index| bytes.get(index))
                .copied()
                .map(|byte| Value::Int(byte.into())),
        )),
        (Scalars, [Value::Str(text)]) => Ok(Value::Array(
            text.chars()
                .map(|scalar| Value::Int(u32::from(scalar).into()))
                .collect(),
        )),
        (ToArray, [Value::Bytes(bytes)]) => Ok(Value::Array(
            bytes.iter().map(|&byte| Value::Int(byte.into())).collect(),
        )),
        (FromScalars, [Value::Array(items)]) => {
            let text = items
                .iter()
                .map(|value| match value {
                    Value::Int(value) => value.to_u32().and_then(char::from_u32),
                    _ => None,
                })
                .collect::<Option<String>>();
            Ok(option(text.map(Value::Str)))
        }
        (FromArray, [Value::Array(items)]) => {
            let bytes = items
                .iter()
                .map(|value| match value {
                    Value::Int(value) => value.to_u8(),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>();
            Ok(option(bytes.map(Value::Bytes)))
        }
        (EncodeUtf8, [Value::Str(text)]) => Ok(Value::Bytes(text.as_bytes().to_vec())),
        (DecodeUtf8, [Value::Bytes(bytes)]) => Ok(option(
            std::str::from_utf8(bytes)
                .ok()
                .map(|text| Value::Str(text.to_owned())),
        )),
        _ => Err(nonstatic(span)),
    }
}

impl Checker<'_> {
    pub(super) fn eval_primitive(
        &mut self,
        env: &Env,
        name: &str,
        mut args: Vec<Value>,
        span: Span,
    ) -> Eval {
        match (name, args.as_slice()) {
            ("assert", [Value::Bool(true), ..]) => Ok(Value::Unit),
            ("assert", [Value::Bool(false), ..]) => {
                Err(Signal::Error(Code::E0830, span, "static assertion failed"))
            }
            ("panic", _) => Err(defect(span, "static evaluation panicked")),
            ("Some" | "Ok" | "Err", []) => Ok(Value::Tag(name.into(), vec![Value::Unit])),
            ("Some" | "Ok" | "Err", [_]) => Ok(Value::Tag(name.into(), args)),
            ("len", [Value::Array(items)]) => Ok(integer(items.len())),
            ("len", [Value::Map(items)]) => Ok(integer(items.len())),
            ("len", [Value::Str(str)]) => Ok(integer(str.chars().count())),
            ("len", [Value::Bytes(bytes)]) => Ok(integer(bytes.len())),
            ("split", [Value::Str(text), Value::Str(separator)]) => Ok(Value::Array(
                text.split(separator.as_str())
                    .map(|part| Value::Str(part.to_owned()))
                    .collect(),
            )),
            (
                "clone",
                [
                    Value::Array(_)
                    | Value::Tuple(_)
                    | Value::Record(_)
                    | Value::Map(_)
                    | Value::Tag(_, _),
                ],
            ) => Ok(args.pop().unwrap_or(Value::Unit)),
            ("clone", [_]) => Err(Signal::Error(
                Code::E0301,
                span,
                "clone requires a clonable shared object",
            )),
            ("inner", [Value::Tag(_, values)]) if values.len() == 1 => {
                values.first().cloned().ok_or_else(|| nonstatic(span))
            }
            ("inner", [Value::Tag(_, values)]) if values.is_empty() => Ok(Value::Unit),
            ("inner", [Value::Tag(_, values)]) => Ok(Value::Tuple(values.clone())),
            ("contains", [Value::Array(values), item]) => {
                Ok(Value::Bool(values.iter().any(|v| ieee_equal(v, item))))
            }
            ("contains", [Value::Map(values), item]) => {
                Ok(Value::Bool(values.iter().any(|(k, _)| ieee_equal(k, item))))
            }
            ("type_name", [Value::Type(ty)]) => Ok(Value::Str(ty.display(self.hir).to_string())),
            ("coords", [Value::Type(ty)]) => self.eval_coords(env, ty, span),
            ("variants", [Value::Type(ty)]) => match self.normalize(ty) {
                Ty::Option(_) => Ok(Value::Array(vec![
                    Value::Str("Some".into()),
                    Value::Str("None".into()),
                ])),
                Ty::Result(..) => Ok(Value::Array(vec![
                    Value::Str("Ok".into()),
                    Value::Str("Err".into()),
                ])),
                Ty::Adt(adt) => {
                    if adt.kind == AdtKind::Foreign {
                        return Err(Signal::Error(
                            Code::E0907,
                            span,
                            "foreign representation is sealed",
                        ));
                    }
                    if adt.kind == AdtKind::OpaqueSum && adt.defining_scope != env.scope {
                        return Err(Signal::Error(
                            Code::E0308,
                            span,
                            "opaque representation is sealed",
                        ));
                    }
                    if !matches!(adt.kind, AdtKind::Sum | AdtKind::OpaqueSum) {
                        return Err(Signal::Error(
                            Code::E0301,
                            span,
                            "variants requires a sum type",
                        ));
                    }
                    let def = self.hir.definition(adt.definition);
                    let extensible = def.stmt.is_some_and(|item| {
                        matches!(
                            &self.ast(def.name.span.file).stmt(item).value.kind,
                            StmtKind::Type(decl)
                                if matches!(&decl.definition, TypeDefinition::Sum(vs)
                                    if vs.iter().any(|v| matches!(v, Variant::Extensible)))
                        )
                    });
                    if extensible && !self.hir.same_package(def.scope, env.scope) {
                        return Err(Signal::Error(
                            Code::E0308,
                            span,
                            "extensible sum variants are sealed outside their defining package",
                        ));
                    }
                    Ok(Value::Array(
                        self.sum_variants(&adt)
                            .into_keys()
                            .map(Value::Str)
                            .collect(),
                    ))
                }
                _ => Err(Signal::Error(
                    Code::E0301,
                    span,
                    "variants requires a sum type",
                )),
            },
            ("has_default", [Value::Type(ty), Value::Str(field)]) => {
                let target = self.normalize(ty);
                if let Ty::Adt(adt) = &target {
                    if adt.kind == AdtKind::Foreign {
                        return Err(Signal::Error(
                            Code::E0907,
                            span,
                            "foreign representation is sealed",
                        ));
                    }
                    if matches!(adt.kind, AdtKind::Opaque | AdtKind::OpaqueSum)
                        && adt.defining_scope != env.scope
                    {
                        return Err(Signal::Error(
                            Code::E0308,
                            span,
                            "opaque representation is sealed",
                        ));
                    }
                }
                let fields_ok = match &target {
                    Ty::Record(fields, _) => fields.contains_key(field),
                    Ty::Adt(adt) => match self.representation(env, adt) {
                        Some(Ty::Record(fields, _)) => fields.contains_key(field),
                        _ => {
                            return Err(Signal::Error(
                                Code::E0358,
                                span,
                                "Reflect::has_default requires a record type",
                            ));
                        }
                    },
                    _ => {
                        return Err(Signal::Error(
                            Code::E0358,
                            span,
                            "Reflect::has_default requires a record type",
                        ));
                    }
                };
                if !fields_ok {
                    return Err(Signal::Error(
                        Code::E0323,
                        span,
                        "invalid field key for Reflect::has_default",
                    ));
                }
                Ok(Value::Bool(
                    self.record_defaults(&Some(target)).contains(field),
                ))
            }
            ("to_f64", [Value::Int(value)]) => Ok(Value::F64(
                value
                    .to_f64()
                    .unwrap_or_else(|| {
                        if value.is_negative() {
                            f64::NEG_INFINITY
                        } else {
                            f64::INFINITY
                        }
                    })
                    .to_bits(),
            )),
            ("convert" | "trunc", [Value::F64(value)]) => {
                let value = f64::from_bits(*value);
                let integer = if name == "trunc" || value.fract() == 0.0 {
                    BigInt::from_f64(value.trunc())
                } else {
                    None
                };
                Ok(integer.map_or_else(
                    || Value::Tag("None".into(), Vec::new()),
                    |value| Value::Tag("Some".into(), vec![Value::Int(value)]),
                ))
            }
            _ => Err(nonstatic(span)),
        }
    }

    pub(super) fn eval_metadata(
        &mut self,
        env: &mut Env,
        path: &syntax::Path,
        args: &[Value],
        span: Span,
    ) -> Eval {
        let Some(member) = path.segments.last() else {
            return Err(nonstatic(span));
        };
        let Some(Value::Type(target)) = args.first() else {
            return Err(Signal::Error(
                Code::E0306,
                span,
                "metadata query requires a type value",
            ));
        };
        let attribute = if let Some(argument) = member.arguments.get(1) {
            self.type_argument(env, argument)
        } else if let Some(Ty::Array(member)) = self.types.get(&span) {
            self.normalize(&member.ty)
        } else {
            return Err(Signal::Error(
                Code::E0344,
                span,
                "metadata query requires an attribute type",
            ));
        };
        let key = match (member.name.value.as_str(), args.get(1)) {
            ("attrs", None) => None,
            ("field_attrs" | "variant_attrs", Some(Value::Str(key))) => Some(key.as_str()),
            _ => return Err(nonstatic(span)),
        };
        let Some((local, expressions)) =
            self.metadata_source(env, target, &member.name.value, key, span)?
        else {
            return Ok(Value::Array(Vec::new()));
        };
        let values = expressions
            .into_iter()
            .filter_map(|expression| self.metadata(&local, expression))
            .filter_map(|(ty, value)| (ty == attribute).then_some(value))
            .collect();
        Ok(Value::Array(values))
    }

    fn metadata_source(
        &mut self,
        env: &Env,
        target: &Ty,
        operation: &str,
        key: Option<&str>,
        span: Span,
    ) -> Eval<Option<(Env, Vec<ExprId>)>> {
        let Ty::Adt(adt) = target else {
            return match (operation, target, key) {
                ("attrs", _, _) => Ok(None),
                ("field_attrs", Ty::Record(fields, _), Some(key)) if fields.contains_key(key) => {
                    Ok(None)
                }
                _ => Err(Signal::Error(
                    Code::E0323,
                    span,
                    "invalid metadata coordinate",
                )),
            };
        };
        let def = self.hir.definition(adt.definition);
        let Some(stmt) = def.stmt else {
            return Ok(None);
        };
        let local = self.instantiate_adt(adt);
        let node = self.ast(local.file).stmt(stmt);
        let Some(key) = key else {
            return Ok(Some((local, node.value.attrs.clone())));
        };
        if adt.kind == AdtKind::Foreign {
            return Err(Signal::Error(
                Code::E0907,
                span,
                "foreign representation is sealed",
            ));
        }
        if matches!(adt.kind, AdtKind::Opaque | AdtKind::OpaqueSum)
            && adt.defining_scope != env.scope
        {
            return Err(Signal::Error(
                Code::E0308,
                span,
                "opaque representation is sealed",
            ));
        }
        if let StmtKind::Type(declaration) = &node.value.kind {
            match (&declaration.definition, operation) {
                (TypeDefinition::Data(rep), "field_attrs") => {
                    if let Type::Record { fields, .. } = &self.ast(local.file).ty(*rep).value
                        && let Some(field) = fields.iter().find(|field| field.name.value == key)
                    {
                        return Ok(Some((local, field.attrs.clone())));
                    }
                }
                (TypeDefinition::Sum(_), "variant_attrs") => {
                    if let Some(source) = self.variant_metadata(adt, key, &mut Default::default()) {
                        return Ok(Some(source));
                    }
                }
                _ => {}
            }
        }
        Err(Signal::Error(
            Code::E0323,
            span,
            "invalid metadata coordinate",
        ))
    }

    fn variant_metadata(
        &mut self,
        adt: &Adt,
        tag: &str,
        visited: &mut std::collections::HashSet<DefinitionId>,
    ) -> Option<(Env, Vec<ExprId>)> {
        if !visited.insert(adt.definition) {
            return None;
        }
        let mut local = self.instantiate_adt(adt);
        let definition = self.hir.definition(adt.definition);
        let StmtKind::Type(declaration) = &self.ast(local.file).stmt(definition.stmt?).value.kind
        else {
            return None;
        };
        let TypeDefinition::Sum(variants) = &declaration.definition else {
            return None;
        };
        for variant in variants {
            match variant {
                Variant::Constructor { name, attrs, .. } if name.value == tag => {
                    return Some((local, attrs.clone()));
                }
                Variant::Spread(ty) => {
                    if let Ty::Adt(subset) = self.type_expr(&mut local, *ty)
                        && let Some(found) = self.variant_metadata(&subset, tag, visited)
                    {
                        return Some(found);
                    }
                }
                _ => {}
            }
        }
        None
    }

    fn eval_coords(&mut self, env: &Env, ty: &Ty, span: Span) -> Eval {
        let rep;
        let ty = if let Ty::Adt(adt) = ty {
            if adt.kind == AdtKind::Foreign {
                return Err(Signal::Error(
                    Code::E0907,
                    span,
                    "foreign representation is sealed",
                ));
            }
            if matches!(adt.kind, AdtKind::Opaque | AdtKind::OpaqueSum)
                && adt.defining_scope != env.scope
            {
                return Err(Signal::Error(
                    Code::E0308,
                    span,
                    "opaque representation is sealed",
                ));
            }
            rep = self.representation(env, adt);
            rep.as_ref().unwrap_or(ty)
        } else {
            ty
        };
        let entries = match ty {
            Ty::Record(fields, _) => fields
                .iter()
                .map(|(key, member)| {
                    Value::Tuple(vec![Value::Mode(member.mode), Value::Str(key.clone())])
                })
                .collect(),
            Ty::Tuple(items) => items
                .iter()
                .enumerate()
                .map(|(position, member)| {
                    Value::Tuple(vec![Value::Mode(member.mode), integer(position)])
                })
                .collect(),
            Ty::Unit => Vec::new(),
            _ => {
                return Err(Signal::Error(
                    Code::E0358,
                    span,
                    "coords requires a record or tuple",
                ));
            }
        };
        Ok(Value::Array(entries))
    }
}
