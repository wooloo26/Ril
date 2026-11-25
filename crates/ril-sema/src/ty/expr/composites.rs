use std::collections::{BTreeMap, HashSet};

use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::{self, Expr, ExprId, Mode, StmtKind, TypeDefinition, ValueField};

use crate::ty::{
    AdtKind, Member, MemberMode, Ty,
    check::{Checker, Env},
};

impl Checker<'_> {
    pub(super) fn navigation(&mut self, env: &mut Env, base: ExprId, steps: &[ExprId]) -> Ty {
        let mut ty = self.expr(env, base, None);
        for &step in steps {
            let node = self.ast(env.file).expr(step);
            ty = self.normalize(&ty);
            ty = match &node.value {
                Expr::Member { member, safe, .. } => {
                    if *safe {
                        ty = match ty {
                            Ty::Option(inner) => *inner,
                            Ty::Unknown | Ty::Never => Ty::Unknown,
                            _ => {
                                self.error(
                                    Code::E0715,
                                    node.span,
                                    "safe member access requires an option",
                                );
                                Ty::Unknown
                            }
                        };
                    }
                    self.project(env, member, &ty, node.span, false)
                }
                Expr::Index { index, safe, .. } => {
                    if *safe && let Ty::Option(inner) = ty {
                        ty = *inner;
                    }
                    self.index(env, ty, *index, *safe, node.span)
                }
                _ => ril_source::ice!("unexpected navigation step"),
            };
            self.types.insert(node.span, ty.clone());
            self.navigation_values.insert(node.span, ty.clone());
        }
        let ty = self.normalize(&ty);
        if matches!(ty, Ty::Option(_) | Ty::Unknown) {
            ty
        } else {
            Ty::Option(Box::new(ty))
        }
    }

    pub(super) fn index(
        &mut self,
        env: &mut Env,
        base: Ty,
        index: ExprId,
        safe: bool,
        span: Span,
    ) -> Ty {
        let mut base = self.normalize(&base);
        if let Ty::Draft(inner) = base {
            base = *inner;
        }
        if matches!(base, Ty::Map(..)) && !safe && env.map_store != Some(span) {
            self.error(
                Code::E0352,
                span,
                "map reads require the safe index operator",
            );
        }
        let (key, value) = match &base {
            Ty::Array(item) => (Ty::Int, item.ty.clone()),
            Ty::Map(key, value) => ((**key).clone(), value.ty.clone()),
            Ty::Str => (Ty::Int, Ty::Str),
            Ty::Bytes => (Ty::Int, Ty::Int),
            Ty::Unknown => (Ty::Unknown, Ty::Unknown),
            _ => {
                self.error(
                    Code::E0352,
                    span,
                    "index target must be an array, map, str, or bytes",
                );
                (Ty::Unknown, Ty::Unknown)
            }
        };
        let index_ty = self.expr(env, index, Some(&key));
        if index_ty == Ty::Range && matches!(base, Ty::Array(_) | Ty::Str | Ty::Bytes) {
            base
        } else {
            self.require(env, self.ast(env.file).expr(index).span, &index_ty, &key);
            value
        }
    }

    pub(super) fn record(
        &mut self,
        env: &mut Env,
        name: Option<&syntax::Path>,
        fields: &[ValueField],
        expected: Option<&Ty>,
        span: Span,
    ) -> Ty {
        let data = name
            .map(|path| self.constructor_type(env, path, expected))
            .or_else(|| expected.cloned());
        let mut raw = data.clone();
        if let Some(Ty::Adt(adt)) = &data {
            if adt.kind == AdtKind::Foreign {
                self.error(Code::E0907, span, "cannot construct a foreign handle");
                return Ty::Unknown;
            }
            if adt.kind == AdtKind::Opaque && adt.defining_scope != env.scope {
                self.error(Code::E0308, span, "opaque type construction is sealed");
                return Ty::Unknown;
            }
            raw = self.representation(env, adt);
        }
        if let Some(Ty::Record(mut required, open)) = raw {
            let mut provided = BTreeMap::new();
            for field in fields {
                let found = required.get_mut(&field.name.value);
                if found.is_none() && !open {
                    self.error(Code::E0302, field.name.span, "unexpected record field");
                }
                let ty = self.field_expr(env, field, found.as_ref().map(|m| &m.ty));
                if let Some(found) = found {
                    let fits = self.require(env, field.name.span, &ty, &found.ty);
                    if fits && name.is_none() && found.ty.has_via_members() && ty != Ty::Never {
                        found.ty = ty;
                    }
                    let written = self.member_mode(env, &field.storage);
                    if name.is_none() && found.mode.mode == Mode::Via {
                        if written.variable != found.mode.variable {
                            self.error(
                                Code::E0357,
                                field.name.span,
                                "incompatible field slot replaceability",
                            );
                        }
                        found.mode = written;
                    } else if written != MemberMode::PLAIN && written != found.mode {
                        self.error(Code::E0357, field.name.span, "incompatible field mode");
                    }
                }
                provided.insert(field.name.value.as_str(), ());
            }
            let defaults = self.record_defaults(&data);
            for field in required.keys() {
                if !provided.contains_key(field.as_str()) && !defaults.contains(field) && !open {
                    self.error(Code::E0307, span, format!("missing record field {field}"));
                }
            }
            match data {
                Some(Ty::Record(..)) => Ty::Record(required, open),
                _ => data.unwrap_or(Ty::Unknown),
            }
        } else if name.is_some() && !matches!(data, Some(Ty::Unknown)) {
            self.error(
                Code::E0301,
                span,
                "named record construction requires a record representation",
            );
            Ty::Unknown
        } else {
            let fields = fields
                .iter()
                .map(|field| {
                    (
                        field.name.value.clone(),
                        Member {
                            mode: self.member_mode(env, &field.storage),
                            ty: self.field_expr(env, field, None),
                        },
                    )
                })
                .collect();
            Ty::Record(fields, false)
        }
    }

    pub(in crate::ty) fn record_defaults(&self, ty: &Option<Ty>) -> HashSet<String> {
        let Some(Ty::Adt(adt)) = ty else {
            return HashSet::new();
        };
        let def = self.hir.definition(adt.definition);
        let Some(stmt) = def.stmt else {
            return HashSet::new();
        };
        let ast = self.ast(def.name.span.file);
        let StmtKind::Type(decl) = &ast.stmt(stmt).value.kind else {
            return HashSet::new();
        };
        let TypeDefinition::Data(ty) = decl.definition else {
            return HashSet::new();
        };
        if let syntax::Type::Record { fields, .. } = &ast.ty(ty).value {
            fields
                .iter()
                .filter(|field| field.default.is_some())
                .map(|field| field.name.value.clone())
                .collect()
        } else {
            HashSet::new()
        }
    }

    fn field_expr(&mut self, env: &mut Env, field: &ValueField, expected: Option<&Ty>) -> Ty {
        if let Some(expr) = field.value {
            self.expr(env, expr, expected)
        } else if let Some(id) = self.resolve(field.name.span) {
            self.def_type(env, id, field.name.span, false)
        } else {
            Ty::Unknown
        }
    }

    pub(super) fn inferred_element(&mut self, env: &Env, element: Option<ExprId>) -> Member {
        Member {
            mode: self.literal_element_mode(env, element),
            ty: self.fresh(),
        }
    }

    pub(super) fn literal_element(
        &self,
        env: &Env,
        element: Option<ExprId>,
        expected: &Member,
    ) -> Member {
        let mut member = expected.clone();
        if member.mode.mode == Mode::Via {
            member.mode = self.literal_element_mode(env, element);
        }
        member
    }

    pub(super) fn receive_literal_element(
        &mut self,
        env: &mut Env,
        element: ExprId,
        member: &mut Member,
    ) {
        let actual = self.expect(env, element, &member.ty);
        if member.ty.has_via_members() && actual != Ty::Never {
            member.ty = actual;
        }
    }

    fn literal_element_mode(&self, env: &Env, element: Option<ExprId>) -> MemberMode {
        let mode = match element.map(|id| &self.ast(env.file).expr(id).value) {
            Some(Expr::Unary { op, .. }) if op.value == "ref" => Mode::Ref,
            Some(Expr::Unary { op, .. }) if op.value == "^mut" => Mode::Shared,
            _ => Mode::Plain,
        };
        MemberMode {
            variable: false,
            mode,
        }
    }
}
