use std::collections::{BTreeMap, HashSet};

use ril_base::{diag::Code, span::Span};
use ril_frontend::{
    hir::{BuiltinPayload, BuiltinSum, DefinitionId},
    syntax::{self, StmtKind, TypeDefinition},
};

use crate::ty::{
    Adt, AdtKind, GenericValue, Ty,
    check::{Checker, Env},
};

impl<'a> Checker<'a> {
    pub(in crate::ty) fn sum_subset(&mut self, env: &Env, actual: &Ty, target: &Ty) -> bool {
        let (Ty::Adt(actual), Ty::Adt(target)) = (self.normalize(actual), self.normalize(target))
        else {
            return false;
        };
        self.sum_includes(env, &actual, &target, &mut HashSet::new())
    }

    fn sum_includes(
        &mut self,
        env: &Env,
        actual: &Adt,
        target: &Adt,
        active: &mut HashSet<DefinitionId>,
    ) -> bool {
        if !matches!(target.kind, AdtKind::Sum | AdtKind::OpaqueSum) {
            return false;
        }
        if actual.definition == target.definition {
            return actual.arguments == target.arguments;
        }
        if self.hir.builtin_sum(actual.definition) == Some(BuiltinSum::PanicError)
            && self.hir.builtin_sum(target.definition) == Some(BuiltinSum::TaskFault)
        {
            return true;
        }
        if (target.kind == AdtKind::OpaqueSum && env.scope != target.defining_scope)
            || !active.insert(target.definition)
        {
            return false;
        }
        let mut local = self.instantiate_adt(target);
        let includes = self.sum_declaration(target).is_some_and(|variants| {
            variants.iter().any(|variant| {
                let syntax::Variant::Spread(ty) = variant else {
                    return false;
                };
                let Ty::Adt(subset) = self.type_expr(&mut local, *ty) else {
                    return false;
                };
                self.sum_includes(&local, actual, &subset, active)
            })
        });
        active.remove(&target.definition);
        includes
    }

    fn sum_declaration(&self, adt: &Adt) -> Option<&'a [syntax::Variant]> {
        let definition = self.hir.definition(adt.definition);
        let stmt = definition.stmt?;
        let StmtKind::Type(decl) = &self.ast(definition.name.span.file).stmt(stmt).value.kind
        else {
            return None;
        };
        match &decl.definition {
            TypeDefinition::Sum(variants) => Some(variants),
            _ => None,
        }
    }

    pub(in crate::ty) fn sum_variants(&mut self, adt: &Adt) -> BTreeMap<String, Vec<Ty>> {
        let span = self.hir.definition(adt.definition).name.span;
        self.sum_variant_shapes(adt, &mut HashSet::new(), span)
            .into_iter()
            .map(|(name, payload)| (name, payload.unwrap_or_default()))
            .collect()
    }

    fn sum_variant_shapes(
        &mut self,
        adt: &Adt,
        active: &mut HashSet<DefinitionId>,
        at: Span,
    ) -> BTreeMap<String, Option<Vec<Ty>>> {
        if let Some(kind) = self.hir.builtin_sum(adt.definition) {
            return kind
                .variants()
                .iter()
                .map(|&(tag, payload)| {
                    let shape = match payload {
                        BuiltinPayload::UnitTag => None,
                        BuiltinPayload::PanicInfo => Some(vec![Ty::PanicInfo]),
                        BuiltinPayload::Element => Some(vec![match adt.arguments.first() {
                            Some(GenericValue::Type(element)) => element.clone(),
                            _ => Ty::Unknown,
                        }]),
                    };
                    (tag.into(), shape)
                })
                .collect();
        }
        if !active.insert(adt.definition) {
            self.error(Code::E0313, at, "cyclic sum spread");
            return BTreeMap::new();
        }
        let mut local = self.instantiate_adt(adt);
        let variants = self.sum_declaration(adt).unwrap_or_default();
        let mut all = BTreeMap::new();
        for variant in variants {
            match variant {
                syntax::Variant::Constructor {
                    name,
                    payload,
                    attrs,
                } => {
                    for &attribute in attrs {
                        self.metadata(&local, attribute);
                    }
                    let payload = payload.as_ref().map(|items| {
                        items
                            .iter()
                            .map(|&ty| self.type_expr(&mut local, ty))
                            .collect()
                    });
                    self.merge_sum_variant(&mut all, name.value.clone(), payload, name.span);
                }
                syntax::Variant::Spread(ty) => {
                    let span = self.ast(local.file).ty(*ty).span;
                    match self.type_expr(&mut local, *ty) {
                        Ty::Adt(subset) if subset.kind == AdtKind::Sum => {
                            if self.sum_declaration(&subset).is_some_and(|variants| {
                                variants
                                    .iter()
                                    .any(|variant| matches!(variant, syntax::Variant::Extensible))
                            }) {
                                self.error(Code::E0308, span, "an extensible sum cannot be spread");
                                continue;
                            }
                            for (name, payload) in self.sum_variant_shapes(&subset, active, span) {
                                self.merge_sum_variant(&mut all, name, payload, span);
                            }
                        }
                        Ty::Adt(subset) if subset.kind == AdtKind::OpaqueSum => {
                            self.error(Code::E0308, span, "an opaque sum cannot be spread");
                        }
                        Ty::Unknown | Ty::Param(_) => {}
                        _ => self.error(Code::E0306, span, "spread target must be a sum type"),
                    }
                }
                syntax::Variant::Extensible => {}
            }
        }
        active.remove(&adt.definition);
        all
    }

    fn merge_sum_variant(
        &mut self,
        variants: &mut BTreeMap<String, Option<Vec<Ty>>>,
        name: String,
        payload: Option<Vec<Ty>>,
        span: Span,
    ) {
        match variants.entry(name) {
            std::collections::btree_map::Entry::Occupied(previous)
                if previous.get() != &payload =>
            {
                self.error(
                    Code::E0213,
                    span,
                    format!("conflicting payload for {}", previous.key()),
                );
            }
            std::collections::btree_map::Entry::Vacant(slot) => {
                slot.insert(payload);
            }
            _ => {}
        }
    }
}
