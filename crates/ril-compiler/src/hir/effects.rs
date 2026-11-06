//! Lexical effect members and the alias graph used for instance checking.
use super::{DefId, Definition, DefinitionKind, Entry, Index, ScopeId, UseKind, expression_path};
use crate::{
    ast::{Expr, ExprKind, TypeExpr, TypeKind},
    source::Span,
};
use std::collections::{BTreeMap, BTreeSet};

/// An edge of an effect set. Different edges can instantiate the same
/// declaration with different static arguments.
#[derive(Debug)]
pub struct EffectAliasMember {
    pub effect: DefId,
    pub arguments: Vec<TypeExpr>,
    pub scope: ScopeId,
    pub span: Option<Span>,
}

#[derive(Debug)]
pub enum EffectMember {
    Operation {
        family: DefId,
    },
    /// A source namespace exposes an operation name through an effect set.
    /// The declaration candidates describe its surface. Instance selection
    /// follows the alias graph with substituted static arguments.
    Projection {
        alias: DefId,
        operations: Vec<DefId>,
    },
}

impl EffectMember {
    fn family(&self) -> DefId {
        match self {
            Self::Operation { family } => *family,
            Self::Projection { alias, .. } => *alias,
        }
    }
}

#[derive(Debug)]
pub struct EffectInstanceUse {
    pub family: DefId,
    /// Direct operation or projection declaration.
    pub operation: DefId,
    pub arguments: Option<Vec<TypeExpr>>,
    pub handler: Option<HandlerTarget>,
}

#[derive(Debug, Clone, Copy)]
pub struct HandlerTarget {
    pub group: Span,
    pub arm: ScopeId,
}

#[derive(Debug)]
pub(super) struct EffectAliasSite {
    alias: DefId,
    scope: ScopeId,
    path: Vec<String>,
    arguments: Vec<TypeExpr>,
    span: Span,
}

impl Index {
    pub(super) fn install_async_alias(&mut self, prelude: ScopeId) {
        let members = ["Fiber", "Concurrent"]
            .into_iter()
            .map(|name| EffectAliasMember {
                effect: self.hir.scopes[prelude.0].bindings[name].definition,
                arguments: vec![],
                scope: prelude,
                span: None,
            })
            .collect();
        let alias = self.builtin(prelude, "Async", DefinitionKind::EffectAlias, 0);
        let namespace = self.scope(None, None, None);
        self.hir.definitions[alias.0].members = Some(namespace);
        self.hir.effect_aliases.insert(alias, members);
    }

    pub(super) fn is_effect(&self, definition: DefId) -> bool {
        matches!(
            self.hir.definitions[definition.0].kind,
            DefinitionKind::Effect | DefinitionKind::EffectAlias
        )
    }

    pub(super) fn effect_name(&mut self, scope: ScopeId, syntax: &TypeExpr) {
        if let TypeKind::Name { path, arguments } = &syntax.kind {
            self.site(
                scope,
                syntax.span,
                path.clone(),
                UseKind::EffectName {
                    applied: !arguments.is_empty(),
                },
            );
            for argument in arguments {
                self.ty(scope, argument);
            }
        }
    }

    pub(super) fn index_effect_alias(
        &mut self,
        alias: DefId,
        scope: ScopeId,
        members: &[TypeExpr],
    ) {
        self.hir.effect_aliases.insert(alias, vec![]);
        for member in members {
            self.effect_name(scope, member);
            if let TypeKind::Name { path, arguments } = &member.kind {
                self.pending_effect_members.push(EffectAliasSite {
                    alias,
                    scope,
                    path: path.clone(),
                    arguments: arguments.clone(),
                    span: member.span,
                });
            }
        }
    }

    /// Imports and effect alias surfaces can become available to each other.
    /// Each pass links new edges and publishes newly reachable operation names.
    pub(super) fn link_effect_aliases(&mut self) -> bool {
        let mut changed = false;
        for site in std::mem::take(&mut self.pending_effect_members) {
            if let Ok(effect) = self.resolve(site.scope, &site.path, site.span.start, false)
                && self.is_effect(effect)
            {
                self.hir
                    .effect_aliases
                    .get_mut(&site.alias)
                    .expect("indexed alias")
                    .push(EffectAliasMember {
                        effect,
                        arguments: site.arguments,
                        scope: site.scope,
                        span: Some(site.span),
                    });
                changed = true;
            } else {
                self.pending_effect_members.push(site);
            }
        }
        if changed {
            for members in self.hir.effect_aliases.values_mut() {
                members.sort_by_key(|member| member.span.map(|span| span.start));
            }
        }

        let aliases: Vec<_> = self.hir.effect_aliases.keys().copied().collect();
        for alias in aliases {
            let surface = self.effect_surface(alias);
            let namespace = self.member_scope(alias).expect("alias namespace");
            for (name, operations) in surface {
                let definition =
                    if let Some(entry) = self.hir.scopes[namespace.0].bindings.get(&name) {
                        entry.definition
                    } else {
                        let definition = self.allocate(Definition {
                            name: name.clone(),
                            kind: DefinitionKind::EffectProjection,
                            scope: namespace,
                            span: None,
                            public: true,
                            constructor_form: None,
                            mutable: false,
                            signature: Some(vec![]),
                            members: None,
                            alias: None,
                        });
                        self.hir.scopes[namespace.0].bindings.insert(
                            name,
                            Entry {
                                definition,
                                visible_at: 0,
                                public: true,
                            },
                        );
                        changed = true;
                        definition
                    };
                self.hir.effect_members.insert(
                    definition,
                    EffectMember::Projection {
                        alias,
                        operations: operations.into_iter().collect(),
                    },
                );
            }
        }
        changed
    }

    fn effect_surface(&self, root: DefId) -> BTreeMap<String, BTreeSet<DefId>> {
        let mut surface = BTreeMap::<String, BTreeSet<DefId>>::new();
        let mut pending = vec![root];
        let mut visited = BTreeSet::new();
        while let Some(effect) = pending.pop() {
            if !visited.insert(effect) {
                continue;
            }
            if let Some(members) = self.hir.effect_aliases.get(&effect) {
                pending.extend(members.iter().map(|member| member.effect));
            } else if let Ok(namespace) = self.member_scope(effect) {
                for (name, entry) in &self.hir.scopes[namespace.0].bindings {
                    if self.hir.definitions[entry.definition.0].kind
                        == DefinitionKind::EffectOperation
                    {
                        surface
                            .entry(name.clone())
                            .or_default()
                            .insert(entry.definition);
                    }
                }
            }
        }
        surface
    }

    pub(super) fn handler_operation(
        &mut self,
        scope: ScopeId,
        expr: &Expr,
        handler: HandlerTarget,
    ) {
        match &expr.kind {
            ExprKind::EffectOperation { effect, name } => {
                self.qualified_effect_operation(scope, expr.span, effect, name, Some(handler));
            }
            ExprKind::Generic { base, arguments } => {
                if let Some(path) = expression_path(base) {
                    self.site(
                        scope,
                        expr.span,
                        path,
                        UseKind::Operation {
                            arguments: None,
                            handler: Some(handler),
                            applied: true,
                        },
                    );
                    for argument in arguments {
                        self.ty(scope, argument);
                    }
                }
            }
            _ => {
                if let Some(path) = expression_path(expr) {
                    self.site(
                        scope,
                        expr.span,
                        path,
                        UseKind::Operation {
                            arguments: None,
                            handler: Some(handler),
                            applied: false,
                        },
                    );
                }
            }
        }
    }

    pub(super) fn qualified_effect_operation(
        &mut self,
        scope: ScopeId,
        span: Span,
        effect: &Expr,
        name: &str,
        handler: Option<HandlerTarget>,
    ) {
        self.expr(scope, effect);
        if let ExprKind::Generic { base, arguments } = &effect.kind
            && let Some(mut path) = expression_path(base)
        {
            path.push(name.to_owned());
            self.site(
                scope,
                span,
                path,
                UseKind::Operation {
                    arguments: Some(arguments.clone()),
                    handler,
                    applied: false,
                },
            );
        }
    }

    pub(super) fn resolve_effect_use(
        &mut self,
        definition: DefId,
        span: Span,
        use_kind: UseKind,
    ) -> Option<EffectInstanceUse> {
        let (arguments, handler) = match use_kind {
            UseKind::Operation {
                arguments, handler, ..
            } => (arguments, handler),
            UseKind::Ordinary | UseKind::Application => (None, None),
            _ => return None,
        };
        let operation = if self.hir.effect_members.contains_key(&definition) {
            Some(definition)
        } else if self.hir.definitions[definition.0].alias.is_some() {
            self.signature_of(definition)
                .map(|signature| signature.item)
        } else {
            None
        };
        let selection = operation.and_then(|operation| {
            self.hir
                .effect_members
                .get(&operation)
                .map(|member| (operation, member.family()))
        });
        match selection {
            Some((operation, family)) => Some(EffectInstanceUse {
                family,
                operation,
                arguments,
                handler,
            }),
            None => {
                if handler.is_some() || arguments.is_some() {
                    self.error(
                        span,
                        "E0621",
                        "the selected declaration is not an effect operation",
                    );
                }
                None
            }
        }
    }

    pub(super) fn monomorphic_operation(&self, operation: DefId) -> Option<DefId> {
        let member = self.hir.effect_members.get(&operation)?;
        if !self.has_no_generic_parameters(member.family()) {
            return None;
        }
        match member {
            EffectMember::Operation { .. } => Some(operation),
            EffectMember::Projection { operations, .. } => {
                let [candidate] = operations.as_slice() else {
                    return None;
                };
                let EffectMember::Operation { family } = self.hir.effect_members.get(candidate)?
                else {
                    return None;
                };
                self.has_no_generic_parameters(*family)
                    .then_some(*candidate)
            }
        }
    }

    fn has_no_generic_parameters(&self, definition: DefId) -> bool {
        self.hir.definitions[definition.0]
            .signature
            .as_ref()
            .is_some_and(Vec::is_empty)
    }
}
