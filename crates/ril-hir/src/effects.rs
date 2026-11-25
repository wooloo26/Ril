use std::collections::{BTreeMap, BTreeSet};

use ril_source::{
    diag::{Code, Diagnostic},
    span::Span,
};

use ril_syntax::syntax::{Name, Path, StmtKind, Type, Visibility};

use super::{DefinitionId, DefinitionKind, Entry, Program, Resolution, ScopeId, Target};

pub(super) struct PendingOperation {
    caller: ScopeId,
    effect_scope: ScopeId,
    name: Name,
    path: Span,
}

impl Program {
    pub(super) fn defer_operation(
        &mut self,
        current: Target,
        caller: ScopeId,
        name: &Name,
        path: &Path,
        diagnostic: &Diagnostic,
    ) -> bool {
        let Target::Def(id) = current else {
            return false;
        };
        let DefinitionKind::Effect(effect_scope) = self.definition(id).kind else {
            return false;
        };
        if diagnostic.code != Some(Code::E0209)
            || path
                .segments
                .last()
                .is_none_or(|segment| segment.name.span != name.span)
        {
            return false;
        }
        self.pending_operations.push(PendingOperation {
            caller,
            effect_scope,
            name: name.clone(),
            path: path.span,
        });
        true
    }

    pub(super) fn resolve_effect_spreads(&mut self, errors: &mut Vec<Diagnostic>) {
        let mut edges = BTreeMap::new();
        for (id, def) in self.definitions() {
            if !matches!(def.kind, DefinitionKind::Effect(_)) {
                continue;
            }
            let file = self.file(def.name.span.file);
            if let Some(stmt) = def.stmt
                && let StmtKind::Effect { spreads, .. } = &file.ast.stmt(stmt).value.kind
            {
                let mut inclusions = Vec::new();
                for &spread in spreads {
                    let node = file.ast.ty(spread);
                    let span = node.span;
                    match self.resolve(span) {
                        Some(Resolution::Definition(target))
                            if matches!(
                                self.definition(target).kind,
                                DefinitionKind::Effect(_)
                            ) =>
                        {
                            inclusions.push((target, span));
                        }
                        None if matches!(node.value, Type::Named(_)) => {}
                        _ => {
                            errors.push(Diagnostic::error(
                                Code::E0620,
                                span,
                                "spread target must be an effect",
                            ));
                        }
                    }
                }
                edges.insert(id, inclusions);
            }
        }
        let mut active = BTreeSet::new();
        for &effect in edges.keys() {
            self.expand_effect(effect, &edges, &mut active, errors);
        }
        for pending in std::mem::take(&mut self.pending_operations) {
            match self.lookup(
                pending.caller,
                pending.effect_scope,
                &pending.name,
                Code::E0209,
            ) {
                Ok(target) => {
                    self.resolutions.insert(pending.name.span, target.into());
                    self.resolutions.insert(pending.path, target.into());
                }
                Err(error) => errors.push(error),
            }
        }
    }

    fn expand_effect(
        &mut self,
        effect: DefinitionId,
        edges: &BTreeMap<DefinitionId, Vec<(DefinitionId, Span)>>,
        active: &mut BTreeSet<DefinitionId>,
        errors: &mut Vec<Diagnostic>,
    ) {
        if self.effect_spreads.contains_key(&effect) {
            return;
        }
        let DefinitionKind::Effect(scope) = self.definition(effect).kind else {
            return;
        };
        active.insert(effect);
        let mut included = BTreeSet::new();
        for &(other, span) in edges.get(&effect).into_iter().flatten() {
            if active.contains(&other) {
                errors.push(Diagnostic::error(Code::E0313, span, "cyclic effect spread"));
                continue;
            }
            self.expand_effect(other, edges, active, errors);
            included.insert(other);
            if let Some(indirect) = self.effect_spreads.get(&other) {
                included.extend(indirect);
            }
            let operations = self.effect_operations(other).collect::<Vec<_>>();
            for operation in operations {
                let name = self.definition(operation).name.value.clone();
                let names = &mut self.scope_mut(scope).names;
                if let Some(existing) = names.get(&name) {
                    if !matches!(existing.target, Target::Def(id) if id == operation) {
                        errors.push(Diagnostic::error(
                            Code::E0622,
                            span,
                            format!("conflicting effect operation {name}"),
                        ));
                    }
                } else {
                    names.insert(
                        name,
                        Entry {
                            target: Target::Def(operation),
                            visibility: Visibility::Public,
                        },
                    );
                }
            }
        }
        active.remove(&effect);
        self.effect_spreads.insert(effect, included);
    }
}
