use std::collections::{BTreeMap, BTreeSet, HashMap};

use ril_hir::{DefinitionId, DefinitionKind, Program};
use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::{GenericArg, Path, StmtKind, Type};

use super::{
    GenericValue, Ty, Value,
    check::{Checker, Env, path_name, substitute},
    mode_name, render,
};

#[derive(Clone)]
pub(crate) struct Instance {
    pub(crate) definition: DefinitionId,
    pub(crate) includes: BTreeSet<String>,
    arguments: Vec<GenericValue>,
    bindings: HashMap<DefinitionId, GenericValue>,
}

impl Instance {
    pub(crate) fn native_label(&self, hir: &Program, types: &BTreeMap<DefinitionId, Ty>) -> String {
        if types.is_empty() {
            return label(hir, self.definition, &self.arguments);
        }
        let bindings = types
            .iter()
            .map(|(&id, ty)| (id, GenericValue::Type(ty.clone())))
            .collect();
        let arguments = self
            .arguments
            .iter()
            .map(|arg| match arg {
                GenericValue::Type(ty) => GenericValue::Type(substitute(ty, &bindings)),
                GenericValue::Data(Value::Type(ty)) => {
                    GenericValue::Data(Value::Type(Box::new(substitute(ty, &bindings))))
                }
                value => value.clone(),
            })
            .collect::<Vec<_>>();
        label(hir, self.definition, &arguments)
    }
}

fn label(hir: &Program, definition: DefinitionId, arguments: &[GenericValue]) -> String {
    let identity = hir.effect_label(definition);
    if arguments.is_empty() {
        return identity;
    }
    let args = arguments
        .iter()
        .map(|argument| match argument {
            GenericValue::Type(ty) => ty.qualified_display(hir).to_string(),
            GenericValue::Mode(mode) => mode_name(*mode).into(),
            GenericValue::Data(Value::Type(ty)) => format!("<{}>", ty.qualified_display(hir)),
            GenericValue::Data(data) => render(data),
            GenericValue::Effects(row) => {
                let mut parts: Vec<String> = row.concrete.iter().map(|e| format!("@{e}")).collect();
                for &v in &row.vars {
                    parts.push(format!("@{}", hir.definition(v).name.value));
                }
                if row.direct_open {
                    parts.push("@fn".into());
                }
                if row.open {
                    parts.push("@".into());
                }
                if parts.is_empty() {
                    "@()".into()
                } else {
                    parts.join(" ")
                }
            }
        })
        .collect::<Vec<_>>();
    format!("{identity}<{}>", args.join(", "))
}

impl Checker<'_> {
    pub(super) fn effect_label(&mut self, env: &mut Env, path: &Path) -> String {
        if let Some(effect) = self.resolve(path.span)
            && matches!(self.hir.definition(effect).kind, DefinitionKind::Effect(_))
        {
            let args = path
                .segments
                .last()
                .map_or(&[][..], |part| part.arguments.as_slice());
            self.effect_arguments(env, effect, args, path.span)
        } else {
            path_name(path)
        }
    }

    pub(super) fn effect_covers(&self, covering: &str, actual: &str) -> bool {
        covering == actual
            || self.effect_instances.get(covering).map_or_else(
                || self.hir.effect_covers(covering, actual),
                |instance| instance.includes.contains(actual),
            )
    }

    pub(super) fn operation_instance(
        &mut self,
        env: &mut Env,
        operation: DefinitionId,
        path: &Path,
    ) -> HashMap<DefinitionId, GenericValue> {
        let Some(owner) = self.hir.operation_effect(operation) else {
            return HashMap::new();
        };
        let qualified = path.segments.iter().rev().find_map(|part| {
            let effect = self.resolve(part.name.span)?;
            matches!(self.hir.definition(effect).kind, DefinitionKind::Effect(_))
                .then_some((effect, part.arguments.as_slice()))
        });
        let (qualified, args) = qualified.unwrap_or((owner, &[]));
        let selected = self.effect_arguments(env, qualified, args, path.span);
        let mut instance = self.effect_instances.get(&selected).cloned();
        let mut operation_effect = selected;
        if owner != qualified
            && let Some(outer) = &instance
        {
            let label = outer.includes.iter().find(|candidate| {
                self.effect_instances
                    .get(*candidate)
                    .is_some_and(|sub| sub.definition == owner)
            });
            if let Some(label) = label {
                operation_effect = label.clone();
                instance = self.effect_instances.get(label).cloned();
            }
        }
        self.operation_effects.insert(path.span, operation_effect);
        let Some(instance) = instance else {
            return HashMap::new();
        };
        let bindings = instance.bindings.clone();
        self.operation_instances.insert(path.span, instance);
        bindings
    }

    fn effect_arguments(
        &mut self,
        env: &mut Env,
        effect: DefinitionId,
        arguments: &[GenericArg],
        span: Span,
    ) -> String {
        let def = self.hir.definition(effect);
        let Some(stmt) = def.stmt else {
            return self.hir.effect_label(effect);
        };
        let StmtKind::Effect {
            generics, spreads, ..
        } = &self.ast(def.name.span.file).stmt(stmt).value.kind
        else {
            return self.hir.effect_label(effect);
        };
        let (arguments, mut local) = self.type_arguments(env, effect, generics, arguments, span);
        let arguments: Vec<_> = arguments
            .into_iter()
            .map(|argument| match argument {
                GenericValue::Type(ty) => GenericValue::Type(self.normalize(&ty)),
                argument => argument,
            })
            .collect();
        let label = label(self.hir, effect, &arguments);
        // Generic instances with the same printed parameter name can bind different
        // lexical parameters. Compute the bindings for every occurrence.
        let mut includes = BTreeSet::new();
        for &spread in spreads {
            let node = self.ast(local.file).ty(spread);
            if let Type::Named(path) = &node.value {
                let included = self.effect_label(&mut local, path);
                if let Some(instance) = self.effect_instances.get(&included) {
                    includes.extend(instance.includes.iter().cloned());
                }
                includes.insert(included);
            }
        }
        let mut operations = BTreeMap::new();
        for instance in &includes {
            if let Some(definition) = self
                .effect_instances
                .get(instance)
                .map(|sub| sub.definition)
            {
                for op in self.hir.effect_operations(definition) {
                    if self.hir.operation_effect(op) == Some(definition)
                        && let Some(previous) = operations.insert(op, instance)
                        && previous != instance
                    {
                        self.error(
                            Code::E0622,
                            span,
                            "spread exposes multiple instances of an effect operation",
                        );
                    }
                }
            }
        }
        self.effect_instances.insert(
            label.clone(),
            Instance {
                definition: effect,
                arguments,
                includes,
                bindings: local.generics,
            },
        );
        label
    }

    pub(super) fn effect_row_from_paths(
        &mut self,
        env: &mut Env,
        paths: &[Path],
    ) -> super::EffectRow {
        let mut row = super::EffectRow::default();
        for path in paths {
            if let Some(id) = self.resolve(path.span)
                && self.hir.is_effect_param(id)
            {
                if let Some(GenericValue::Effects(bound)) = env.generics.get(&id).cloned() {
                    row.merge(&bound);
                } else if !row.vars.contains(&id) {
                    row.vars.push(id);
                }
            } else {
                let label = self.effect_label(env, path);
                if !row.concrete.contains(&label) {
                    row.concrete.push(label);
                }
            }
        }
        row.concrete.sort();
        row.vars.sort();
        row
    }

    pub(super) fn call_effect_row(
        &mut self,
        id: DefinitionId,
        generics: &HashMap<DefinitionId, GenericValue>,
    ) -> Option<super::EffectRow> {
        let def = self.hir.definition(id);
        let StmtKind::Function(function) = &self.ast(def.name.span.file).stmt(def.stmt?).value.kind
        else {
            return None;
        };
        let mut local = Env::new(def.name.span.file, def.scope);
        local.generics.clone_from(generics);
        let mut raw =
            self.effect_row_from_paths(&mut local, &function.signature.obligations.effects);
        raw.open |= function.signature.obligations.open_effects;
        raw.direct_open |= function.signature.obligations.direct_open_effects;
        Some(self.normalize_effect_row(&raw))
    }
}
