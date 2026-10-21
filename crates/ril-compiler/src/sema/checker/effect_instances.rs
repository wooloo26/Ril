//! Effect-only static reification. Internal binder names are created after the
//! public owned-AST validation boundary and require an entry in the registry.
use super::super::effect_identity::{EffectInvocation, StaticArgumentWitness};
use super::*;

#[derive(Default)]
pub(super) struct StaticArguments {
    pub arguments: Vec<StaticArgumentWitness>,
    pub captured_arguments: Vec<StaticArgumentWitness>,
    pub unresolved_captured_binders: BTreeSet<String>,
}

impl Checker {
    fn certified_effect_type_binder(&self, identity: &str) -> bool {
        let Some(binder) = self.generic_binders.get(identity) else {
            return false;
        };
        let parameter = self
            .functions
            .iter()
            .find(|function| function.definition == binder.definition)
            .and_then(|function| function.syntax.generics.get(binder.index as usize));
        parameter.is_some_and(|parameter| {
            crate::sema::record_bounds::certifies_type_sort(
                identity,
                binder,
                parameter,
                &self.record_bounds,
            )
        })
    }
    fn effect_binder_type(&mut self, identity: &str, span: Span) -> TypeExpr {
        let token = format!("\0effect-binder:{identity}");
        self.effect_type_binders
            .insert(token.clone(), identity.into());
        TypeExpr {
            hir_id: None,
            text: String::new(),
            span,
            kind: TypeKind::Name {
                path: vec![token],
                arguments: vec![],
            },
        }
    }

    fn registered_effect_row_binder(&self, name: &str, identity: &str) -> bool {
        self.effect_type_binders
            .get(name)
            .is_some_and(|actual| actual == identity)
            && self.bound_rows.iter().any(|row| {
                matches!(&row.identity,
                    crate::sema::model::rows::RowIdentity::Binder(actual) if actual == identity)
                    && !row.declaration_paths.is_empty()
            })
    }

    fn effect_selected_type(&mut self, ty: &Ty, span: Span) -> Option<TypeExpr> {
        let ty = self.call_inference_type(ty);
        if let Ty::Generic(identity) = &ty {
            if !self.certified_effect_type_binder(identity) {
                return None;
            }
            return Some(self.effect_binder_type(identity, span));
        }
        // Reification must retain all qualifiers. In particular, do not turn
        // an inferred fixed array or callable into the weaker erased Ty view.
        self.selected_type_key(&ty)?;
        io_types::data_type(&ty, span)
    }

    pub(super) fn effect_argument_syntax(
        &mut self,
        syntax: &TypeExpr,
    ) -> Result<TypeExpr, &'static str> {
        crate::static_eval::effects::bounded_argument_key(syntax, &self.effect_type_binders)
            .ok_or("effect Source syntax exceeds its work bound")?;
        self.effect_argument_syntax_inner(syntax, 0, false, &mut 4096)
    }

    fn effect_argument_syntax_inner(
        &mut self,
        syntax: &TypeExpr,
        depth: usize,
        row_position: bool,
        work: &mut usize,
    ) -> Result<TypeExpr, &'static str> {
        *work = work
            .checked_sub(1)
            .ok_or("effect Source interpretation exhausted its work bound")?;
        if depth >= 64 {
            return Err("effect Source capture chain exceeds its depth bound");
        }
        let mut syntax = syntax.clone();
        if let TypeKind::Name { path, arguments } = &syntax.kind {
            let name = path.join("::");
            if let Some(identity) = self
                .effect_type_binders
                .get(&name)
                .or_else(|| self.type_source.environment.generic_context.get(&name))
                .cloned()
            {
                if !arguments.is_empty() {
                    return Err(
                        "symbolic effect type constructor requires a kind substitution proof",
                    );
                }
                *work = work
                    .checked_sub(self.functions.len() + 3 + 3 * identity.len().div_ceil(32))
                    .ok_or("effect Source binder lookup exhausted its work bound")?;
                if !self.certified_effect_type_binder(&identity) {
                    if row_position {
                        *work = work
                            .checked_sub(self.bound_rows.len())
                            .ok_or("effect Source row lookup exhausted its work bound")?;
                        if self.registered_effect_row_binder(&name, &identity) {
                            return Ok(self.effect_binder_type(&identity, syntax.span));
                        }
                    }
                    return Err("symbolic effect argument requires a certified Type binder sort");
                }
                if let Some(selection) = self
                    .type_source
                    .environment
                    .generic_sources
                    .get(&identity)
                    .cloned()
                {
                    if selection.closed().is_some() {
                        if !selection.validate_closed() {
                            self.unsupported(
                                syntax.span,
                                "closed effect Source differs from its original graph",
                            );
                            return Err("closed effect Source differs from its original graph");
                        }
                        return Ok(selection.syntax.as_ref().clone());
                    }
                    use crate::sema::source_types::{SourceTypesError, WorkLimit};
                    let span = syntax.span;
                    let mut budget = WorkLimit::new(*work);
                    let projected = selection.quantified_syntax_projection(
                        span,
                        &mut budget,
                        &mut |identity, row, budget| {
                            budget.charge(
                                self.functions.len()
                                    + selection.environment.bound_row_context.len()
                                    + 3 + 3 * identity.len().div_ceil(32),
                            )?;
                            let genuine_type = self.certified_effect_type_binder(identity);
                            let genuine_row = row && selection.environment.bound_row_context.values()
                                .any(|id| self.bound_rows.get(id.0 as usize).is_some_and(|declaration| {
                                    declaration.id == *id && matches!(&declaration.identity,
                                        crate::sema::model::rows::RowIdentity::Binder(actual) if actual == identity)
                                }));
                            if !genuine_type && !genuine_row {
                                return Err(SourceTypesError::Unresolved);
                            }
                            Ok(self.effect_binder_type(identity, span))
                        },
                    );
                    *work = budget.remaining();
                    return projected.map_err(|error| {
                        self.unsupported(
                            span,
                            format!("captured effect Source graph projection failed: {error}"),
                        );
                        "captured effect Source has no complete bounded graph projection"
                    });
                }
                return if let Some(selected) = self
                    .type_source
                    .environment
                    .generic_substitutions
                    .get(&identity)
                    .cloned()
                {
                    self.effect_selected_type(&selected, syntax.span)
                        .ok_or("selected effect argument lacks its complete source type shape")
                } else {
                    Ok(self.effect_binder_type(&identity, syntax.span))
                };
            }
            if let Some(declaration) = self.types.get(&name) {
                let mut dependencies = BTreeSet::new();
                if let Some(value) = &declaration.value {
                    dependencies.extend(crate::static_eval::effects::type_dependencies(value));
                }
                for parameter in &declaration.generics {
                    if let Some(bound) = &parameter.bound {
                        dependencies.extend(crate::static_eval::effects::type_dependencies(bound));
                    }
                    if let Some(default) = &parameter.default {
                        dependencies
                            .extend(crate::static_eval::effects::type_dependencies(default));
                    }
                }
                for parameter in &declaration.generics {
                    dependencies.remove(&parameter.name);
                }
                if dependencies.iter().any(|name| {
                    self.type_source
                        .environment
                        .generic_context
                        .contains_key(name)
                }) {
                    return Err(
                        "effect argument alias captures an enclosing binder without its declaration environment",
                    );
                }
            }
        }
        match &mut syntax.kind {
            TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
                for argument in arguments {
                    *argument =
                        self.effect_argument_syntax_inner(argument, depth + 1, false, work)?;
                }
            }
            TypeKind::Optional(inner) => {
                **inner = self.effect_argument_syntax_inner(inner, depth + 1, false, work)?
            }
            TypeKind::Array { length, element } => {
                if let Some(length) = length {
                    let probe = TypeExpr {
                        hir_id: None,
                        text: String::new(),
                        span: length.span,
                        kind: TypeKind::Computation(length.clone()),
                    };
                    self.closed_effect_syntax(&probe)?;
                }
                **element = self.effect_argument_syntax_inner(element, depth + 1, false, work)?;
            }
            TypeKind::Map { key, value } => {
                **key = self.effect_argument_syntax_inner(key, depth + 1, false, work)?;
                **value = self.effect_argument_syntax_inner(value, depth + 1, false, work)?;
            }
            TypeKind::Record { fields, row } => {
                for field in fields {
                    field.ty =
                        self.effect_argument_syntax_inner(&field.ty, depth + 1, false, work)?;
                }
                if let Some(row) = row {
                    **row = self.effect_argument_syntax_inner(row, depth + 1, true, work)?;
                }
            }
            TypeKind::Callable {
                parameters,
                result,
                annotations,
            } => {
                if !annotations.is_empty() {
                    if !self.type_source.environment.generic_context.is_empty() {
                        return Err(
                            "effect argument callable rows require their canonical lexical binder environment",
                        );
                    }
                    self.closed_effect_syntax(&syntax)?;
                    return Ok(syntax);
                }
                for parameter in parameters {
                    if let Some(ty) = &mut parameter.ty {
                        *ty = self.effect_argument_syntax_inner(ty, depth + 1, false, work)?;
                    }
                }
                if let Some(result) = result {
                    **result = self.effect_argument_syntax_inner(result, depth + 1, false, work)?;
                }
            }
            _ => self.closed_effect_syntax(&syntax)?,
        }
        Ok(syntax)
    }

    fn closed_effect_syntax(&self, syntax: &TypeExpr) -> Result<(), &'static str> {
        if !self.type_source.environment.generic_context.is_empty()
            && matches!(
                syntax.kind,
                TypeKind::TypeFunction { .. } | TypeKind::KindArrow { .. }
            )
        {
            return Err(
                "symbolic higher-kind effect arguments require a canonical lexical environment",
            );
        }
        if crate::static_eval::effects::type_dependencies(syntax)
            .iter()
            .any(|name| {
                self.type_source
                    .environment
                    .generic_context
                    .contains_key(name)
                    || self.effect_type_binders.contains_key(name)
            })
        {
            Err("symbolic effect computation requires a canonical static substitution proof")
        } else {
            Ok(())
        }
    }

    pub(super) fn static_arguments_for(
        &mut self,
        info: &FunctionInfo,
        site: Span,
    ) -> StaticArguments {
        let arguments = info
            .syntax
            .generics
            .iter()
            .enumerate()
            .map(|(index, parameter)| {
                let identity = self
                    .type_source
                    .environment
                    .generic_context
                    .get(&parameter.name)
                    .cloned()
                    .unwrap_or_default();
                let syntax = TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span: site,
                    kind: TypeKind::Name {
                        path: vec![parameter.name.clone()],
                        arguments: vec![],
                    },
                };
                let syntax = self.effect_argument_syntax(&syntax).ok();
                let key = syntax.as_ref().map(|syntax| {
                    crate::static_eval::effects::argument_key(syntax, &self.effect_type_binders)
                });
                StaticArgumentWitness {
                    definition: info.definition,
                    index: index as u32,
                    binder: identity,
                    key,
                    syntax,
                }
            })
            .collect();
        let mut captured_arguments = Vec::new();
        let mut unresolved_captured_binders = BTreeSet::new();
        for (name, identity) in &info.typing_environment.generic_context {
            if info
                .syntax
                .generics
                .iter()
                .any(|parameter| parameter.name == *name)
            {
                continue;
            }
            let Some(binder) = self.generic_binders.get(identity).cloned() else {
                unresolved_captured_binders.insert(identity.clone());
                continue;
            };
            let written = TypeExpr {
                hir_id: None,
                text: String::new(),
                span: site,
                kind: TypeKind::Name {
                    path: vec![name.clone()],
                    arguments: vec![],
                },
            };
            let syntax = self.effect_argument_syntax(&written).ok();
            let key = syntax.as_ref().map(|syntax| {
                crate::static_eval::effects::argument_key(syntax, &self.effect_type_binders)
            });
            captured_arguments.push(StaticArgumentWitness {
                definition: binder.definition,
                index: binder.index,
                binder: identity.clone(),
                key,
                syntax,
            });
        }
        StaticArguments {
            arguments,
            captured_arguments,
            unresolved_captured_binders,
        }
    }

    pub(super) fn record_effect_invocation(
        &mut self,
        info: &FunctionInfo,
        site: Span,
        summary: &super::super::summary::InvocationSummary,
        verifying: bool,
        callback_epoch: usize,
    ) {
        let selected = self.static_arguments_for(info, site);
        self.effect_invocations.push(EffectInvocation {
            invocation: self.copy_invocation_stack.last().copied(),
            budget_validation: self.budget_validation_depth > 0,
            function: info.definition,
            site,
            arguments: selected.arguments,
            captured_arguments: selected.captured_arguments,
            unresolved_captured_binders: selected.unresolved_captured_binders,
            operations: summary.performed_operations.clone(),
            callbacks: self.effect_callback_uses[callback_epoch..].to_vec(),
            unresolved: summary.unresolved.clone(),
            verifying,
        });
    }
}
