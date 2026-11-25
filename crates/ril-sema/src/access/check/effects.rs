use super::*;

impl Analyzer<'_> {
    pub(super) fn effect(&mut self, ctx: &Context, ledger: &Ledger, effect: &str, span: Span) {
        self.use_effect(ctx, ledger, Obligation::Effect(effect.into()), span, None);
    }

    pub(super) fn operation(&self, id: DefinitionId, path: Span) -> Option<Operation> {
        let definition = self.program.hir.operation_effect(id)?;
        let effect = self
            .program
            .operation_effects
            .get(&path)
            .cloned()
            .unwrap_or_else(|| self.program.hir.effect_label(definition));
        Some(Operation { id, effect })
    }

    pub(super) fn effect_operations(&self, effect: &str) -> Vec<Operation> {
        let hir = &self.program.hir;
        let Some(definition) = self.program.effect_definition(effect) else {
            return Vec::new();
        };
        let children = self
            .program
            .effect_instances
            .get(effect)
            .map(|instance| &instance.includes);
        hir.effect_operations(definition)
            .filter_map(|id| {
                let original = hir.operation_effect(id)?;
                let instance = if original == definition {
                    effect.to_owned()
                } else if let Some(label) = children
                    .into_iter()
                    .flatten()
                    .find(|label| self.program.effect_definition(label) == Some(original))
                {
                    label.clone()
                } else {
                    hir.effect_label(original)
                };
                Some(Operation {
                    id,
                    effect: instance,
                })
            })
            .collect()
    }

    pub(super) fn use_effect(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        obligation: Obligation,
        span: Span,
        if_exercised: Option<Fact>,
    ) {
        if ctx.shadow || !ctx.reachable {
            return;
        }
        let (label, operations) = match &obligation {
            Obligation::Operation(operation) => (operation.effect.clone(), vec![operation.clone()]),
            Obligation::Effect(effect) => (effect.clone(), self.effect_operations(effect)),
            _ => ril_base::ice!("expected effect obligation"),
        };
        if !operations.is_empty() && operations.iter().all(|id| ctx.handlers.contains_key(id)) {
            for handler in operations.iter().filter_map(|id| ctx.handlers.get(id)) {
                self.link_invocation_if(ctx, handler, if_exercised.as_ref());
                self.check_handler_iteration(ledger, handler, span, if_exercised.as_ref());
                if handler.live_callable_state
                    || handler
                        .origins()
                        .any(|origin| origin.mode != Access::Immutable)
                {
                    self.rules.push(Rule {
                        premises: if_exercised.iter().cloned().collect(),
                        conclusion: Fact {
                            owner: ctx.owner,
                            obligation: Obligation::StatefulHandler,
                        },
                    });
                }
            }
            return;
        }
        let local_effect = self
            .program
            .effect_definition(&label)
            .is_some_and(|definition| {
                ctx.local_effects
                    .contains(&self.program.hir.effect_label(definition))
            });
        let error = if local_effect {
            Some((
                Code::E0618,
                "effect must be handled in its declaring block".into(),
            ))
        } else if !ctx.in_function {
            Some((
                Code::E0202,
                format!("top-level initialization cannot perform @{label}"),
            ))
        } else {
            None
        };
        if let Some((code, message)) = error {
            if let Some(fact) = if_exercised {
                self.deferred_errors
                    .push((vec![fact], Diagnostic::error(code, span, message)));
            } else {
                self.error(code, span, message);
            }
        } else {
            self.rules.push(Rule {
                premises: if_exercised.into_iter().collect(),
                conclusion: Fact {
                    owner: ctx.owner,
                    obligation,
                },
            });
        }
    }

    pub(super) fn check_handler_iteration(
        &mut self,
        ledger: &Ledger,
        handler: &Datum,
        span: Span,
        exercised: Option<&Fact>,
    ) {
        if ledger.iteration.is_empty() {
            return;
        }
        for (&owner, captures) in &handler.invocations {
            for (&source, actual) in captures {
                let overlap = handler.origins().any(|origin| {
                    origin.mode.writes()
                        && (actual.contains(&origin.region.source)
                            || origin.dependency_spans().any(|span| span == source))
                        && ledger
                            .iteration
                            .iter()
                            .any(|iterable| iterable.origins().any(|value| value.overlaps(origin)))
                });
                if overlap {
                    let premises = std::iter::once(Fact {
                        owner,
                        obligation: Obligation::Write(source),
                    })
                    .chain(exercised.cloned())
                    .collect();
                    self.deferred_errors.push((
                        premises,
                        Diagnostic::error(
                            Code::E0526,
                            span,
                            "effect handler writes to a collection being iterated",
                        ),
                    ));
                }
            }
        }
    }

    pub(super) fn requirement(
        &mut self,
        ctx: &Context,
        span: Span,
        obligation: Obligation,
        msg: &'static str,
    ) {
        if ctx.reachable && !ctx.shadow {
            self.requirements.push(Requirement {
                fact: Fact {
                    owner: ctx.owner,
                    obligation,
                },
                span,
                message: msg,
            });
        }
    }

    pub(super) fn record_effect_use(
        &self,
        function: &DefinitionCheck,
        summary: &mut Summary,
        effect: &str,
        operation: Option<DefinitionId>,
    ) {
        summary.effects.push(effect.to_owned());
        for (declaration, declared) in function.declared.effects.iter().enumerate() {
            if self.program.effect_covers(declared, effect) {
                summary.effect_uses.push(EffectUse {
                    declaration,
                    effect: effect.to_owned(),
                    operation: operation.map(|operation| self.program.hir.export_name(operation)),
                });
            }
        }
    }

    pub(super) fn named_value_has_live_state(
        &mut self,
        id: DefinitionId,
        ctx: &Context,
        ledger: &Ledger,
    ) -> bool {
        let function = self.function_syntax(id);
        let mut captured = self
            .function_syntax(id)
            .into_iter()
            .flat_map(|fun| &fun.signature.obligations.state)
            .filter(|clause| clause.kind == StateKind::Environment)
            .flat_map(|clause| &clause.bindings);
        if captured.any(|(storage, path)| {
            storage.variable
                || storage.mode != Mode::Plain
                || self
                    .declaration(path.span)
                    .and_then(|decl| ledger.slots.get(&decl))
                    .is_some_and(|slot| {
                        slot.variable
                            || slot.value.contains_live_callable_environment()
                            || slot
                                .value
                                .origins()
                                .any(|root| root.mode != Access::Immutable)
                    })
        }) {
            return true;
        }
        let live_handlers: Vec<_> = self
            .program
            .callables
            .get(&id)
            .into_iter()
            .flat_map(|callable| &callable.effects)
            .flat_map(|effect| self.effect_operations(effect))
            .filter(|operation| {
                ctx.handlers.get(operation).is_some_and(|handler| {
                    handler.live_callable_state
                        || handler
                            .origins()
                            .any(|origin| origin.mode != Access::Immutable)
                })
            })
            .collect();
        if live_handlers.is_empty() {
            return false;
        }
        if let Some(function) = function
            && ctx.reachable
            && !ctx.shadow
        {
            self.function(function, ledger);
        }
        live_handlers
            .iter()
            .any(|operation| self.named_may_use_handler(id, operation))
    }

    pub(super) fn named_may_use_handler(&self, id: DefinitionId, operation: &Operation) -> bool {
        let uses_handler = |obligation: &Obligation| match obligation {
            Obligation::Operation(used) => used == operation,
            Obligation::Effect(effect) => self.program.effect_covers(effect, &operation.effect),
            _ => false,
        };
        if let Some(imported) = self.program.imported_functions.get(&id)
            && let Some(signature) = self.program.callables.get(&id)
        {
            let owner = self.program.hir.definition(id).name.span;
            return self
                .imported_effect_obligations(owner, signature, &imported.summary, owner)
                .iter()
                .any(uses_handler);
        }
        let Some(checked) = self.functions.iter().find(|function| function.id == id) else {
            // A foreign or currently recursive body has only its declared bound.
            return true;
        };
        self.rules.iter().any(|rule| {
            rule.conclusion.owner == checked.owner && uses_handler(&rule.conclusion.obligation)
        })
    }
}
