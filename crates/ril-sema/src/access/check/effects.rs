use super::*;

impl Analyzer<'_> {
    pub(super) fn effect(&mut self, ctx: &Context, ledger: &Ledger, effect: &str, span: Span) {
        self.use_effect(ctx, ledger, Obligation::Effect(effect.into()), span, None);
    }

    pub(super) fn use_effect_var(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        var: DefinitionId,
        span: Span,
    ) {
        if ctx.shadow || !ctx.reachable {
            return;
        }
        let direct = self.program.hir.is_direct_effect_param(var);
        if !direct && ctx.no_ctl.is_some() {
            self.error(
                Code::E0616,
                span,
                "unconstrained effect row parameter may contain ctl and is prohibited in defer cleanup or fn handler arm; constrain with ': fn'",
            );
        }
        if !direct {
            let unarmed: Vec<_> = ledger
                .pending_linear()
                .filter(|occ| {
                    !ledger.linear_armed.get(*occ).is_some_and(|defer_span| {
                        ctx.ctl_boundary.is_none_or(|b| {
                            defer_span.file == b.file
                                && defer_span.start >= b.start
                                && defer_span.end <= b.end
                        })
                    })
                })
                .map(|occ| occ.span)
                .collect();
            for handle_span in unarmed {
                let mut diag = Diagnostic::error(
                    Code::E0625,
                    span,
                    "must-consume value must be managed by an armed defer across effect row call",
                );
                if handle_span != span {
                    diag = diag.with_label(handle_span, "unarmed must-consume value created here");
                }
                self.error_diag(diag);
            }
        }
        if ledger.iteration.iter().any(|iterable| {
            iterable
                .roots
                .iter()
                .any(|origin| origin.mode == Access::Shared)
        }) {
            self.error(
                Code::E0526,
                span,
                "shared collection being iterated cannot cross an unhandled effect",
            );
        }
        self.seed(ctx, Obligation::EffectVar(var));
    }

    pub(super) fn use_open_effect(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        direct: bool,
        span: Span,
    ) {
        if ctx.shadow || !ctx.reachable {
            return;
        }
        if !direct && ctx.no_ctl.is_some() {
            self.error(
                Code::E0616,
                span,
                "open '@' callback may contain ctl and is prohibited in defer cleanup or fn handler arm; use '@fn'",
            );
        }
        if !direct {
            let unarmed: Vec<_> = ledger
                .pending_linear()
                .filter(|occ| {
                    !ledger.linear_armed.get(*occ).is_some_and(|defer_span| {
                        ctx.ctl_boundary.is_none_or(|b| {
                            defer_span.file == b.file
                                && defer_span.start >= b.start
                                && defer_span.end <= b.end
                        })
                    })
                })
                .map(|occ| occ.span)
                .collect();
            for handle_span in unarmed {
                let mut diag = Diagnostic::error(
                    Code::E0625,
                    span,
                    "must-consume value must be managed by an armed defer across open '@' call",
                );
                if handle_span != span {
                    diag = diag.with_label(handle_span, "unarmed must-consume value created here");
                }
                self.error_diag(diag);
            }
        }
        if ledger.iteration.iter().any(|iterable| {
            iterable
                .roots
                .iter()
                .any(|origin| origin.mode == Access::Shared)
        }) {
            self.error(
                Code::E0526,
                span,
                "shared collection being iterated cannot cross an unhandled effect",
            );
        }
        self.seed(
            ctx,
            if direct {
                Obligation::DirectOpenEffect
            } else {
                Obligation::OpenEffect
            },
        );
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
            _ => ril_source::ice!("expected effect obligation"),
        };
        if !operations.is_empty() && operations.iter().all(|id| ctx.handlers.contains_key(id)) {
            for op in &operations {
                if self.program.hir.is_ctl_operation(op.id)
                    && ctx.ctl_boundary.is_none_or(|b| {
                        b.file != ctx.owner.file
                            || b.start < ctx.owner.start
                            || b.end > ctx.owner.end
                    })
                {
                    self.rules.push(Rule {
                        premises: if_exercised.iter().cloned().collect(),
                        conclusion: Fact {
                            owner: ctx.owner,
                            obligation: Obligation::CtlHandler,
                        },
                    });
                }
                if let Some(handler) = ctx.handlers.get(op) {
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
            }
            return;
        }
        let has_ctl = match &obligation {
            Obligation::Operation(op) => self.program.hir.is_ctl_operation(op.id),
            Obligation::Effect(effect) => self.program.effect_has_ctl(effect),
            _ => false,
        };
        if has_ctl && ctx.no_ctl.is_some() {
            let diag = Diagnostic::error(
                Code::E0616,
                span,
                "unhandled ctl effect is prohibited in defer cleanup or fn handler arm",
            );
            if let Some(fact) = &if_exercised {
                self.deferred_errors.push((vec![fact.clone()], diag));
            } else {
                self.error_diag(diag);
            }
        }
        if has_ctl {
            let unarmed: Vec<_> = ledger
                .pending_linear()
                .filter(|occ| {
                    !ledger.linear_armed.get(*occ).is_some_and(|defer_span| {
                        ctx.ctl_boundary.is_none_or(|b| {
                            defer_span.file == b.file
                                && defer_span.start >= b.start
                                && defer_span.end <= b.end
                        })
                    })
                })
                .map(|occ| occ.span)
                .collect();
            for handle_span in unarmed {
                let mut diag = Diagnostic::error(
                    Code::E0625,
                    span,
                    "must-consume value must be managed by an armed defer across unhandled ctl call",
                );
                if handle_span != span {
                    diag = diag.with_label(handle_span, "unarmed must-consume value created here");
                }
                if let Some(fact) = &if_exercised {
                    self.deferred_errors.push((vec![fact.clone()], diag));
                } else {
                    self.error_diag(diag);
                }
            }
        }
        if (has_ctl || label != "io")
            && ledger.iteration.iter().any(|iterable| {
                iterable
                    .roots
                    .iter()
                    .any(|origin| origin.mode == Access::Shared)
            })
        {
            let diag = Diagnostic::error(
                Code::E0526,
                span,
                "shared collection being iterated cannot cross an unhandled effect",
            );
            if let Some(fact) = &if_exercised {
                self.deferred_errors.push((vec![fact.clone()], diag));
            } else {
                self.error_diag(diag);
            }
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

    pub(super) fn charge_latent_effects(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        value: &Datum,
        span: Span,
    ) {
        self.charge_latent_effects_if(ctx, ledger, value, span, None);
    }

    pub(super) fn charge_latent_effects_if(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        value: &Datum,
        span: Span,
        if_exercised: Option<&Fact>,
    ) {
        for (id, effect) in &value.latent_operations {
            self.use_effect(
                ctx,
                ledger,
                Obligation::Operation(Operation {
                    id: *id,
                    effect: effect.clone(),
                }),
                span,
                if_exercised.cloned(),
            );
        }
        for effect in &value.latent_effects {
            self.use_effect(
                ctx,
                ledger,
                Obligation::Effect(effect.clone()),
                span,
                if_exercised.cloned(),
            );
        }
        for &var in &value.latent_effect_vars {
            self.use_effect_var(ctx, ledger, var, span);
        }
        if value.latent_open_effect || value.latent_direct_open_effect {
            self.use_open_effect(
                ctx,
                ledger,
                value.latent_direct_open_effect && !value.latent_open_effect,
                span,
            );
        }
    }

    pub(super) fn charge_latent_effects_filtered_if(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        value: &Datum,
        covered: &[String],
        span: Span,
        if_exercised: Option<&Fact>,
    ) {
        for (id, effect) in &value.latent_operations {
            if covered
                .iter()
                .any(|cov| self.program.effect_covers(cov, effect))
            {
                continue;
            }
            self.use_effect(
                ctx,
                ledger,
                Obligation::Operation(Operation {
                    id: *id,
                    effect: effect.clone(),
                }),
                span,
                if_exercised.cloned(),
            );
        }
        for effect in &value.latent_effects {
            if covered
                .iter()
                .any(|cov| self.program.effect_covers(cov, effect))
            {
                continue;
            }
            self.use_effect(
                ctx,
                ledger,
                Obligation::Effect(effect.clone()),
                span,
                if_exercised.cloned(),
            );
        }
        for &var in &value.latent_effect_vars {
            self.use_effect_var(ctx, ledger, var, span);
        }
        if value.latent_open_effect || value.latent_direct_open_effect {
            self.use_open_effect(
                ctx,
                ledger,
                value.latent_direct_open_effect && !value.latent_open_effect,
                span,
            );
        }
    }

    pub(super) fn has_unhandled_ctl(&self, ctx: &Context, value: &Datum, ty: &Ty) -> bool {
        self.has_unhandled_ctl_filtered(ctx, value, ty, &[])
    }

    pub(super) fn has_unhandled_ctl_filtered(
        &self,
        ctx: &Context,
        value: &Datum,
        ty: &Ty,
        covered: &[String],
    ) -> bool {
        if value.latent_open_effect
            || value
                .latent_effect_vars
                .iter()
                .any(|v| !self.program.hir.is_direct_effect_param(*v))
        {
            return true;
        }
        if value.latent_operations.iter().any(|(id, effect)| {
            self.program.hir.is_ctl_operation(*id)
                && !covered
                    .iter()
                    .any(|cov| self.program.effect_covers(cov, effect))
                && !ctx.handlers.contains_key(&Operation {
                    id: *id,
                    effect: effect.clone(),
                })
        }) {
            return true;
        }
        let check_effect = |effect: &str| {
            !covered
                .iter()
                .any(|cov| self.program.effect_covers(cov, effect))
                && self.program.effect_has_ctl(effect)
                && self.effect_operations(effect).iter().any(|op| {
                    self.program.hir.is_ctl_operation(op.id) && !ctx.handlers.contains_key(op)
                })
        };
        if value.latent_effects.iter().any(|eff| check_effect(eff)) {
            return true;
        }
        if let Ty::Callable(sig) = ty
            && (sig.open_effects
                || sig.effects.iter().any(|eff| check_effect(eff))
                || sig
                    .effect_vars
                    .iter()
                    .any(|v| !self.program.hir.is_direct_effect_param(*v)))
        {
            return true;
        }
        false
    }

    pub(super) fn named_value_has_live_state(
        &mut self,
        id: DefinitionId,
        _ctx: &Context,
        ledger: &Ledger,
    ) -> bool {
        let mut captured = self
            .function_syntax(id)
            .into_iter()
            .flat_map(|fun| &fun.signature.obligations.state)
            .filter(|clause| clause.kind == StateKind::Environment)
            .flat_map(|clause| &clause.bindings);
        captured.any(|(storage, path)| {
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
        })
    }
}
