use super::*;

impl Analyzer<'_> {
    pub(super) fn function(&mut self, fun: &Function, outer: &Ledger) {
        let Some(id) = self.definition(fun.name.span) else {
            return;
        };
        if !self.done.insert(id) {
            return;
        }
        let Some(callable) = self.program.callables.get(&id) else {
            return;
        };
        let Some(body) = fun.body else {
            if self.program.hir.file(fun.name.span.file).kind == FileKind::Foreign {
                self.check_foreign(fun, callable);
            }
            return;
        };
        let mut ctx = Context::new(fun.name.span);
        if let Some(statement) = self.program.hir.definition(id).stmt {
            ctx.scope = self.ast(ctx.file).stmt(statement).span;
        }
        ctx.in_function = true;
        ctx.set_caller_storage(outer);
        ctx.runtime = !fun.is_meta;
        ctx.expected = fun.signature.result_mode;
        ctx.formals = fun
            .signature
            .params
            .iter()
            .map(|p| p.name.as_ref().map(|name| name.span))
            .collect();
        ctx.returns = fun
            .signature
            .result_sources
            .iter()
            .filter_map(|name| self.declaration(name.span))
            .collect();
        ctx.declared_contained = self.declared_sources(&fun.signature);
        let capture_modes: BTreeMap<_, _> = fun
            .signature
            .obligations
            .state
            .iter()
            .filter(|clause| clause.kind == StateKind::Environment)
            .flat_map(|clause| &clause.bindings)
            .filter_map(|(storage, path)| {
                self.declaration(path.span)
                    .map(|binding| (binding, storage.mode))
            })
            .collect();
        let captures: BTreeSet<_> = capture_modes.keys().copied().collect();
        ctx.capture_modes = Some(capture_modes);
        let mut ledger = outer.clone();
        ledger.enter_capture_storage(ctx.owner, &ctx.formals, |binding| {
            captures.contains(&binding)
        });
        ledger.clear_result_obligations();
        ledger.clear_array_extents();
        ledger.inspected.clear();
        ledger.reset_revocations();
        ledger.no_continuation = false;
        ledger.iteration.clear();
        ledger.holds.clear();
        if callable.open_effects || callable.open_state {
            self.error(
                Code::E0547,
                ctx.owner,
                "named definitions require closed effect and state sets",
            );
        }
        for (ast_param, param) in fun.signature.params.iter().zip(&callable.parameters) {
            let span = ast_param.name.as_ref().map_or(ctx.owner, |name| name.span);
            self.binding_scopes.insert(span, ctx.scope);
            if param.mode == Mode::Via {
                ctx.via.insert(span);
                if param.ty.is_value() {
                    self.error(
                        Code::E0550,
                        span,
                        "via is redundant on a value-type parameter",
                    );
                }
            }
            if param.mode == Mode::New && param.ty.is_value() {
                self.error(Code::E0411, span, "new parameter requires a shared object");
            }
            if param.mode == Mode::New {
                ctx.new_formals.insert(span);
            }
            let mut value = if param.ty.is_value() {
                Datum::default()
            } else {
                Datum::source(span, Access::from_mode(param.mode), param.mode == Mode::New)
            };
            value.transform(&mut |origin| {
                origin.dependencies.insert(span.into());
                origin.enter_formal(ctx.owner, param.mode);
                if matches!(param.ty, Ty::Draft(_)) {
                    origin.draft = true;
                    origin.confined = Some(ctx.scope);
                }
            });
            value = results::receive_results(self.program, &mut ledger, &param.ty, value, span);
            ledger.slots.insert(
                span,
                Slot {
                    decl: span,
                    variable: false,
                    mode: param.mode,
                    value,
                },
            );
            if param.mode == Mode::Mut {
                self.requirement(
                    &ctx,
                    span,
                    Obligation::Write(span),
                    "mut parameter requires reachable write, forwarding, or handoff",
                );
            }
            if param.mode == Mode::Shared {
                self.requirement(
                    &ctx,
                    span,
                    Obligation::Retain(span),
                    "shared parameter must be retained",
                );
            }
        }
        let member_axes = member_axes(callable, &ctx.formals);
        self.register_member_axes(&member_axes);
        ctx.member_via = !member_axes.is_empty();
        for clause in &fun.signature.obligations.state {
            if matches!(clause.kind, StateKind::Environment | StateKind::Return)
                && clause.bindings.is_empty()
            {
                self.error(
                    Code::E0538,
                    clause.span,
                    "named state groups require source bindings",
                );
            }
        }
        for &helper in &fun.helpers {
            self.statement(&mut ctx, &mut ledger, helper, false);
        }
        let value = self.expr(&mut ctx, &mut ledger, body);
        let body_span = self.ast(ctx.file).expr(body).span;
        if ctx.reachable && self.ty(body_span) != &Ty::Never {
            self.returned(&mut ctx, &mut ledger, value, body_span);
            self.check_results(&ledger, &BTreeSet::new());
        }
        let mut return_sources = BTreeSet::new();
        for value in &ctx.return_values {
            value.visit_origins(&mut Vec::new(), &mut |result_path, origin| {
                let Some(formal) = ctx
                    .formals
                    .iter()
                    .position(|param| *param == Some(origin.region.source))
                else {
                    return;
                };
                let access = if result_path.is_empty() {
                    match ctx.expected {
                        Mode::Ref | Mode::Shared => Access::from_mode(ctx.expected),
                        Mode::Infer => origin.mode,
                        _ => return,
                    }
                } else if !origin.new && ctx.expected != Mode::Plain {
                    origin.mode
                } else {
                    return;
                };
                return_sources.insert(ReturnSource {
                    formal,
                    source_path: origin.region.selection.clone(),
                    result_path: result_path.to_vec(),
                    access,
                });
            });
        }
        if ctx.runtime && ctx.expected != Mode::Infer && !ctx.return_values.is_empty() {
            let excess = ctx.declared_contained.iter().any(|&(mode, source)| {
                ctx.formals
                    .iter()
                    .position(|decl| *decl == Some(source))
                    .is_none_or(|index| {
                        !return_sources.iter().any(|entry| {
                            entry.formal == index
                                && entry.access == mode
                                && !entry.result_path.is_empty()
                        })
                    })
            });
            if excess {
                self.error(Code::E0529, ctx.owner, "unused contained return source");
            }
        }
        let exits = self.storage_exits.remove(&ctx.owner).unwrap_or_default();
        let storage::StorageExit {
            mut updates,
            flow: mut storage_flow,
        } = storage::StorageExit::join(&exits);
        calls::seal_call_allocations(
            &mut self.callback_results,
            ctx.return_values
                .iter_mut()
                .filter(|value| {
                    ctx.expected != Mode::Plain
                        || !value.results().is_empty()
                        || value.has_array_layout()
                })
                .chain(updates.values_mut().map(|update| &mut update.value))
                .chain(storage_flow.iter_mut().flat_map(StorageFlow::values_mut)),
            body_span,
        );
        self.functions.push(DefinitionCheck {
            owner: ctx.owner,
            id,
            formals: ctx.formals,
            declared: (**callable).clone(),
            via: ctx.via,
            member_axes,
            return_sources: return_sources.into_iter().collect(),
            returned_new: !ctx.return_values.is_empty()
                && ctx.return_values.iter().all(|value| value.requires_new),
            returns: ctx.return_values,
            updates,
            storage_flow,
            normal_exit: !exits.is_empty(),
            capture_names: captures,
        });
    }

    pub(super) fn declared_sources(&self, signature: &Signature) -> Vec<(Access, Span)> {
        signature
            .obligations
            .state
            .iter()
            .filter(|clause| clause.kind == StateKind::Return)
            .flat_map(|clause| &clause.bindings)
            .filter_map(|(storage, path)| {
                self.declaration(path.span)
                    .map(|span| (Access::from_mode(storage.mode), span))
            })
            .collect()
    }

    pub(super) fn check_foreign(&mut self, fun: &Function, signature: &Callable) {
        let prohibited = matches!(
            signature.result_mode,
            Mode::Shared | Mode::Via | Mode::Infer
        ) || signature
            .state
            .iter()
            .any(|state| matches!(state.as_str(), "^mut" | "capture"))
            || signature.parameters.iter().any(|parameter| {
                matches!(parameter.mode, Mode::Shared | Mode::Via)
                    || parameter.mode == Mode::Plain
                        && matches!(&parameter.ty, Ty::Adt(adt) if adt.kind == AdtKind::Foreign)
            })
            || signature.result_mode == Mode::Plain
                && matches!(&signature.result, Ty::Adt(adt) if adt.kind == AdtKind::Foreign);
        if prohibited {
            self.error(
                Code::E0908,
                fun.name.span,
                "foreign signature requires non-shared handle authority",
            );
        }
    }

    pub(super) fn finish_function(
        &mut self,
        facts: &BTreeSet<Fact>,
        fun: &DefinitionCheck,
    ) -> Summary {
        let mut summary = Summary {
            return_sources: fun.return_sources.clone(),
            return_allocations: Datum::return_allocations(&fun.returns),
            constructs: fun.returned_new,
            nonreturning: !fun.normal_exit,
            invocations: self
                .invocation_summaries
                .remove(&fun.owner)
                .into_iter()
                .flatten()
                .collect(),
            mode_calls: Some(
                self.mode_call_summaries
                    .remove(&fun.owner)
                    .into_iter()
                    .flatten()
                    .collect(),
            ),
            callback_returns: fun
                .returns
                .iter()
                .flat_map(|value| self.callback_return_contracts(&fun.formals, value))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect(),
            storage_updates: self.storage_contracts(fun),
            snapshot_inputs: self.snapshots.inputs(fun.owner, &fun.formals),
            ..Summary::default()
        };
        self.publish_snapshot_contract(fun, &mut summary);
        let mut up = BTreeSet::new();
        for fact in facts.iter().filter(|fact| fact.owner == fun.owner) {
            match &fact.obligation {
                Obligation::Write(span) => {
                    if let Some(param) = fun.formals.iter().position(|decl| *decl == Some(*span))
                        && fun
                            .declared
                            .parameters
                            .get(param)
                            .is_some_and(|formal| formal.mode != Mode::New)
                    {
                        summary.writes.push(param);
                    }
                }
                Obligation::WriteExisting(span) => {
                    if let Some(param) = fun.formals.iter().position(|decl| *decl == Some(*span)) {
                        summary.writes.push(param);
                    }
                }
                Obligation::Share(span) | Obligation::StoreShare(span) => {
                    if let Some(param) = fun.formals.iter().position(|decl| *decl == Some(*span)) {
                        summary.retained.push(param);
                        if matches!(fact.obligation, Obligation::Share(_)) {
                            summary.independent_retention.push(param);
                        }
                    }
                }
                Obligation::ReadUp(span) => {
                    up.insert(*span);
                }
                Obligation::Invoke(span) => {
                    if let Some(formal) = fun.formals.iter().position(|decl| *decl == Some(*span)) {
                        summary.invoked.push(formal);
                    }
                }
                Obligation::Effect(effect) => {
                    self.record_effect_use(fun, &mut summary, effect, None);
                }
                Obligation::Operation(operation) => {
                    self.record_effect_use(
                        fun,
                        &mut summary,
                        &operation.effect,
                        Some(operation.id),
                    );
                }
                Obligation::Capture => summary.captures = true,
                _ => {}
            }
        }
        summary.writes.sort_unstable();
        summary.writes.dedup();
        summary.retained.sort_unstable();
        summary.retained.dedup();
        summary.independent_retention.sort_unstable();
        summary.invoked.sort_unstable();
        summary.effects.sort();
        summary.effects.dedup();
        summary.effect_uses.sort_unstable();
        summary.effect_uses.dedup();
        summary.normalize_invocations();
        let name = fun.owner;
        let sig = &fun.declared;
        let exercised = |slots: &[usize]| {
            slots.iter().any(|&i| {
                fun.formals
                    .get(i)
                    .and_then(|decl| *decl)
                    .is_some_and(|span| !fun.via.contains(&span))
            })
        };
        for (state, actual) in [
            ("mut", exercised(&summary.writes)),
            ("^mut", exercised(&summary.retained)),
            ("capture", summary.captures),
        ] {
            let declared = sig.state.iter().any(|clause| clause == state);
            if actual && !declared {
                self.error(Code::E0510, name, format!("missing &{state} obligation"));
            } else if !actual && declared && fun.via.is_empty() {
                self.error(Code::E0529, name, format!("unused &{state} obligation"));
            }
        }
        for effect in &summary.effects {
            if !sig
                .effects
                .iter()
                .any(|declared| self.program.effect_covers(declared, effect))
            {
                self.error(Code::E0612, name, format!("unhandled @{effect}"));
            }
        }
        for effect in &sig.effects {
            if !summary
                .effects
                .iter()
                .any(|actual| self.program.effect_covers(effect, actual))
            {
                self.error(
                    Code::E0612,
                    name,
                    format!("declared @{effect} is never exercised"),
                );
            }
        }
        if up.difference(&fun.capture_names).next().is_some() {
            self.error(Code::E0510, name, "missing &up dependency");
        }
        if fun.capture_names.difference(&up).next().is_some() {
            self.error(Code::E0529, name, "unused &up dependency");
        }
        summary
    }

    pub(super) fn storage_contracts(&self, fun: &DefinitionCheck) -> Vec<StorageUpdate> {
        self.describe_storage_updates(&fun.formals, &fun.updates)
    }

    pub(super) fn describe_storage_updates(
        &self,
        formals: &[Option<Span>],
        entries: &BTreeMap<Region, Replacement>,
    ) -> Vec<StorageUpdate> {
        let formal_index = |source| formals.iter().position(|formal| *formal == Some(source));
        let mut updates: Vec<_> = entries
            .iter()
            .filter_map(|(region, update)| {
                let formal = formal_index(region.source)?;
                let mut sources = BTreeSet::new();
                update
                    .value
                    .visit_origins(&mut Vec::new(), &mut |result_path, origin| {
                        if let Some(formal) = formal_index(origin.region.source) {
                            sources.insert(ReturnSource {
                                formal,
                                source_path: origin.region.selection.clone(),
                                result_path: result_path.to_vec(),
                                access: origin.mode,
                            });
                        }
                    });
                Some(StorageUpdate {
                    formal,
                    path: region.selection.clone(),
                    sources: sources.into_iter().collect(),
                    callback_returns: self.callback_return_contracts(formals, &update.value),
                    snapshot_projections: Vec::new(),
                    allocations: Datum::return_allocations(std::slice::from_ref(&update.value)),
                    definite: update.definite,
                    constructs: update.value.requires_new,
                })
            })
            .collect();
        updates.sort_unstable();
        updates
    }
}
