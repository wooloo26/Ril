use super::*;

impl Analyzer<'_> {
    pub(in crate::access::check) fn handlers(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        handlers: &[Handler],
    ) {
        let mut operations = BTreeSet::new();
        let mut installed = std::collections::BTreeMap::new();
        for handler in handlers {
            let span = handler.operation.span;
            let operation = self
                .definition(span)
                .and_then(|id| self.operation(id, span));
            if let Some(operation) = &operation {
                if !operations.insert(operation.clone()) {
                    self.error(Code::E0622, span, "duplicate operation in handler group");
                }
            } else {
                self.error(
                    Code::E0621,
                    span,
                    "handler must target a user effect operation",
                );
            }
            let rhs = self.ast(ctx.file).expr(handler.value);
            let inline = matches!(rhs.value, Expr::Closure { .. });
            let mut value = if inline {
                let mut local = ctx.clone();
                if handler.mode == Mode::New {
                    local.expected = Mode::New;
                }
                self.closure(&local, ledger, handler.value, true)
            } else {
                self.expr(ctx, ledger, handler.value)
            };
            if let Expr::Path(path) = &rhs.value
                && let Some(id) = self.definition(path.span)
            {
                let def = self.program.hir.definition(id);
                if let Some(stmt) = def.stmt
                    && let StmtKind::Function(fun) =
                        &self.ast(def.name.span.file).stmt(stmt).value.kind
                {
                    let bindings: BTreeSet<_> = fun
                        .signature
                        .obligations
                        .state
                        .iter()
                        .filter(|clause| clause.kind == StateKind::Environment)
                        .flat_map(|clause| &clause.bindings)
                        .filter_map(|(_, path)| self.declaration(path.span))
                        .collect();
                    for (index, binding) in bindings.into_iter().enumerate() {
                        if let Some(slot) = ledger.slots.get(&binding) {
                            value
                                .members
                                .insert(Coordinate::Index(index.to_string()), slot.value.clone());
                            value
                                .invocations
                                .entry(fun.name.span)
                                .or_default()
                                .insert(binding, BTreeSet::from([binding]));
                        }
                    }
                }
            }
            if matches!(
                self.ty(rhs.span),
                Ty::Callable(signature) if signature.is_ctl
            ) {
                self.error(
                    Code::E0534,
                    rhs.span,
                    "deep handler arm cannot use a ctl continuation",
                );
            }
            let mut effect_ctx = ctx.clone();
            if !handler.is_ctl {
                effect_ctx.no_ctl = Some(rhs.span);
            }
            self.charge_latent_effects(&effect_ctx, ledger, &value, rhs.span);
            if !inline && let Ty::Callable(signature) = self.ty(rhs.span) {
                for effect in &signature.effects {
                    self.effect(&effect_ctx, ledger, effect, rhs.span);
                }
            }
            self.link_invocation(ctx, &value);
            if ctx.reachable && !ctx.shadow {
                self.check_handler_iteration(ledger, &value, rhs.span, None);
            }
            let capture_mode = value
                .members
                .values()
                .flat_map(Datum::origins)
                .map(|origin| origin.mode)
                .max();
            let held_mode = match handler.mode {
                specified @ (Mode::Ref | Mode::Mut | Mode::Shared) => Some(specified),
                _ => match capture_mode {
                    Some(Access::Shared) => Some(Mode::Shared),
                    Some(Access::Mut) => Some(Mode::Mut),
                    Some(Access::Ref) => Some(Mode::Ref),
                    _ => None,
                },
            };
            if let Some(mode) = held_mode {
                if handler.mode == Mode::Plain
                    && !inline
                    && !value.requires_new
                    && !matches!(&rhs.value, Expr::Path(path) if self.definition(path.span).is_some_and(|id| self.program.hir.definition(id).kind == DefinitionKind::Function))
                {
                    self.error(
                        Code::E0405,
                        rhs.span,
                        "a live handler variable requires an explicit access mode",
                    );
                }
                ledger.holds.push((mode, value.clone()));
            }
            if let Some(operation) = operation {
                installed.insert(operation, value);
            }
        }
        ctx.handlers.extend(installed);
    }

    pub(in crate::access::check) fn closure(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        id: ExprId,
        contextual: bool,
    ) -> Datum {
        let node = self.ast(ctx.file).expr(id);
        let Expr::Closure {
            params,
            body,
            obligations,
        } = &node.value
        else {
            return Datum::default();
        };
        let mut locals = ledger.clone();
        locals.clear_result_obligations();
        locals.clear_linear_obligations();
        locals.clear_array_extents();
        locals.no_continuation = false;
        let mut inner = Context::new(node.span);
        inner.hir_scope = Some(self.hir_scope(ctx));
        inner.in_function = true;
        inner.set_caller_storage(ledger);
        inner.expected = Mode::Infer;
        inner.runtime = ctx.runtime;
        inner.shadow = ctx.shadow;
        inner.reachable = ctx.reachable;
        inner.via.clone_from(&ctx.via);
        inner.member_via = ctx.member_via;
        inner.formals = params
            .iter()
            .map(|param| param.name.as_ref().map(|name| name.span))
            .collect();
        locals.enter_capture_storage(node.span, &inner.formals, |_| true);
        if let Ty::Callable(signature) = self.ty(node.span) {
            let axes = member_axes(signature, &inner.formals);
            inner.member_via |= !axes.is_empty();
            self.register_member_axes(&axes);
            let via = params
                .iter()
                .filter_map(|p| {
                    p.name
                        .as_ref()
                        .filter(|_| p.mode == Mode::Via)
                        .map(|name| name.span)
                })
                .collect();
            self.closure_modes.insert(
                node.span,
                ClosureModes {
                    formals: inner.formals.clone(),
                    via,
                    member_axes: axes,
                    returns: Vec::new(),
                    updates: BTreeMap::new(),
                    storage_flow: None,
                    models_publication: false,
                    captures: Vec::new(),
                },
            );
        }
        if obligations.open_effects || obligations.open_state {
            self.error(
                Code::E0547,
                node.span,
                "closure definition cannot open its annotations",
            );
        }
        if obligations
            .state
            .iter()
            .any(|clause| clause.kind == StateKind::Environment && !clause.bindings.is_empty())
        {
            self.error(Code::E0538, node.span, "closure captures are inferred");
        }
        for p in params {
            if let Some(name) = &p.name {
                self.binding_scopes.insert(name.span, inner.scope);
                if p.mode == Mode::New {
                    inner.new_formals.insert(name.span);
                }
                let mode = Access::from_mode(p.mode);
                let param_ty = self
                    .definition(name.span)
                    .and_then(|id| self.program.bindings.get(&id));
                let is_value = param_ty.is_some_and(|ty| self.program.is_value(ty));
                let is_ctl = param_ty.is_some_and(|ty| self.program.is_ctl_ty(ty));
                if p.mode == Mode::New && (is_value || is_ctl) {
                    self.error(
                        Code::E0411,
                        name.span,
                        "new parameter requires a shared object",
                    );
                }
                let mut value = if is_value {
                    Datum::default()
                } else {
                    let mut datum = Datum::source(name.span, mode, p.mode == Mode::New);
                    if p.mode == Mode::New {
                        datum.requires_new = false;
                    }
                    datum
                };
                if p.mode == Mode::Via {
                    inner.via.insert(name.span);
                    if is_value || is_ctl {
                        self.error(
                            Code::E0550,
                            name.span,
                            "via is redundant on a value-type parameter",
                        );
                    }
                }
                if let Some(ty) = param_ty {
                    value = crate::access::check::results::receive_results(
                        self.program,
                        self.hir_scope(&inner),
                        &mut locals,
                        ty,
                        value,
                        name.span,
                    );
                    if matches!(p.mode, Mode::Plain | Mode::New)
                        && name.value != "_"
                        && self.program.is_must_consume(ty)
                    {
                        locals.record_linear(
                            &mut value,
                            name.span,
                            matches!(ty, Ty::Array(_) | Ty::Map(..)),
                        );
                    }
                }
                value.transform(&mut |origin| {
                    origin.dependencies.insert(name.span.into());
                    origin.enter_formal(inner.owner, p.mode);
                    if matches!(param_ty, Some(Ty::Draft(_))) {
                        origin.confined = Some(node.span);
                        origin.draft = true;
                    }
                });
                locals.slots.insert(
                    name.span,
                    Slot {
                        decl: name.span,
                        variable: false,
                        mode: p.mode,
                        value,
                    },
                );
                let exempt = contextual && name.value.starts_with('_');
                if p.mode == Mode::Via && !exempt {
                    let body_span = self.ast(inner.file).expr(*body).span;
                    let used = name.value != "_"
                        && self.definition(name.span).is_some_and(|def_id| {
                            self.program
                                .hir
                                .references_within(body_span)
                                .any(|(_, id)| id == def_id)
                        });
                    if !used {
                        self.error(
                            Code::E0550,
                            name.span,
                            "via is redundant on an unused closure parameter",
                        );
                    }
                }
                if matches!(p.mode, Mode::Mut | Mode::Shared) && !exempt {
                    self.requirement(
                        &inner,
                        name.span,
                        if p.mode == Mode::Shared {
                            Obligation::Retain(name.span)
                        } else {
                            Obligation::Write(name.span)
                        },
                        "closure parameter authority is unused",
                    );
                }
            }
        }
        let before = self.rules.len();
        let prior_slots = inner.caller_slots.clone();
        let prior_holds = locals.holds.len();
        let mut output =
            self.eval_exit_expr(&mut inner, &mut locals, *body, &prior_slots, prior_holds, 0, true);
        let implicit = self.ty(self.ast(ctx.file).expr(*body).span) != &Ty::Never;
        if inner.reachable && implicit {
            self.run_defers(&mut inner, &mut locals, 0);
            locals.holds.truncate(prior_holds);
            self.try_promote_exit_new(&inner, &locals, &mut output, &prior_slots, prior_holds, true);
            output = locals.snapshot(&output);
            locals.inspect(&output);
            locals.consume_datum_linear(&output);
            self.check_results(&locals, &BTreeSet::new());
            self.check_linear(&locals, &BTreeSet::new());
            self.storage_exit(&inner, &locals);
            if output.returns_call_scoped_writer(Mode::Infer) {
                self.error(
                    Code::E0528,
                    node.span,
                    "a call-scoped writer cannot escape in a return",
                );
            }
        } else {
            output = locals.snapshot(&output);
        }
        let exits = self.storage_exits.remove(&node.span).unwrap_or_default();
        let body_span = self.ast(ctx.file).expr(*body).span;
        if let Some(closure) = self.closure_modes.get_mut(&node.span) {
            let exit = crate::access::check::storage::StorageExit::join(&exits);
            closure.updates = exit.updates;
            closure.storage_flow = exit.flow;
            closure.models_publication = closure
                .updates
                .keys()
                .all(|region| closure.formals.contains(&Some(region.source)));
            closure.returns.clone_from(&inner.return_values);
            if implicit && inner.reachable {
                closure.returns.push(output.clone());
            }
            seal_call_allocations(
                &mut self.callback_results,
                closure
                    .returns
                    .iter_mut()
                    .chain(closure.updates.values_mut().map(|update| &mut update.value))
                    .chain(
                        closure
                            .storage_flow
                            .iter_mut()
                            .flat_map(StorageFlow::values_mut),
                    ),
                body_span,
            );
        }
        if output.origins().any(|origin| origin.draft) {
            self.error(Code::E0607, node.span, "draft escapes update callback");
        } else if output.origins().any(|origin| origin.confined.is_some()) {
            self.error(
                Code::E0604,
                node.span,
                "closure result escapes its confinement",
            );
        }
        let used: BTreeSet<_> = self
            .rules
            .iter()
            .skip(before)
            .filter_map(|rule| {
                if rule.conclusion.owner == inner.owner
                    && let Obligation::ReadUp(span) = rule.conclusion.obligation
                {
                    Some(span)
                } else {
                    None
                }
            })
            .collect();
        if let Some(modes) = self.closure_modes.get_mut(&node.span) {
            modes.captures = used
                .iter()
                .filter_map(|binding| {
                    ledger
                        .slots
                        .get(binding)
                        .map(|slot| (*binding, slot.variable))
                })
                .collect();
        }
        let cap_info: Vec<(Span, Mode)> = used
            .iter()
            .filter_map(|binding| {
                ledger
                    .slots
                    .get(binding)
                    .map(|slot| (*binding, if slot.variable { Mode::Mut } else { slot.mode }))
            })
            .collect();
        if !cap_info.is_empty() {
            self.closure_captures.insert(node.span, cap_info);
        }
        let new = ctx.expected == Mode::New;
        let mut closure = Datum::source(
            node.span,
            if new { Access::Mut } else { Access::Immutable },
            new,
        );
        for root in &mut closure.roots {
            root.snapshot_provider = Some(node.span);
        }
        closure.result_fresh = (implicit || !inner.return_values.is_empty())
            && (!implicit || output.requires_new)
            && inner.return_values.iter().all(|value| value.requires_new);
        for (index, slot) in used
            .iter()
            .filter_map(|span| ledger.slots.get(span))
            .enumerate()
        {
            let mut value = ledger.loop_snapshot(&slot.value).into_owned();
            if value.origins().any(|origin| origin.confined.is_some()) {
                self.error(
                    Code::E0604,
                    node.span,
                    "closure cannot capture a scoped resource",
                );
            }
            if slot.variable {
                let mut cell = Datum::source(slot.decl, Access::Mut, false);
                cell.transform(&mut |origin| {
                    origin.region = Region::allocation(slot.decl);
                    origin.dependencies.insert(slot.decl.into());
                });
                cell.members.insert(Coordinate::Index("0".into()), value);
                value = cell;
            }
            closure
                .members
                .insert(Coordinate::Index(index.to_string()), value);
        }
        for &decl in &used {
            let is_must_consume = self
                .definition(decl)
                .and_then(|id| self.program.bindings.get(&id))
                .is_some_and(|ty| self.program.is_must_consume(ty));
            if is_must_consume {
                self.error(
                    Code::E0625,
                    node.span,
                    "closure cannot capture a must-consume value",
                );
            }
            if ledger.slots.contains_key(&decl)
                && locals.has_direct_revocation(decl)
                && !ledger.has_direct_revocation(decl)
            {
                ledger.revoke(decl.into(), None);
                if ledger
                    .slots
                    .get(&decl)
                    .is_some_and(|slot| !slot.value.results().is_empty())
                {
                    self.error(
                        Code::E0720,
                        node.span,
                        "closure cannot capture an uninspected fallible result",
                    );
                } else if !is_must_consume {
                    self.error(
                        Code::E0548,
                        node.span,
                        "closure cannot consume a captured binding",
                    );
                }
            }
        }
        for rule in self
            .rules
            .iter()
            .skip(before)
            .filter(|rule| rule.conclusion.owner == inner.owner)
        {
            match &rule.conclusion.obligation {
                Obligation::Effect(effect) => {
                    closure.latent_effects.insert(effect.clone());
                }
                Obligation::Operation(operation) => {
                    closure
                        .latent_operations
                        .insert((operation.id, operation.effect.clone()));
                }
                Obligation::StatefulHandler => {
                    closure.live_callable_state = true;
                }
                Obligation::CtlHandler => {
                    closure.uses_ctl_handler = true;
                }
                _ => {}
            }
        }
        if !closure.members.is_empty() {
            closure.environments.insert(node.span);
            for root in &mut closure.roots {
                root.region = Region::allocation(node.span);
            }
            let bindings = used
                .into_iter()
                .map(|decl| {
                    let sources = std::iter::once(decl)
                        .chain(
                            ledger
                                .slots
                                .get(&decl)
                                .into_iter()
                                .flat_map(|slot| slot.value.root_dependencies()),
                        )
                        .collect();
                    (decl, sources)
                })
                .collect();
            closure.invocations.insert(inner.owner, bindings);
        }
        closure
    }
}
