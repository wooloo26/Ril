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
        ctx.return_guards = fun.signature.guards.clone();
        let capture_modes: BTreeMap<_, _> = fun
            .signature
            .obligations
            .state
            .iter()
            .filter(|clause| clause.kind == StateKind::Environment)
            .flat_map(|clause| &clause.bindings)
            .filter_map(|(storage, path)| {
                if let Some(def_id) = self.definition(path.span)
                    && let Some(ty) = self.program.bindings.get(&def_id)
                    && self.program.is_must_consume(ty)
                {
                    self.error(
                        Code::E0625,
                        path.span,
                        "named local function cannot capture a must-consume value",
                    );
                }
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
        ledger.clear_linear_obligations();
        ledger.clear_array_extents();
        ledger.inspected.clear();
        ledger.reset_revocations();
        ledger.no_continuation = false;
        ledger.iteration.clear();
        ledger.holds.clear();
        fn contains_open_effect_callable(ty: &Ty) -> bool {
            match ty {
                Ty::Callable(c) => {
                    c.open_effects
                        || c.direct_open_effects
                        || c.parameters
                            .iter()
                            .any(|p| contains_open_effect_callable(&p.ty))
                        || contains_open_effect_callable(&c.result)
                }
                Ty::Tuple(items) => items.iter().any(|m| contains_open_effect_callable(&m.ty)),
                Ty::Record(fields, _) => fields
                    .iter()
                    .any(|(_, m)| contains_open_effect_callable(&m.ty)),
                Ty::Array(m) => contains_open_effect_callable(&m.ty),
                Ty::Map(k, v) => {
                    contains_open_effect_callable(k) || contains_open_effect_callable(&v.ty)
                }
                Ty::Draft(inner) => contains_open_effect_callable(inner),
                Ty::Adt(adt) => adt.arguments.iter().any(|arg| match arg {
                    crate::ty::GenericValue::Type(t) => contains_open_effect_callable(t),
                    _ => false,
                }),
                _ => false,
            }
        }
        let has_open_effect_param = callable
            .parameters
            .iter()
            .any(|p| contains_open_effect_callable(&p.ty));
        if callable.open_state
            || ((callable.open_effects || callable.direct_open_effects) && !has_open_effect_param)
        {
            self.error(
                Code::E0547,
                ctx.owner,
                "named definitions require closed state sets and open '@' requires an open callback parameter",
            );
        }
        let body_span = self.ast(ctx.file).expr(body).span;
        for (ast_param, param) in fun.signature.params.iter().zip(&callable.parameters) {
            let span = ast_param.name.as_ref().map_or(ctx.owner, |name| name.span);
            self.binding_scopes.insert(span, ctx.scope);
            if param.mode == Mode::Via {
                ctx.via.insert(span);
                if self.program.is_value(&param.ty) || self.program.is_linear_root(&param.ty) {
                    self.error(
                        Code::E0550,
                        span,
                        "via is invalid on a value-type or linear parameter",
                    );
                }
            }
            if param.mode == Mode::Via || param.ty.has_via_members() {
                let used = ast_param
                    .name
                    .as_ref()
                    .filter(|name| name.value != "_")
                    .and_then(|name| self.definition(name.span))
                    .is_some_and(|def_id| {
                        self.program
                            .hir
                            .references_within(body_span)
                            .any(|(_, id)| id == def_id)
                    });
                if !used {
                    self.error(Code::E0550, span, "via is redundant on an unused parameter");
                }
            }
            if param.mode == Mode::New
                && (self.program.is_value(&param.ty) || self.program.is_linear_root(&param.ty))
            {
                self.error(
                    Code::E0411,
                    span,
                    "new parameter requires a non-linear shared object",
                );
            }
            if param.mode == Mode::New {
                ctx.new_formals.insert(span);
            }
            let mut value =
                if self.program.is_value(&param.ty) && !self.program.is_must_consume(&param.ty) {
                    Datum::default()
                } else {
                    let mut datum =
                        Datum::source(span, Access::from_mode(param.mode), param.mode == Mode::New);
                    if param.mode == Mode::New {
                        datum.requires_new = false;
                    }
                    datum
                };
            value.transform(&mut |origin| {
                origin.dependencies.insert(span.into());
                origin.enter_formal(ctx.owner, param.mode);
                if matches!(param.ty, Ty::Draft(_)) {
                    origin.draft = true;
                    origin.confined = Some(ctx.scope);
                }
            });
            value = results::receive_results(
                self.program,
                self.hir_scope(&ctx),
                &mut ledger,
                &param.ty,
                value,
                span,
            );
            if matches!(param.mode, Mode::Plain | Mode::New)
                && self.program.is_must_consume(&param.ty)
            {
                ledger.record_linear(
                    &mut value,
                    span,
                    matches!(param.ty, Ty::Array(_) | Ty::Map(..)),
                );
            }
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
                    "mut parameter requires reachable write or forwarding",
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
        for ast_param in &fun.signature.params {
            if !ast_param.is_meta && !ast_param.guards.is_empty() {
                self.check_guard_args(&mut ctx, &mut ledger, &ast_param.guards);
            }
        }
        let prior_slots = ctx.caller_slots.clone();
        let prior_holds = ledger.holds.len();
        let mut value = self.eval_exit_expr(
            &mut ctx,
            &mut ledger,
            body,
            &prior_slots,
            prior_holds,
            0,
            true,
        );
        let body_span = self.ast(ctx.file).expr(body).span;
        if ctx.reachable && !ledger.no_continuation && self.ty(body_span) != &Ty::Never {
            self.run_defers(&mut ctx, &mut ledger, 0);
            self.check_live(
                &ctx,
                &ledger,
                &value,
                body_span,
                "returned value was consumed by defer",
            );
            ledger.holds.truncate(prior_holds);
            self.try_promote_exit_new(&ctx, &ledger, &mut value, &prior_slots, prior_holds, true);
            self.returned(&mut ctx, &mut ledger, value, body_span);
            self.check_results(&ledger, &BTreeSet::new());
            self.check_linear(&ledger, &BTreeSet::new());
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
        let (has_holes, has_pruned_meta) = self.scan_body_flags(ctx.file, body);
        let outer_slots = outer
            .slots
            .iter()
            .map(|(&decl, slot)| (decl, (slot.variable, slot.mode)))
            .collect();
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
            outer_slots,
            is_meta: fun.is_meta,
            has_holes,
            has_pruned_meta,
        });
    }

    pub(super) fn check_guard_args(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        guards: &[ExprId],
    ) {
        if !ctx.runtime || ctx.shadow || !ctx.reachable {
            return;
        }
        for &guard in guards {
            if self.program.hir.is_static_proof_guard(ctx.file, guard) {
                continue;
            }
            let mut node = self.ast(ctx.file).expr(guard);
            if let Expr::Unary { op, value } = &node.value
                && op.value == "ref"
            {
                node = self.ast(ctx.file).expr(*value);
            }
            if let Expr::Call { args, .. } = &node.value {
                let arg_exprs: Vec<ExprId> = args.iter().map(|a| a.value).collect();
                for arg_expr in arg_exprs {
                    let _ = self.expr(ctx, ledger, arg_expr);
                }
            }
        }
    }

    pub(super) fn check_return_static_proof_liveness(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        guards: &[ExprId],
    ) {
        if !ctx.runtime || ctx.shadow || !ctx.reachable {
            return;
        }
        for &guard in guards {
            if !self.program.hir.is_static_proof_guard(ctx.file, guard) {
                continue;
            }
            let span = self.ast(ctx.file).expr(guard).span;
            for (ref_span, def_id) in self.program.hir.references_within(span) {
                let def = self.program.hir.definition(def_id);
                if def.kind == ril_hir::DefinitionKind::Local
                    && let Some(slot) = ledger.slots.get(&def.name.span)
                {
                    let slot_val = slot.value.clone();
                    self.check_live(
                        ctx,
                        ledger,
                        &slot_val,
                        ref_span,
                        "static return proof references a consumed parameter",
                    );
                }
            }
        }
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
            mode_calls: self
                .mode_call_summaries
                .remove(&fun.owner)
                .into_iter()
                .flatten()
                .collect(),
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
        let mut used_effect_vars = BTreeSet::new();
        let mut used_open_effect = false;
        let mut used_direct_open_effect = false;
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
                Obligation::EffectVar(var) => {
                    used_effect_vars.insert(*var);
                }
                Obligation::OpenEffect => {
                    used_open_effect = true;
                }
                Obligation::DirectOpenEffect => {
                    used_direct_open_effect = true;
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
                    Code::E0626,
                    name,
                    format!("declared @{effect} is never exercised"),
                );
            }
        }
        for &var in &used_effect_vars {
            if !sig.effect_vars.contains(&var) {
                let var_name = &self.program.hir.definition(var).name.value;
                self.error(Code::E0612, name, format!("unhandled @{var_name}"));
            }
        }
        for &var in &sig.effect_vars {
            if !used_effect_vars.contains(&var) {
                let var_name = &self.program.hir.definition(var).name.value;
                self.error(
                    Code::E0626,
                    name,
                    format!("declared @{var_name} is never exercised"),
                );
            }
        }
        if used_open_effect {
            if sig.direct_open_effects && !sig.open_effects {
                self.error(
                    Code::E0616,
                    name,
                    "open '@' callback may perform ctl and cannot be covered by '@fn'",
                );
            } else if !sig.open_effects {
                self.error(
                    Code::E0612,
                    name,
                    "missing '@' obligation for open-effect callback",
                );
            }
        }
        if used_direct_open_effect && !sig.open_effects && !sig.direct_open_effects {
            self.error(
                Code::E0612,
                name,
                "missing '@fn' obligation for direct open-effect callback",
            );
        }
        if sig.open_effects && !used_open_effect && !used_direct_open_effect {
            self.error(Code::E0626, name, "declared '@' is never exercised");
        }
        if sig.direct_open_effects && !used_direct_open_effect {
            self.error(Code::E0626, name, "declared '@fn' is never exercised");
        }
        if up.difference(&fun.capture_names).next().is_some() {
            self.error(Code::E0510, name, "missing &up dependency");
        }
        if fun.capture_names.difference(&up).next().is_some() {
            self.error(Code::E0529, name, "unused &up dependency");
        }
        if let Some(syntax) = self.function_syntax(fun.id)
            && let Some(body) = syntax.body
            && !syntax.generics.is_empty()
        {
            let (drop_set, dup_set, suspend_set) =
                self.compute_generic_linearity(syntax, body, &summary);
            summary.forbids_linear_drop = drop_set;
            summary.forbids_linear_dup = dup_set;
            summary.forbids_linear_suspend = suspend_set;
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

    fn compute_generic_linearity(
        &self,
        fun: &Function,
        body: ExprId,
        summary: &Summary,
    ) -> (Vec<usize>, Vec<usize>, Vec<usize>) {
        let file = fun.name.span.file;
        let ast = self.ast(file);
        let generic_index: BTreeMap<DefinitionId, usize> = fun
            .generics
            .iter()
            .enumerate()
            .filter_map(|(idx, g)| self.definition(g.name.span).map(|id| (id, idx)))
            .collect();
        if generic_index.is_empty() {
            return (Vec::new(), Vec::new(), Vec::new());
        }
        let mut forbids_drop = BTreeSet::new();
        let mut forbids_dup = BTreeSet::new();
        let mut forbids_suspend = BTreeSet::new();

        let mark_ty = |ty: &Ty, out: &mut BTreeSet<usize>| {
            let mut params = BTreeSet::new();
            self.program.collect_type_params(ty, &mut params);
            for pid in params {
                if let Some(&idx) = generic_index.get(&pid) {
                    out.insert(idx);
                }
            }
        };

        let mut param_defs: BTreeMap<DefinitionId, (Mode, BTreeSet<usize>)> = BTreeMap::new();
        for p in &fun.signature.params {
            if p.is_meta {
                continue;
            }
            if let Some(name) = &p.name
                && let Some(def_id) = self.definition(name.span)
                && let Some(ty) = self.program.bindings.get(&def_id)
            {
                let mut indices = BTreeSet::new();
                mark_ty(ty, &mut indices);
                if !indices.is_empty() {
                    if name.value == "_" {
                        forbids_drop.extend(indices.iter().copied());
                    } else {
                        param_defs.insert(def_id, (p.mode, indices));
                    }
                }
            }
        }

        fn walk_pattern(
            this: &Analyzer<'_>,
            ast: &Ast,
            pat: PatternId,
            mark_ty: &impl Fn(&Ty, &mut BTreeSet<usize>),
            forbids_drop: &mut BTreeSet<usize>,
            local_generics: &mut BTreeMap<DefinitionId, BTreeSet<usize>>,
        ) {
            let node = ast.pattern(pat);
            match &node.value {
                Pattern::Wildcard => {
                    mark_ty(this.ty(node.span), forbids_drop);
                }
                Pattern::Binding(_, name) => {
                    if let Some(id) = this.definition(name.span)
                        && let Some(ty) = this.program.bindings.get(&id)
                    {
                        let mut set = BTreeSet::new();
                        mark_ty(ty, &mut set);
                        if !set.is_empty() {
                            local_generics.insert(id, set);
                        }
                    }
                }
                Pattern::Tuple(items) | Pattern::Wrap(_, items) | Pattern::Or(items) => {
                    for &item in items {
                        walk_pattern(this, ast, item, mark_ty, forbids_drop, local_generics);
                    }
                }
                Pattern::Constructor(_, Some(items)) => {
                    for &item in items {
                        walk_pattern(this, ast, item, mark_ty, forbids_drop, local_generics);
                    }
                }
                Pattern::Slice { elements, .. } => {
                    for &item in elements {
                        walk_pattern(this, ast, item, mark_ty, forbids_drop, local_generics);
                    }
                }
                Pattern::Record { fields, .. } => {
                    for field in fields {
                        if let Some(p) = field.pattern {
                            walk_pattern(this, ast, p, mark_ty, forbids_drop, local_generics);
                        } else if let Some(id) = this.definition(field.name.span)
                            && let Some(ty) = this.program.bindings.get(&id)
                        {
                            let mut set = BTreeSet::new();
                            mark_ty(ty, &mut set);
                            if !set.is_empty() {
                                local_generics.insert(id, set);
                            }
                        }
                    }
                }
                Pattern::Subset {
                    binding: Some(p), ..
                } => walk_pattern(this, ast, *p, mark_ty, forbids_drop, local_generics),
                _ => {}
            }
        }

        fn merge_sum(dst: &mut BTreeMap<DefinitionId, usize>, src: BTreeMap<DefinitionId, usize>) {
            for (k, v) in src {
                *dst.entry(k).or_insert(0) += v;
            }
        }
        fn merge_max(dst: &mut BTreeMap<DefinitionId, usize>, src: BTreeMap<DefinitionId, usize>) {
            for (k, v) in src {
                let entry = dst.entry(k).or_insert(0);
                *entry = (*entry).max(v);
            }
        }

        #[allow(clippy::too_many_arguments)]
        fn walk_expr(
            this: &Analyzer<'_>,
            ast: &Ast,
            id: ExprId,
            mark_ty: &impl Fn(&Ty, &mut BTreeSet<usize>),
            forbids_drop: &mut BTreeSet<usize>,
            forbids_dup: &mut BTreeSet<usize>,
            local_generics: &mut BTreeMap<DefinitionId, BTreeSet<usize>>,
        ) -> BTreeMap<DefinitionId, usize> {
            let node = ast.expr(id);
            let mut reads = BTreeMap::new();
            match &node.value {
                Expr::Path(path) => {
                    if let Some(def_id) = this.definition(path.span) {
                        *reads.entry(def_id).or_insert(0) += 1;
                    }
                }
                Expr::Unary { value, .. } | Expr::Cast { value, .. } => {
                    reads = walk_expr(
                        this,
                        ast,
                        *value,
                        mark_ty,
                        forbids_drop,
                        forbids_dup,
                        local_generics,
                    );
                }
                Expr::Binary { op, left, right } => {
                    if op.value == "=" && matches!(ast.expr(*left).value, Expr::Index { .. }) {
                        mark_ty(this.ty(ast.expr(*left).span), forbids_drop);
                    }
                    merge_sum(
                        &mut reads,
                        walk_expr(
                            this,
                            ast,
                            *left,
                            mark_ty,
                            forbids_drop,
                            forbids_dup,
                            local_generics,
                        ),
                    );
                    merge_sum(
                        &mut reads,
                        walk_expr(
                            this,
                            ast,
                            *right,
                            mark_ty,
                            forbids_drop,
                            forbids_dup,
                            local_generics,
                        ),
                    );
                }
                Expr::Block { statements, .. } | Expr::With { statements, .. } => {
                    for (i, &stmt_id) in statements.iter().enumerate() {
                        let is_tail = i + 1 == statements.len();
                        let stmt = ast.stmt(stmt_id);
                        match &stmt.value.kind {
                            StmtKind::Binding {
                                pattern,
                                value: Some(expr),
                                fallback,
                                ..
                            } => {
                                merge_sum(
                                    &mut reads,
                                    walk_expr(
                                        this,
                                        ast,
                                        *expr,
                                        mark_ty,
                                        forbids_drop,
                                        forbids_dup,
                                        local_generics,
                                    ),
                                );
                                walk_pattern(
                                    this,
                                    ast,
                                    *pattern,
                                    mark_ty,
                                    forbids_drop,
                                    local_generics,
                                );
                                if let Some(fb) = fallback {
                                    merge_sum(
                                        &mut reads,
                                        walk_expr(
                                            this,
                                            ast,
                                            *fb,
                                            mark_ty,
                                            forbids_drop,
                                            forbids_dup,
                                            local_generics,
                                        ),
                                    );
                                }
                            }
                            StmtKind::Expr(expr) => {
                                merge_sum(
                                    &mut reads,
                                    walk_expr(
                                        this,
                                        ast,
                                        *expr,
                                        mark_ty,
                                        forbids_drop,
                                        forbids_dup,
                                        local_generics,
                                    ),
                                );
                                if !is_tail {
                                    mark_ty(this.ty(ast.expr(*expr).span), forbids_drop);
                                }
                            }
                            StmtKind::Defer(expr) => {
                                merge_sum(
                                    &mut reads,
                                    walk_expr(
                                        this,
                                        ast,
                                        *expr,
                                        mark_ty,
                                        forbids_drop,
                                        forbids_dup,
                                        local_generics,
                                    ),
                                );
                            }
                            _ => {}
                        }
                    }
                }
                Expr::If {
                    condition, yes, no, ..
                } => {
                    match condition {
                        Condition::Expr(e) => {
                            merge_sum(
                                &mut reads,
                                walk_expr(
                                    this,
                                    ast,
                                    *e,
                                    mark_ty,
                                    forbids_drop,
                                    forbids_dup,
                                    local_generics,
                                ),
                            );
                        }
                        Condition::Binding { pattern, value, .. } => {
                            merge_sum(
                                &mut reads,
                                walk_expr(
                                    this,
                                    ast,
                                    *value,
                                    mark_ty,
                                    forbids_drop,
                                    forbids_dup,
                                    local_generics,
                                ),
                            );
                            walk_pattern(
                                this,
                                ast,
                                *pattern,
                                mark_ty,
                                forbids_drop,
                                local_generics,
                            );
                        }
                    }
                    let mut branch_reads = walk_expr(
                        this,
                        ast,
                        *yes,
                        mark_ty,
                        forbids_drop,
                        forbids_dup,
                        local_generics,
                    );
                    let yes_span = ast.expr(*yes).span;
                    if let Some(no_expr) = no {
                        let no_reads = walk_expr(
                            this,
                            ast,
                            *no_expr,
                            mark_ty,
                            forbids_drop,
                            forbids_dup,
                            local_generics,
                        );
                        let no_span = ast.expr(*no_expr).span;
                        for &def_id in branch_reads.keys() {
                            if !no_reads.contains_key(&def_id) {
                                let dspan = this.program.hir.definition(def_id).name.span;
                                let inside = dspan.file == yes_span.file
                                    && dspan.start >= yes_span.start
                                    && dspan.end <= yes_span.end;
                                if !inside && let Some(ty) = this.program.bindings.get(&def_id) {
                                    mark_ty(ty, forbids_drop);
                                }
                            }
                        }
                        for &def_id in no_reads.keys() {
                            if !branch_reads.contains_key(&def_id) {
                                let dspan = this.program.hir.definition(def_id).name.span;
                                let inside = dspan.file == no_span.file
                                    && dspan.start >= no_span.start
                                    && dspan.end <= no_span.end;
                                if !inside && let Some(ty) = this.program.bindings.get(&def_id) {
                                    mark_ty(ty, forbids_drop);
                                }
                            }
                        }
                        merge_max(&mut branch_reads, no_reads);
                    } else {
                        for &def_id in branch_reads.keys() {
                            let dspan = this.program.hir.definition(def_id).name.span;
                            let inside = dspan.file == yes_span.file
                                && dspan.start >= yes_span.start
                                && dspan.end <= yes_span.end;
                            if !inside && let Some(ty) = this.program.bindings.get(&def_id) {
                                mark_ty(ty, forbids_drop);
                            }
                        }
                    }
                    merge_sum(&mut reads, branch_reads);
                }
                Expr::While { condition, body } => {
                    let mut loop_reads = BTreeMap::new();
                    match condition {
                        Condition::Expr(e) => {
                            merge_sum(
                                &mut loop_reads,
                                walk_expr(
                                    this,
                                    ast,
                                    *e,
                                    mark_ty,
                                    forbids_drop,
                                    forbids_dup,
                                    local_generics,
                                ),
                            );
                        }
                        Condition::Binding { pattern, value, .. } => {
                            merge_sum(
                                &mut loop_reads,
                                walk_expr(
                                    this,
                                    ast,
                                    *value,
                                    mark_ty,
                                    forbids_drop,
                                    forbids_dup,
                                    local_generics,
                                ),
                            );
                            walk_pattern(
                                this,
                                ast,
                                *pattern,
                                mark_ty,
                                forbids_drop,
                                local_generics,
                            );
                        }
                    }
                    merge_sum(
                        &mut loop_reads,
                        walk_expr(
                            this,
                            ast,
                            *body,
                            mark_ty,
                            forbids_drop,
                            forbids_dup,
                            local_generics,
                        ),
                    );
                    for &def_id in loop_reads.keys() {
                        let dspan = this.program.hir.definition(def_id).name.span;
                        let inside = dspan.file == node.span.file
                            && dspan.start >= node.span.start
                            && dspan.end <= node.span.end;
                        if !inside && let Some(ty) = this.program.bindings.get(&def_id) {
                            mark_ty(ty, forbids_drop);
                            mark_ty(ty, forbids_dup);
                        }
                    }
                    merge_sum(&mut reads, loop_reads);
                }
                Expr::For {
                    iterable,
                    pattern,
                    body,
                    ..
                } => {
                    match this.ty(ast.expr(*iterable).span) {
                        Ty::Array(item) => mark_ty(&item.ty, forbids_dup),
                        Ty::Map(_, item) => mark_ty(&item.ty, forbids_dup),
                        _ => {}
                    }
                    merge_sum(
                        &mut reads,
                        walk_expr(
                            this,
                            ast,
                            *iterable,
                            mark_ty,
                            forbids_drop,
                            forbids_dup,
                            local_generics,
                        ),
                    );
                    walk_pattern(this, ast, *pattern, mark_ty, forbids_drop, local_generics);
                    merge_sum(
                        &mut reads,
                        walk_expr(
                            this,
                            ast,
                            *body,
                            mark_ty,
                            forbids_drop,
                            forbids_dup,
                            local_generics,
                        ),
                    );
                }
                Expr::Match { value, arms, .. } => {
                    merge_sum(
                        &mut reads,
                        walk_expr(
                            this,
                            ast,
                            *value,
                            mark_ty,
                            forbids_drop,
                            forbids_dup,
                            local_generics,
                        ),
                    );
                    let mut arm_reads = BTreeMap::new();
                    for arm in arms {
                        walk_pattern(
                            this,
                            ast,
                            arm.pattern,
                            mark_ty,
                            forbids_drop,
                            local_generics,
                        );
                        let mut one = BTreeMap::new();
                        if let Some(g) = arm.guard {
                            merge_sum(
                                &mut one,
                                walk_expr(
                                    this,
                                    ast,
                                    g,
                                    mark_ty,
                                    forbids_drop,
                                    forbids_dup,
                                    local_generics,
                                ),
                            );
                        }
                        merge_sum(
                            &mut one,
                            walk_expr(
                                this,
                                ast,
                                arm.body,
                                mark_ty,
                                forbids_drop,
                                forbids_dup,
                                local_generics,
                            ),
                        );
                        merge_max(&mut arm_reads, one);
                    }
                    merge_sum(&mut reads, arm_reads);
                }
                Expr::Member { base, .. } => {
                    mark_ty(this.ty(node.span), forbids_dup);
                    merge_sum(
                        &mut reads,
                        walk_expr(
                            this,
                            ast,
                            *base,
                            mark_ty,
                            forbids_drop,
                            forbids_dup,
                            local_generics,
                        ),
                    );
                }
                Expr::Index { base, index, .. } => {
                    match this.ty(ast.expr(*base).span) {
                        Ty::Array(item) => mark_ty(&item.ty, forbids_dup),
                        Ty::Map(_, item) => mark_ty(&item.ty, forbids_dup),
                        _ => mark_ty(this.ty(node.span), forbids_dup),
                    }
                    merge_sum(
                        &mut reads,
                        walk_expr(
                            this,
                            ast,
                            *base,
                            mark_ty,
                            forbids_drop,
                            forbids_dup,
                            local_generics,
                        ),
                    );
                    merge_sum(
                        &mut reads,
                        walk_expr(
                            this,
                            ast,
                            *index,
                            mark_ty,
                            forbids_drop,
                            forbids_dup,
                            local_generics,
                        ),
                    );
                }
                Expr::Tuple(items) | Expr::Array(items) => {
                    for &item in items {
                        merge_sum(
                            &mut reads,
                            walk_expr(
                                this,
                                ast,
                                item,
                                mark_ty,
                                forbids_drop,
                                forbids_dup,
                                local_generics,
                            ),
                        );
                    }
                }
                Expr::Record { fields, .. } => {
                    for f in fields {
                        if let Some(expr) = f.value {
                            merge_sum(
                                &mut reads,
                                walk_expr(
                                    this,
                                    ast,
                                    expr,
                                    mark_ty,
                                    forbids_drop,
                                    forbids_dup,
                                    local_generics,
                                ),
                            );
                        } else if let Some(def_id) = this.definition(f.name.span) {
                            *reads.entry(def_id).or_insert(0) += 1;
                        }
                    }
                }
                Expr::Map(entries) => {
                    for &(k, v) in entries {
                        merge_sum(
                            &mut reads,
                            walk_expr(
                                this,
                                ast,
                                k,
                                mark_ty,
                                forbids_drop,
                                forbids_dup,
                                local_generics,
                            ),
                        );
                        merge_sum(
                            &mut reads,
                            walk_expr(
                                this,
                                ast,
                                v,
                                mark_ty,
                                forbids_drop,
                                forbids_dup,
                                local_generics,
                            ),
                        );
                    }
                }
                Expr::Call { callee, args } => {
                    if let Expr::Path(path) = &ast.expr(*callee).value
                        && let Some(def_id) = this.definition(path.span)
                        && this.program.hir.primitive_module(def_id) == Some("Map")
                        && this.program.hir.definition(def_id).name.value == "insert"
                        && let Some(val_arg) = args.get(2)
                    {
                        mark_ty(this.ty(ast.expr(val_arg.value).span), forbids_drop);
                    }
                    merge_sum(
                        &mut reads,
                        walk_expr(
                            this,
                            ast,
                            *callee,
                            mark_ty,
                            forbids_drop,
                            forbids_dup,
                            local_generics,
                        ),
                    );
                    for arg in args {
                        merge_sum(
                            &mut reads,
                            walk_expr(
                                this,
                                ast,
                                arg.value,
                                mark_ty,
                                forbids_drop,
                                forbids_dup,
                                local_generics,
                            ),
                        );
                    }
                }
                Expr::Wrap { args, .. } => {
                    for arg in args {
                        merge_sum(
                            &mut reads,
                            walk_expr(
                                this,
                                ast,
                                arg.value,
                                mark_ty,
                                forbids_drop,
                                forbids_dup,
                                local_generics,
                            ),
                        );
                    }
                }
                Expr::Pipeline { value, target, .. } => {
                    merge_sum(
                        &mut reads,
                        walk_expr(
                            this,
                            ast,
                            *value,
                            mark_ty,
                            forbids_drop,
                            forbids_dup,
                            local_generics,
                        ),
                    );
                    merge_sum(
                        &mut reads,
                        walk_expr(
                            this,
                            ast,
                            *target,
                            mark_ty,
                            forbids_drop,
                            forbids_dup,
                            local_generics,
                        ),
                    );
                }
                Expr::Transfer {
                    value: Some(expr), ..
                } => {
                    merge_sum(
                        &mut reads,
                        walk_expr(
                            this,
                            ast,
                            *expr,
                            mark_ty,
                            forbids_drop,
                            forbids_dup,
                            local_generics,
                        ),
                    );
                }
                Expr::Closure { body, .. } => {
                    let body_span = ast.expr(*body).span;
                    for (_, ref_id) in this.program.hir.references_within(body_span) {
                        let def = this.program.hir.definition(ref_id);
                        if def.kind == DefinitionKind::Local
                            && (def.name.span.start < node.span.start
                                || def.name.span.end > node.span.end)
                            && let Some(ty) = this.program.bindings.get(&ref_id)
                        {
                            mark_ty(ty, forbids_dup);
                        }
                    }
                }
                _ => {}
            }
            reads
        }

        let mut local_generics = BTreeMap::new();
        let reads = walk_expr(
            self,
            ast,
            body,
            &mark_ty,
            &mut forbids_drop,
            &mut forbids_dup,
            &mut local_generics,
        );
        for (def_id, (mode, indices)) in &param_defs {
            let count = reads.get(def_id).copied().unwrap_or(0);
            if matches!(mode, Mode::Plain | Mode::New | Mode::Via) {
                if count == 0 {
                    forbids_drop.extend(indices.iter().copied());
                } else if count > 1 {
                    forbids_dup.extend(indices.iter().copied());
                }
            }
        }
        for (def_id, indices) in &local_generics {
            let count = reads.get(def_id).copied().unwrap_or(0);
            if count > 1 {
                forbids_dup.extend(indices.iter().copied());
            }
        }
        let has_ctl = summary
            .effects
            .iter()
            .any(|eff| self.program.effect_has_ctl(eff));
        if has_ctl {
            for (mode, indices) in param_defs.values() {
                if matches!(mode, Mode::Plain | Mode::New) {
                    forbids_suspend.extend(indices.iter().copied());
                }
            }
        }
        (
            forbids_drop.into_iter().collect(),
            forbids_dup.into_iter().collect(),
            forbids_suspend.into_iter().collect(),
        )
    }

    pub(super) fn solve_fix_effect_closure(
        &self,
        base_facts: &BTreeSet<Fact>,
    ) -> (Vec<Rule<Fact>>, BTreeSet<Fact>, BTreeMap<Fact, usize>) {
        let mut fix_rules = self.rules.clone();
        let mut distinct_effects = BTreeSet::new();
        let mut distinct_ops = BTreeSet::new();
        for fact in base_facts {
            match &fact.obligation {
                Obligation::Effect(effect) => {
                    distinct_effects.insert(effect.clone());
                }
                Obligation::Operation(op) => {
                    distinct_ops.insert(op.clone());
                }
                _ => {}
            }
        }
        for edge in &self.call_edges {
            for effect in &distinct_effects {
                let ops = self.effect_operations(effect);
                let handled = !ops.is_empty() && ops.iter().all(|op| edge.handled_ops.contains(op));
                if !handled {
                    fix_rules.push(Rule {
                        premises: vec![Fact {
                            owner: edge.callee_owner,
                            obligation: Obligation::Effect(effect.clone()),
                        }],
                        conclusion: Fact {
                            owner: edge.caller_owner,
                            obligation: Obligation::Effect(effect.clone()),
                        },
                    });
                }
            }
            for op in &distinct_ops {
                if !edge.handled_ops.contains(op) {
                    fix_rules.push(Rule {
                        premises: vec![Fact {
                            owner: edge.callee_owner,
                            obligation: Obligation::Operation(op.clone()),
                        }],
                        conclusion: Fact {
                            owner: edge.caller_owner,
                            obligation: Obligation::Operation(op.clone()),
                        },
                    });
                }
            }
        }
        let (fix_facts, derived_by) = horn::solve_with_witnesses(&fix_rules);
        (fix_rules, fix_facts, derived_by)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn build_inferred_signature(
        &self,
        fun: &DefinitionCheck,
        summary: &Summary,
        base_facts: &BTreeSet<Fact>,
        fix_rules: &[Rule<Fact>],
        fix_facts: &BTreeSet<Fact>,
        derived_by: &BTreeMap<Fact, usize>,
        owner_names: &BTreeMap<Span, String>,
    ) -> crate::access::InferredSignature {
        let def = self.program.hir.definition(fun.id);
        let is_local_where = !def
            .stmt
            .is_some_and(|stmt| self.is_top_level_stmt(fun.owner.file, stmt));
        let is_main = !is_local_where
            && def.name.value == "main"
            && self.program.hir.file(fun.owner.file).kind
                == ril_syntax::parser::FileKind::Executable;

        let mut effect_fact_map: BTreeMap<String, Vec<Fact>> = BTreeMap::new();
        for fact in fix_facts.iter().filter(|f| f.owner == fun.owner) {
            match &fact.obligation {
                Obligation::Effect(effect) => {
                    effect_fact_map
                        .entry(effect.clone())
                        .or_default()
                        .push(fact.clone());
                }
                Obligation::Operation(op) => {
                    effect_fact_map
                        .entry(op.effect.clone())
                        .or_default()
                        .push(fact.clone());
                }
                _ => {}
            }
        }
        let all_effects: Vec<String> = effect_fact_map.keys().cloned().collect();
        let mut effects = Vec::new();
        for eff in &all_effects {
            let covered_by_other = all_effects
                .iter()
                .any(|other| other != eff && self.program.effect_covers(other, eff));
            if !covered_by_other {
                effects.push(eff.clone());
            }
        }

        let mut effect_causes = BTreeMap::new();
        for eff in &effects {
            if let Some(candidate_facts) = effect_fact_map.get(eff) {
                let mut best_chain: Option<Vec<String>> = None;
                for fact in candidate_facts {
                    let chain =
                        Self::extract_causal_chain(fact, fix_rules, derived_by, owner_names);
                    if best_chain
                        .as_ref()
                        .is_none_or(|cur| chain.len() < cur.len())
                    {
                        best_chain = Some(chain);
                    }
                }
                if let Some(chain) = best_chain {
                    effect_causes.insert(eff.clone(), chain);
                }
            }
        }

        let exercised = |slots: &[usize]| {
            slots.iter().any(|&i| {
                fun.formals
                    .get(i)
                    .and_then(|decl| *decl)
                    .is_some_and(|span| !fun.via.contains(&span))
            })
        };
        let needs_mut = exercised(&summary.writes);
        let needs_shared_mut = exercised(&summary.retained);
        let needs_capture = summary.captures;

        let mut up_spans = BTreeSet::new();
        let mut up_replaced = BTreeSet::new();
        let mut up_written = BTreeSet::new();
        let mut up_shared = BTreeSet::new();
        for fact in base_facts.iter().filter(|f| f.owner == fun.owner) {
            match &fact.obligation {
                Obligation::ReadUp(span) => {
                    up_spans.insert(*span);
                }
                Obligation::Replace(span) => {
                    up_replaced.insert(*span);
                }
                Obligation::Write(span) | Obligation::WriteExisting(span) => {
                    up_written.insert(*span);
                }
                Obligation::Share(span)
                | Obligation::StoreShare(span)
                | Obligation::NeedsSharing(span) => {
                    up_shared.insert(*span);
                }
                _ => {}
            }
        }

        let mut up_captures = Vec::new();
        for span in up_spans {
            let name = self
                .definition(span)
                .map(|id| self.program.hir.definition(id).name.value.clone())
                .unwrap_or_default();
            if name.is_empty() {
                continue;
            }
            let (_, outer_mode) = fun
                .outer_slots
                .get(&span)
                .copied()
                .unwrap_or((false, Mode::Plain));
            let variable = up_replaced.contains(&span);
            let mode = if up_shared.contains(&span) {
                Mode::Shared
            } else if up_written.contains(&span) {
                if outer_mode == Mode::Shared {
                    Mode::Shared
                } else {
                    Mode::Mut
                }
            } else if outer_mode != Mode::Plain {
                Mode::Ref
            } else {
                Mode::Plain
            };
            up_captures.push(crate::access::InferredUpCapture {
                binding_span: span,
                name,
                variable,
                mode,
            });
        }
        up_captures.sort_by(|a, b| a.name.cmp(&b.name));

        let return_mode = if fun.returned_new
            && !self.program.is_value(&fun.declared.result)
            && !self.program.is_must_consume(&fun.declared.result)
        {
            Some(crate::access::InferredReturnMode::New)
        } else {
            None
        };

        let mut return_contained_set = BTreeSet::new();
        for entry in &fun.return_sources {
            if entry.result_path.is_empty() {
                continue;
            }
            if let Some(Some(formal_span)) = fun.formals.get(entry.formal)
                && let Some(param_id) = self.definition(*formal_span)
            {
                let param_name = self.program.hir.definition(param_id).name.value.clone();
                return_contained_set.insert((entry.access, param_name));
            }
        }
        let return_contained: Vec<_> = return_contained_set.into_iter().collect();

        crate::access::InferredSignature {
            def_id: fun.id,
            owner_span: fun.owner,
            visibility: def.visibility,
            is_local_where,
            is_main,
            is_meta: fun.is_meta,
            has_holes: fun.has_holes,
            has_pruned_meta: fun.has_pruned_meta,
            has_via: !fun.via.is_empty() || !fun.member_axes.is_empty(),
            effects,
            effect_causes,
            needs_mut,
            needs_shared_mut,
            needs_capture,
            up_captures,
            return_mode,
            return_contained,
        }
    }

    fn extract_causal_chain(
        root: &Fact,
        rules: &[Rule<Fact>],
        derived_by: &BTreeMap<Fact, usize>,
        owner_names: &BTreeMap<Span, String>,
    ) -> Vec<String> {
        let mut chain = Vec::new();
        let mut visited = BTreeSet::new();
        let mut current = root.clone();
        loop {
            if let Some(name) = owner_names.get(&current.owner)
                && chain.last() != Some(name)
            {
                chain.push(name.clone());
            }
            if !visited.insert(current.clone()) {
                break;
            }
            let Some(&rule_idx) = derived_by.get(&current) else {
                break;
            };
            let Some(rule) = rules.get(rule_idx) else {
                break;
            };
            let next = rule
                .premises
                .iter()
                .find(|p| p.owner != current.owner)
                .or_else(|| rule.premises.first());
            match next {
                Some(premise) => current = premise.clone(),
                None => break,
            }
        }
        chain
    }

    fn is_top_level_stmt(&self, file: FileId, target: StmtId) -> bool {
        fn contains_stmt(ast: &Ast, items: &[StmtId], target: StmtId) -> bool {
            for &item in items {
                if item == target {
                    return true;
                }
                if let StmtKind::Sub {
                    items: sub_items, ..
                } = &ast.stmt(item).value.kind
                    && contains_stmt(ast, sub_items, target)
                {
                    return true;
                }
            }
            false
        }
        let ast = self.ast(file);
        contains_stmt(ast, &ast.items, target)
    }

    fn scan_body_flags(&self, file: FileId, body: ExprId) -> (bool, bool) {
        fn walk_stmt(ast: &Ast, id: StmtId, holes: &mut bool, meta: &mut bool) {
            match &ast.stmt(id).value.kind {
                StmtKind::Binding {
                    value, fallback, ..
                } => {
                    if let Some(v) = value {
                        walk_expr(ast, *v, holes, meta);
                    }
                    if let Some(f) = fallback {
                        walk_expr(ast, *f, holes, meta);
                    }
                }
                StmtKind::Defer(e) | StmtKind::Expr(e) => walk_expr(ast, *e, holes, meta),
                StmtKind::With(h) => walk_expr(ast, h.value, holes, meta),
                StmtKind::Function(f) => {
                    if let Some(b) = f.body {
                        walk_expr(ast, b, holes, meta);
                    }
                }
                _ => {}
            }
        }
        fn walk_expr(ast: &Ast, id: ExprId, holes: &mut bool, meta: &mut bool) {
            match &ast.expr(id).value {
                Expr::Hole => *holes = true,
                Expr::Block {
                    statements,
                    helpers,
                } => {
                    for &s in statements.iter().chain(helpers) {
                        walk_stmt(ast, s, holes, meta);
                    }
                }
                Expr::With {
                    handlers,
                    statements,
                    helpers,
                } => {
                    for h in handlers {
                        walk_expr(ast, h.value, holes, meta);
                    }
                    for &s in statements.iter().chain(helpers) {
                        walk_stmt(ast, s, holes, meta);
                    }
                }
                Expr::If {
                    is_meta,
                    condition,
                    yes,
                    no,
                } => {
                    if *is_meta {
                        *meta = true;
                    }
                    match condition {
                        Condition::Expr(e) | Condition::Binding { value: e, .. } => {
                            walk_expr(ast, *e, holes, meta);
                        }
                    }
                    walk_expr(ast, *yes, holes, meta);
                    if let Some(n) = no {
                        walk_expr(ast, *n, holes, meta);
                    }
                }
                Expr::Match {
                    is_meta,
                    value,
                    arms,
                    ..
                } => {
                    if *is_meta {
                        *meta = true;
                    }
                    walk_expr(ast, *value, holes, meta);
                    for arm in arms {
                        if let Some(g) = arm.guard {
                            walk_expr(ast, g, holes, meta);
                        }
                        walk_expr(ast, arm.body, holes, meta);
                    }
                }
                Expr::While { condition, body } => {
                    match condition {
                        Condition::Expr(e) | Condition::Binding { value: e, .. } => {
                            walk_expr(ast, *e, holes, meta);
                        }
                    }
                    walk_expr(ast, *body, holes, meta);
                }
                Expr::For { iterable, body, .. } => {
                    walk_expr(ast, *iterable, holes, meta);
                    walk_expr(ast, *body, holes, meta);
                }
                Expr::Unary { value, .. }
                | Expr::Cast { value, .. }
                | Expr::Meta(value)
                | Expr::Closure { body: value, .. } => walk_expr(ast, *value, holes, meta),
                Expr::Binary { left, right, .. } => {
                    walk_expr(ast, *left, holes, meta);
                    walk_expr(ast, *right, holes, meta);
                }
                Expr::Pipeline { value, target, .. } => {
                    walk_expr(ast, *value, holes, meta);
                    walk_expr(ast, *target, holes, meta);
                }
                Expr::Member { base, member, .. } => {
                    walk_expr(ast, *base, holes, meta);
                    if let Member::Computed(e) = member {
                        walk_expr(ast, *e, holes, meta);
                    }
                }
                Expr::Index { base, index, .. } => {
                    walk_expr(ast, *base, holes, meta);
                    walk_expr(ast, *index, holes, meta);
                }
                Expr::Range { start, end, .. } => {
                    if let Some(s) = start {
                        walk_expr(ast, *s, holes, meta);
                    }
                    if let Some(e) = end {
                        walk_expr(ast, *e, holes, meta);
                    }
                }
                Expr::Call { callee, args } => {
                    walk_expr(ast, *callee, holes, meta);
                    for a in args {
                        walk_expr(ast, a.value, holes, meta);
                    }
                }
                Expr::Wrap { args, .. } => {
                    for a in args {
                        walk_expr(ast, a.value, holes, meta);
                    }
                }
                Expr::Record { fields, .. } => {
                    for f in fields {
                        if let Some(v) = f.value {
                            walk_expr(ast, v, holes, meta);
                        }
                    }
                }
                Expr::Array(items) | Expr::Tuple(items) => {
                    for &e in items {
                        walk_expr(ast, e, holes, meta);
                    }
                }
                Expr::Map(entries) => {
                    for &(k, v) in entries {
                        walk_expr(ast, k, holes, meta);
                        walk_expr(ast, v, holes, meta);
                    }
                }
                Expr::Interpolated(parts) => {
                    for p in parts {
                        if let ril_syntax::syntax::StringPart::Interpolation(e) = p {
                            walk_expr(ast, *e, holes, meta);
                        }
                    }
                }
                Expr::Transfer { value: Some(v), .. } => walk_expr(ast, *v, holes, meta),
                _ => {}
            }
        }
        let mut holes = false;
        let mut meta = false;
        walk_expr(self.ast(file), body, &mut holes, &mut meta);
        (holes, meta)
    }
}
