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
        if callable.open_effects || callable.open_state {
            self.error(
                Code::E0547,
                ctx.owner,
                "named definitions require closed effect and state sets",
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
                self.error(Code::E0411, span, "new parameter requires a non-linear shared object");
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
        let mut value = self.eval_exit_expr(&mut ctx, &mut ledger, body, &prior_slots, prior_holds, 0, true);
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
                Obligation::NoCtlParam(span) => {
                    if let Some(formal) = fun.formals.iter().position(|decl| *decl == Some(*span)) {
                        summary.no_ctl_params.push(formal);
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
        summary.no_ctl_params.sort_unstable();
        summary.no_ctl_params.dedup();
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
                    Code::E0626,
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
                        walk_pattern(this, ast, arm.pattern, mark_ty, forbids_drop, local_generics);
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
}
