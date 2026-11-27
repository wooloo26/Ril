use super::*;
use crate::ty::reception;

impl Analyzer<'_> {
    pub(super) fn shadow_type(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        ty: ril_syntax::syntax::TypeId,
    ) {
        use ril_syntax::syntax::{GenericArg, Type};
        match &self.ast(ctx.file).ty(ty).value {
            Type::TypeOf(expr) => {
                let mut shadow = ctx.clone();
                shadow.shadow = true;
                shadow.loop_owner = None;
                let mut slots = ledger.clone();
                slots.clear_result_obligations();
                let result = self.expr(&mut shadow, &mut slots, *expr);
                self.check_results(&slots, &result.root_results());
            }
            Type::Named(path) => {
                for parameter in path.segments.iter().flat_map(|segment| &segment.arguments) {
                    if let GenericArg::Type(ty) = parameter {
                        self.shadow_type(ctx, ledger, *ty);
                    }
                }
            }
            Type::Array(_, ty) | Type::Option(ty) | Type::Project { base: ty, .. } => {
                self.shadow_type(ctx, ledger, *ty);
            }
            Type::Result(left, right) | Type::Map(left, _, right) => {
                self.shadow_type(ctx, ledger, *left);
                self.shadow_type(ctx, ledger, *right);
            }
            Type::Tuple(items) => {
                for (_, ty) in items {
                    self.shadow_type(ctx, ledger, *ty);
                }
            }
            Type::Record { fields, .. } => {
                for field in fields {
                    self.shadow_type(ctx, ledger, field.ty);
                }
            }
            Type::Callable(call) => {
                for ty in call.params.iter().filter_map(|param| param.ty) {
                    self.shadow_type(ctx, ledger, ty);
                }
                self.shadow_type(ctx, ledger, call.result);
            }
            _ => {}
        }
    }

    pub(super) fn retarget(value: &mut Datum, path: &[reception::Step], mode: Access) -> bool {
        let Some((step, rest)) = path.split_first() else {
            if value.roots.iter().any(|root| !root.new) {
                return false;
            }
            for root in &mut value.roots {
                root.fix_mode(mode);
                root.clone_member = false;
            }
            return true;
        };
        let coordinate = match step {
            reception::Step::Field(name) => Coordinate::Field(name.clone()),
            reception::Step::Position(index) => Coordinate::Index(index.to_string()),
            reception::Step::Elements => {
                return if value.members.is_empty() {
                    value.roots.iter().all(|root| root.new)
                } else {
                    value
                        .members
                        .values_mut()
                        .all(|member| Self::retarget(member, rest, mode))
                };
            }
        };
        if let Some(member) = value.members.get_mut(&coordinate) {
            Self::retarget(member, rest, mode)
        } else {
            value.origins().all(|origin| origin.new)
        }
    }

    pub(super) fn receive_member(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        mut value: Datum,
        mode: Access,
        span: Span,
    ) -> Datum {
        if mode != Access::Immutable {
            value.forget_collection_layout();
        }
        if value.roots.is_empty() {
            return value;
        }
        if mode == Access::Shared {
            self.check_shared_reception(&value, span);
        }
        if mode == Access::Immutable
            && self.require_snapshot(
                (ctx, ledger),
                &ledger.snapshot(&value),
                Code::E0535,
                span,
                "live authority cannot enter an immutable member",
            )
        {
            value.specialize_snapshot_sources();
        }
        let inline_closure = value.environments.contains(&span);
        if value.requires_new || inline_closure {
            if mode == Access::Mut
                && inline_closure
                && value
                    .members
                    .values()
                    .flat_map(Datum::origins)
                    .any(|capture| capture.mode.writes())
            {
                self.error(
                    Code::E0510,
                    span,
                    "a closure retaining a writer needs shared writable storage",
                );
            }
            for root in &mut value.roots {
                root.fix_mode(mode);
            }
            return value;
        }
        let valid = value.roots.iter().all(|root| root.mode == mode);
        if !valid {
            let code = match mode {
                Access::Immutable => Code::E0535,
                Access::Ref => Code::E0357,
                Access::Mut if value.writers() => Code::E0510,
                Access::Mut | Access::Shared => Code::E0522,
            };
            self.error(
                code,
                span,
                "existing source does not match the member's access mode",
            );
        }
        if mode == Access::Mut && value.writers() {
            self.error(
                Code::E0510,
                span,
                "mutable member requires an exclusive handoff",
            );
        }
        for root in &mut value.roots {
            root.explicit_share = false;
        }
        value
    }

    pub(super) fn require_snapshot(
        &mut self,
        (ctx, ledger): (&Context, &Ledger),
        value: &Datum,
        code: Code,
        span: Span,
        message: &'static str,
    ) -> bool {
        let mut conditions = BTreeMap::<_, BTreeSet<_>>::new();
        if !value.accepts_snapshot_sources(&mut |origin| {
            let Some(expression) = origin.forwarded_mode() else {
                return false;
            };
            let owner = origin.entry_callable().unwrap_or(ctx.owner);
            conditions.entry(owner).or_default().insert(expression);
            true
        }) {
            self.error(code, span, message);
            return false;
        }
        // A symbolic path can be treated as immutable after this reception.
        // Keep only the mode assignments for which all such paths are plain.
        if ctx.reachable && !ctx.shadow {
            self.snapshots.freeze(ledger, value);
            self.mode_constraints
                .extend(conditions.into_iter().map(|(owner, expressions)| {
                    domains::ModeConstraint {
                        owner,
                        conditions: Vec::new(),
                        test: domains::ModeTest::Immutable(expressions, code),
                        span,
                        message,
                    }
                }));
        }
        true
    }

    pub(super) fn freeze_value(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        value: &mut Datum,
        span: Span,
    ) {
        *value = ledger.snapshot(value);
        self.require_snapshot(
            (ctx, ledger),
            value,
            Code::E0535,
            span,
            "live authority cannot be frozen as a plain snapshot",
        );
        value.freeze();
    }

    pub(super) fn require_shared_replacement(
        &mut self,
        value: &Datum,
        span: Span,
        allow_new: bool,
    ) {
        if value
            .roots
            .iter()
            .any(|root| !(root.explicit_share || allow_new && root.new))
        {
            self.error(
                Code::E0510,
                span,
                "shared replacement requires a '^mut' expression",
            );
        }
    }

    pub(super) fn check_exclusive_reception(&mut self, value: &Datum, span: Span) {
        // A Draft projection remains confined to the derive callback.
        if value.requires_new || value.writers() && value.roots.iter().all(|root| root.draft) {
            return;
        }
        if value.writers() {
            self.error(
                Code::E0510,
                span,
                "a persistent mutable binding requires an exclusive handoff",
            );
        } else {
            self.error(
                Code::E0520,
                span,
                "binding cannot manufacture write authority",
            );
        }
    }

    pub(super) fn check_shared_reception(&mut self, value: &Datum, span: Span) {
        if value
            .roots
            .iter()
            .any(|root| root.call_scoped_access && root.mode.writes())
        {
            self.error(Code::E0528, span, "a call-scoped writer cannot be shared");
        }
    }

    pub(super) fn shared_local_input(
        &mut self,
        ctx: &Context,
        declaration: Span,
        value: &Datum,
        span: Span,
    ) {
        let closure_with_writer =
            value.creates_environment() && value.origins().any(|origin| origin.mode.writes());
        if !value.writers() && !closure_with_writer {
            self.error(
                Code::E0527,
                span,
                "shared binding requires a writable source",
            );
            return;
        }
        self.check_shared_reception(value, span);
        let existing_writer = value.roots.iter().any(|root| {
            root.mode.writes() && !(root.new && (value.requires_new || root.explicit_share))
        });
        if existing_writer || closure_with_writer {
            self.seed(ctx, Obligation::SharedReception(declaration));
        }
    }

    pub(super) fn require_shared_local(&mut self, ctx: &Context, declaration: Span, value: &Datum) {
        self.requirement(
            ctx,
            declaration,
            Obligation::SharedReception(declaration),
            "shared binding requires reachable reception of a shared writer",
        );
        self.shared_local_input(ctx, declaration, value, declaration);
    }

    pub(super) fn check_ref_binding(&mut self, span: Span, value: &Datum, variable: bool) {
        if value.roots.iter().any(|root| root.explicit_share) {
            self.error(
                Code::E0527,
                span,
                "a ref binding does not use a '^mut' marker",
            );
        } else if value.roots.iter().any(|root| root.from_variable) {
            self.error(
                Code::E0531,
                span,
                "a reassignable binding cannot anchor a ref view",
            );
        } else if value.roots.is_empty() {
            self.error(Code::E0531, span, "ref binding has no live object source");
        } else if (value.requires_new
            || value
                .roots
                .iter()
                .any(|root| root.new && root.dependencies.is_empty()))
            && (variable
                || !value
                    .members
                    .values()
                    .flat_map(Datum::origins)
                    .any(|source| source.mode == Access::Ref && !source.new))
        {
            self.error(
                Code::E0543,
                span,
                "temporary has no live ref source to anchor the binding",
            );
        }
    }

    pub(super) fn check_ref_scope(&mut self, span: Span, value: &Datum, destination: Span) {
        let shorter_scope = value
            .roots
            .iter()
            .flat_map(|root| &root.anchor_scopes)
            .any(|source| {
                source.file != destination.file
                    || source.start > destination.start
                    || source.end < destination.end
            });
        if shorter_scope {
            self.error(
                Code::E0604,
                span,
                "ref source scope must enclose the reassignable binding's scope",
            );
        }
    }

    pub(super) fn collect_defer_refs(&self, ctx: &Context, prior_defers: usize) -> BTreeSet<Span> {
        let mut refs = BTreeSet::new();
        for action in ctx.defers.get(prior_defers..).unwrap_or_default() {
            let defer_span = self.ast(action.file).expr(action.expr).span;
            for (_, def_id) in self.program.hir.references_within(defer_span) {
                refs.insert(self.program.hir.definition(def_id).name.span);
            }
        }
        refs
    }

    pub(super) fn can_promote_exit_local(
        &self,
        ctx: &Context,
        ledger: &Ledger,
        value: &Datum,
        prior_slots: &BTreeSet<Span>,
        prior_holds: usize,
        defer_refs: Option<&BTreeSet<Span>>,
        exiting_function: bool,
    ) -> bool {
        if value.requires_new || value.roots.is_empty() || !value.writers() {
            return false;
        }
        if value.roots.iter().any(|r| {
            r.mode != Access::Mut
                || r.confined.is_some()
                || r.from_variable
                || r.call_scoped_access
        }) {
            return false;
        }
        if ledger
            .loop_snapshot(value)
            .origins()
            .any(|o| o.confined.is_some())
        {
            return false;
        }
        for root in &value.roots {
            let src = root.region.source;
            let local_to_exit = if exiting_function {
                !ctx.caller_slots.contains(&src)
                    && (!ctx.formals.contains(&Some(src)) || ctx.new_formals.contains(&src))
            } else {
                !prior_slots.contains(&src)
                    && !ctx.caller_slots.contains(&src)
                    && !ctx.formals.contains(&Some(src))
            };
            if !local_to_exit {
                return false;
            }
            for dep in &root.dependencies {
                if !dep.prior_iteration {
                    if ledger.slots.get(&dep.span).is_some_and(|s| s.variable) {
                        return false;
                    }
                    if defer_refs.is_some_and(|refs| refs.contains(&dep.span)) {
                        return false;
                    }
                }
            }
            if ledger.holds.iter().take(prior_holds).any(|(_, held)| {
                ledger
                    .loop_snapshot(held)
                    .origins()
                    .any(|active| root.overlaps(active))
            }) {
                return false;
            }
            for (decl, slot) in &ledger.slots {
                let outer_slot = if exiting_function {
                    ctx.caller_slots.contains(decl)
                        || (ctx.formals.contains(&Some(*decl)) && !ctx.new_formals.contains(decl))
                } else {
                    prior_slots.contains(decl)
                };
                if outer_slot
                    && ledger
                        .loop_snapshot(&slot.value)
                        .origins()
                        .any(|retained| root.overlaps(retained))
                {
                    return false;
                }
            }
        }
        true
    }

    pub(super) fn promote_datum_to_new(value: &mut Datum) {
        value.requires_new = true;
        for root in &mut value.roots {
            root.new = true;
            root.mode = Access::Mut;
            root.explicit_share = false;
            root.dependencies.clear();
        }
    }

    pub(super) fn try_promote_exit_new(
        &self,
        ctx: &Context,
        ledger: &Ledger,
        value: &mut Datum,
        prior_slots: &BTreeSet<Span>,
        prior_holds: usize,
        exiting_function: bool,
    ) {
        if self.can_promote_exit_local(
            ctx,
            ledger,
            value,
            prior_slots,
            prior_holds,
            None,
            exiting_function,
        ) {
            Self::promote_datum_to_new(value);
        }
    }

    pub(super) fn eval_exit_expr(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        id: ExprId,
        prior_slots: &BTreeSet<Span>,
        prior_holds: usize,
        prior_defers: usize,
        exiting_function: bool,
    ) -> Datum {
        let ast = self.ast(ctx.file);
        let node = ast.expr(id);
        let span = node.span;
        let defer_refs = self.collect_defer_refs(ctx, prior_defers);
        match &node.value {
            Expr::Block {
                statements,
                helpers,
            } if exiting_function => {
                let mut local_ctx = ctx.clone();
                local_ctx.scope = span;
                for &helper in helpers {
                    if let StmtKind::Effect { name, .. } = &ast.stmt(helper).value.kind
                        && let Some(effect) = self.definition(name.span)
                    {
                        local_ctx
                            .local_effects
                            .insert(self.program.hir.effect_label(effect));
                    }
                }
                let start_returns = local_ctx.return_values.len();
                let block_prior = ledger.slots.keys().copied().collect::<BTreeSet<_>>();
                let prior_iter = ledger.iteration.len();
                let block_holds = ledger.holds.len();
                let block_defers = local_ctx.defers.len();
                let mut result = Datum::default();
                for (i, &item) in statements.iter().enumerate() {
                    let is_tail = i + 1 == statements.len();
                    if is_tail
                        && let StmtKind::Expr(tail_expr) = ast.stmt(item).value.kind
                    {
                        result = self.eval_exit_expr(
                            &mut local_ctx,
                            ledger,
                            tail_expr,
                            prior_slots,
                            prior_holds,
                            prior_defers,
                            true,
                        );
                        if self.ty(ast.expr(tail_expr).span) == &Ty::Never {
                            local_ctx.reachable = false;
                        }
                    } else {
                        result = self.statement(&mut local_ctx, ledger, item, is_tail);
                        if let StmtKind::Expr(expr) = ast.stmt(item).value.kind
                            && self.ty(ast.expr(expr).span) == &Ty::Never
                        {
                            local_ctx.reachable = false;
                        }
                    }
                }
                for &helper in helpers {
                    self.statement(&mut local_ctx, ledger, helper, false);
                }
                if local_ctx.reachable && !ledger.no_continuation {
                    self.run_defers(&mut local_ctx, ledger, block_defers);
                    ledger.holds.truncate(block_holds);
                    self.try_promote_exit_new(
                        &local_ctx,
                        ledger,
                        &mut result,
                        prior_slots,
                        prior_holds,
                        true,
                    );
                } else if local_ctx.defers.len() > block_defers {
                    let unchecked = local_ctx
                        .defers
                        .get(block_defers..)
                        .unwrap_or_default()
                        .iter()
                        .any(|d| !self.checked_defers.contains(&d.span));
                    if unchecked {
                        let mut unwind_ledger = ledger.clone();
                        self.run_defers(&mut local_ctx, &mut unwind_ledger, block_defers);
                    }
                }
                local_ctx.defers.truncate(block_defers);
                if result.origins().any(|origin| {
                    origin
                        .confined
                        .is_some_and(|id| span.start <= id.start && id.end <= span.end)
                }) {
                    self.error(Code::E0604, span, "resource or draft escapes its block");
                }
                ledger.slots.retain(|id, _| block_prior.contains(id));
                ledger.iteration.truncate(prior_iter);
                ledger.holds.truncate(block_holds);
                ctx.return_values
                    .extend(local_ctx.return_values.into_iter().skip(start_returns));
                ctx.reachable &= !ledger.no_continuation;
                result
            }
            Expr::Cast { value, .. } => self.eval_exit_expr(
                ctx,
                ledger,
                *value,
                prior_slots,
                prior_holds,
                prior_defers,
                exiting_function,
            ),
            Expr::Record { fields, .. } => {
                let mut record = Datum::source(span, Access::Mut, true);
                let mut evaluated = Vec::with_capacity(fields.len());
                let mut promoted_origins: Vec<(usize, Vec<Origin>)> = Vec::new();
                for (idx, field) in fields.iter().enumerate() {
                    let coordinate = Coordinate::Field(field.name.value.clone());
                    let field_span = field.value.map_or(field.name.span, |e| ast.expr(e).span);
                    let mut value = if let Some(expr) = field.value {
                        self.eval_exit_expr(
                            ctx,
                            ledger,
                            expr,
                            prior_slots,
                            prior_holds,
                            prior_defers,
                            exiting_function,
                        )
                    } else {
                        self.read_span(ctx, ledger, field.name.span)
                    };
                    if self.can_promote_exit_local(
                        ctx,
                        ledger,
                        &value,
                        prior_slots,
                        prior_holds,
                        Some(&defer_refs),
                        exiting_function,
                    ) {
                        promoted_origins.push((idx, value.roots.clone()));
                        Self::promote_datum_to_new(&mut value);
                    }
                    let field_is_linear = self.program.is_must_consume(self.ty(field_span));
                    if field_is_linear {
                        self.consume_linear(ctx, ledger, &mut value);
                    }
                    let access = self.member_schema(span, &coordinate).0;
                    let value = self.receive_member(ctx, ledger, value, access, field_span);
                    evaluated.push((coordinate, value, field_span));
                }
                self.check_exit_sibling_overlap(ledger, &evaluated, &promoted_origins);
                for (coordinate, value, _) in evaluated {
                    record.members.insert(coordinate, value);
                }
                self.finish_exit_composite(ctx, ledger, span, &mut record);
                record
            }
            Expr::Tuple(items) | Expr::Array(items) => {
                let mut sequence = Datum::source(span, Access::Mut, true);
                if let Ty::Array(member) = self.ty(span) {
                    if higher_order::carries_callable(self.program, &member.ty) {
                        ledger.record_array_length(span, items.len());
                    }
                    if results::carries_result(self.program, self.hir_scope(ctx), &member.ty) {
                        sequence.array_len = Some(items.len());
                    }
                }
                let mut evaluated = Vec::with_capacity(items.len());
                let mut promoted_origins: Vec<(usize, Vec<Origin>)> = Vec::new();
                for (i, &item) in items.iter().enumerate() {
                    let coordinate = Coordinate::Index(i.to_string());
                    let item_span = ast.expr(item).span;
                    let mut value = self.eval_exit_expr(
                        ctx,
                        ledger,
                        item,
                        prior_slots,
                        prior_holds,
                        prior_defers,
                        exiting_function,
                    );
                    if self.can_promote_exit_local(
                        ctx,
                        ledger,
                        &value,
                        prior_slots,
                        prior_holds,
                        Some(&defer_refs),
                        exiting_function,
                    ) {
                        promoted_origins.push((i, value.roots.clone()));
                        Self::promote_datum_to_new(&mut value);
                    }
                    if self.program.is_must_consume(self.ty(item_span)) {
                        self.consume_linear(ctx, ledger, &mut value);
                    }
                    let access = self.member_schema(span, &coordinate).0;
                    let value = self.receive_member(ctx, ledger, value, access, item_span);
                    evaluated.push((coordinate, value, item_span));
                }
                self.check_exit_sibling_overlap(ledger, &evaluated, &promoted_origins);
                for (coordinate, value, _) in evaluated {
                    sequence.members.insert(coordinate, value);
                }
                self.finish_exit_composite(ctx, ledger, span, &mut sequence);
                sequence
            }
            Expr::Wrap { path: _, args } => {
                if let [arg] = args.as_slice() {
                    let arg_span = ast.expr(arg.value).span;
                    let mut value = self.eval_exit_expr(
                        ctx,
                        ledger,
                        arg.value,
                        prior_slots,
                        prior_holds,
                        prior_defers,
                        exiting_function,
                    );
                    if arg.mode == Mode::Plain
                        && self.can_promote_exit_local(
                            ctx,
                            ledger,
                            &value,
                            prior_slots,
                            prior_holds,
                            Some(&defer_refs),
                            exiting_function,
                        )
                    {
                        Self::promote_datum_to_new(&mut value);
                    }
                    let mut result = match arg.mode {
                        Mode::Plain if value.requires_new => value,
                        Mode::Plain if Self::forwards_via(ctx, &value) => {
                            self.prepare_argument(ctx, ledger, arg, value, arg_span, Mode::Via)
                        }
                        mode => {
                            let val =
                                self.prepare_argument(ctx, ledger, arg, value, arg_span, mode);
                            for conflict in ledger.hold_conflicts(&val, mode) {
                                self.check_conflict(
                                    ctx,
                                    conflict,
                                    None,
                                    arg_span,
                                    "argument authority overlaps an active handler hold",
                                );
                            }
                            val
                        }
                    };
                    if self.program.is_must_consume(self.ty(arg_span))
                        && !matches!(arg.mode, Mode::Ref | Mode::Mut | Mode::Shared)
                    {
                        self.consume_linear(ctx, ledger, &mut result);
                    }
                    self.finish_exit_composite(ctx, ledger, span, &mut result);
                    return result;
                }
                let mut evaluated = Vec::with_capacity(args.len());
                let mut promoted_origins: Vec<(usize, Vec<Origin>)> = Vec::new();
                for (index, arg) in args.iter().enumerate() {
                    let arg_span = ast.expr(arg.value).span;
                    let mut value = self.eval_exit_expr(
                        ctx,
                        ledger,
                        arg.value,
                        prior_slots,
                        prior_holds,
                        prior_defers,
                        exiting_function,
                    );
                    if arg.mode == Mode::Plain
                        && self.can_promote_exit_local(
                            ctx,
                            ledger,
                            &value,
                            prior_slots,
                            prior_holds,
                            Some(&defer_refs),
                            exiting_function,
                        )
                    {
                        promoted_origins.push((index, value.roots.clone()));
                        Self::promote_datum_to_new(&mut value);
                    }
                    let mut value =
                        self.receive_member(ctx, ledger, value, Access::Immutable, arg_span);
                    if self.program.is_must_consume(self.ty(arg_span))
                        && !matches!(arg.mode, Mode::Ref | Mode::Mut | Mode::Shared)
                    {
                        self.consume_linear(ctx, ledger, &mut value);
                    }
                    evaluated.push((Coordinate::Index(index.to_string()), value, arg_span));
                }
                self.check_exit_sibling_overlap(ledger, &evaluated, &promoted_origins);
                let mut result = Datum::source(span, Access::Mut, true);
                for (coord, val, _) in evaluated {
                    result.members.insert(coord, val);
                }
                self.finish_exit_composite(ctx, ledger, span, &mut result);
                result
            }
            Expr::Call { callee, args } => {
                let is_ctor = match &ast.expr(*callee).value {
                    Expr::Path(path) => self
                        .definition(path.span)
                        .map(|id| self.program.hir.definition(id))
                        .is_some_and(|def| {
                            matches!(def.kind, DefinitionKind::Variant(_))
                                || matches!(def.kind, DefinitionKind::Type)
                        }),
                    _ => false,
                };
                if !is_ctor {
                    return self.expr(ctx, ledger, id);
                }
                let def_id = match &ast.expr(*callee).value {
                    Expr::Path(path) => self.definition(path.span),
                    _ => None,
                };
                let def = def_id.map(|id| self.program.hir.definition(id));
                let sig = def_id
                    .and_then(|id| self.program.callables.get(&id).map(|s| s.as_ref()))
                    .or_else(|| match self.ty(ast.expr(*callee).span) {
                        Ty::Callable(sig) => Some(sig.as_ref()),
                        _ => None,
                    });
                let mut evaluated = Vec::with_capacity(args.len());
                let mut promoted_origins: Vec<(usize, Vec<Origin>)> = Vec::new();
                for (index, arg) in args.iter().enumerate() {
                    let arg_span = ast.expr(arg.value).span;
                    let mut value = self.eval_exit_expr(
                        ctx,
                        ledger,
                        arg.value,
                        prior_slots,
                        prior_holds,
                        prior_defers,
                        exiting_function,
                    );
                    let already_new = value.requires_new;
                    let from_new_formal = value
                        .roots
                        .iter()
                        .any(|r| ctx.new_formals.contains(&r.region.source));
                    if arg.mode == Mode::Plain
                        && self.can_promote_exit_local(
                            ctx,
                            ledger,
                            &value,
                            prior_slots,
                            prior_holds,
                            Some(&defer_refs),
                            exiting_function,
                        )
                    {
                        promoted_origins.push((index, value.roots.clone()));
                        Self::promote_datum_to_new(&mut value);
                    }
                    let inferred = sig
                        .and_then(|s| s.parameters.get(index))
                        .is_some_and(|p| p.mode == Mode::Via);
                    let effective_mode = if inferred {
                        match arg.mode {
                            Mode::Plain if value.requires_new && (already_new || !from_new_formal) => {
                                Mode::New
                            }
                            Mode::Plain if Self::forwards_via(ctx, &value) => Mode::Via,
                            mode => mode,
                        }
                    } else {
                        sig.and_then(|s| s.parameters.get(index))
                            .map_or(arg.mode, |p| p.mode)
                    };
                    let mut value =
                        self.prepare_argument(ctx, ledger, arg, value, arg_span, effective_mode);
                    if self.program.is_must_consume(self.ty(arg_span))
                        && !matches!(arg.mode, Mode::Ref | Mode::Mut | Mode::Shared)
                    {
                        self.consume_linear(ctx, ledger, &mut value);
                    }
                    evaluated.push((Coordinate::Index(index.to_string()), value, arg_span));
                }
                self.check_exit_sibling_overlap(ledger, &evaluated, &promoted_origins);
                let mut result = Datum::source(span, Access::Mut, true);
                for (coord, val, _) in evaluated {
                    result.members.insert(coord, val);
                }
                if let Some(def) = def
                    && matches!(def.kind, DefinitionKind::Variant(_))
                {
                    result.set_variant(&def.name.value);
                }
                self.finish_exit_composite(ctx, ledger, span, &mut result);
                result
            }
            _ => self.expr(ctx, ledger, id),
        }
    }

    fn check_exit_sibling_overlap(
        &mut self,
        ledger: &Ledger,
        evaluated: &[(Coordinate, Datum, Span)],
        promoted_origins: &[(usize, Vec<Origin>)],
    ) {
        for (idx, roots) in promoted_origins {
            for (other_idx, (_, other_val, other_span)) in evaluated.iter().enumerate() {
                if *idx == other_idx {
                    continue;
                }
                let snap = ledger.loop_snapshot(other_val);
                if roots
                    .iter()
                    .any(|r| snap.origins().any(|o| r.overlaps(o)))
                {
                    self.error(
                        Code::E0510,
                        *other_span,
                        "exiting local cannot be both promoted to new and aliased in a sibling expression",
                    );
                }
            }
        }
    }

    fn finish_exit_composite(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        span: Span,
        value: &mut Datum,
    ) {
        ctx.reachable &= !ledger.no_continuation;
        if ctx.reachable
            && self.ty(span).is_result(&self.program.hir)
            && !value.has_root_result()
        {
            ledger.record_result(value, span);
        }
        if ctx.reachable
            && !ctx.shadow
            && self.program.is_must_consume(self.ty(span))
            && value
                .all_linear()
                .iter()
                .all(|occ| ledger.linear_consumed.contains(occ))
        {
            ledger.record_linear(
                value,
                span,
                matches!(self.ty(span), Ty::Array(_) | Ty::Map(..)),
            );
        }
        if self.program.is_value(self.ty(span)) {
            value.roots.clear();
            value.members.clear();
            value.requires_new = false;
        }
        ledger.stamp(value);
    }

    pub(super) fn returned(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        value: Datum,
        span: Span,
    ) {
        let mut value = ledger.snapshot_call_graph(&value);
        ledger.inspect(&value);
        ledger.consume_datum_linear(&value);
        if value.origins().any(|origin| origin.confined.is_some()) {
            self.error(Code::E0604, span, "confined authority cannot be returned");
        }
        if !ctx.runtime || ctx.shadow {
            return;
        }
        if !ctx.return_guards.is_empty() {
            let guards = ctx.return_guards.clone();
            self.check_guard_args(ctx, ledger, &guards);
        }
        self.storage_exit(ctx, ledger);
        if value.creates_environment() {
            self.seed(ctx, Obligation::Capture);
        }
        if value.returns_call_scoped_writer(ctx.expected) {
            self.error(
                Code::E0528,
                span,
                "a call-scoped writer cannot escape in a return",
            );
        }
        match ctx.expected {
            Mode::Plain if value.requires_new => self.error(
                Code::E0544,
                ctx.owner,
                "fresh shared return must declare -> new",
            ),
            Mode::Plain => {
                if self.require_snapshot(
                    (ctx, ledger),
                    &value,
                    Code::E0528,
                    span,
                    "plain return cannot expose live authority",
                ) {
                    value.specialize_snapshot_sources();
                }
            }
            Mode::New if !value.requires_new => {
                self.error(Code::E0546, span, "return does not have new qualification");
            }
            Mode::Ref | Mode::Shared
                if value.roots.is_empty()
                    || value
                        .roots
                        .iter()
                        .any(|root| !ctx.returns.contains(&root.region.source)) =>
            {
                self.error(
                    Code::E0545,
                    span,
                    "return does not select its declared entry source",
                );
            }
            Mode::Shared if value.roots.iter().any(|root| root.mode != Access::Shared) => {
                self.error(
                    Code::E0528,
                    span,
                    "shared return requires an existing shared writer",
                );
            }
            _ => {}
        }
        if ctx.expected == Mode::Shared {
            for origin in &value.roots {
                self.seed(ctx, Obligation::Retain(origin.region.source));
            }
        }
        let actual: BTreeSet<_> = value
            .members
            .values()
            .filter(|_| ctx.expected != Mode::Plain)
            .flat_map(Datum::origins)
            .filter(|origin| {
                !origin.new
                    && ctx.formals.contains(&Some(origin.region.source))
                    && !ctx.new_formals.contains(&origin.region.source)
            })
            .map(|origin| (origin.mode, origin.region.source))
            .collect();
        if ctx.expected != Mode::Infer
            && actual
                .iter()
                .any(|source| !ctx.declared_contained.contains(source))
        {
            self.error(Code::E0510, ctx.owner, "missing contained return source");
        }
        for &(_, source) in actual.iter().filter(|(mode, _)| *mode == Access::Shared) {
            self.seed(ctx, Obligation::Retain(source));
            self.seed(ctx, Obligation::Share(source));
        }
        if ctx.expected != Mode::Plain {
            for origin in value
                .members
                .values()
                .flat_map(Datum::origins)
                .filter(|origin| origin.mode == Access::Shared)
            {
                for dep in origin.dependency_spans() {
                    if !ctx.formals.contains(&Some(dep)) {
                        self.seed(ctx, Obligation::Write(dep));
                    }
                }
            }
        }
        ctx.return_values.push(value);
    }

    pub(super) fn storage_exit(&mut self, ctx: &Context, ledger: &Ledger) {
        if !ctx.in_function
            || !ctx.runtime
            || ctx.shadow
            || !ctx.reachable
            || ledger.no_continuation
        {
            return;
        }
        self.publish_at_exit(ctx, ledger, true);
        self.storage_exits
            .entry(ctx.owner)
            .or_default()
            .push(storage::StorageExit {
                updates: ledger.call_updates(ctx.owner, &ctx.formals, &ctx.caller_slots),
                flow: ledger.storage_flow.clone(),
            });
    }

    pub(super) fn publish_at_exit(&mut self, ctx: &Context, ledger: &Ledger, normal: bool) {
        if !ctx.runtime || ctx.shadow || !ctx.reachable {
            return;
        }
        for &slot in ctx.caller_slots.iter().chain(ctx.formals.iter().flatten()) {
            let Some(slot) = ledger.slots.get(&slot) else {
                continue;
            };
            let caller_root = !ctx.new_formals.contains(&slot.decl);
            let value = ledger.snapshot(&slot.value);
            value.surviving_publications(ctx.owner, caller_root, &mut |stored| {
                if stored.creates_environment() {
                    self.seed(ctx, Obligation::Capture);
                }
                for origin in stored
                    .origins()
                    .filter(|origin| origin.mode == Access::Shared)
                {
                    for dep in origin.dependency_spans() {
                        if !ctx.formals.contains(&Some(dep)) {
                            self.seed(ctx, Obligation::Write(dep));
                        }
                    }
                    self.seed(ctx, Obligation::Retain(origin.region.source));
                    let modeled = ctx.formals.contains(&Some(slot.decl))
                        || ledger.replaces_slot(ctx.owner, slot.decl);
                    let effect = if normal && modeled {
                        Obligation::StoreShare(origin.region.source)
                    } else {
                        Obligation::Share(origin.region.source)
                    };
                    self.seed(ctx, effect);
                }
            });
        }
    }

    pub(super) fn check_publication_source(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        value: &Datum,
        span: Span,
    ) {
        let value = ledger.loop_snapshot(value);
        self.check_stored_views(&value, false, span);
        if value
            .origins()
            .any(|origin| origin.call_scoped_access && origin.mode.writes())
        {
            self.error(
                Code::E0528,
                span,
                "a call-scoped writer cannot be retained in caller storage",
            );
        }
        for origin in value.origins().filter(|origin| {
            origin.mode == Access::Shared
                && origin.region.selection.is_empty()
                && ctx.via.contains(&origin.region.source)
        }) {
            self.seed(ctx, Obligation::NeedsSharing(origin.region.source));
        }
    }

    pub(super) fn check_stored_views(&mut self, value: &Datum, root_as_ref: bool, span: Span) {
        if value
            .origins()
            .any(|origin| origin.mode == Access::Ref && origin.call_scoped_access)
            || root_as_ref && value.roots.iter().any(|origin| origin.call_scoped_access)
        {
            self.error(
                Code::E0604,
                span,
                "a ref view of a call-scoped writer cannot be stored in existing storage",
            );
        }
    }

    pub(super) fn check_results(&mut self, ledger: &Ledger, except: &BTreeSet<ResultOccurrence>) {
        let pending: BTreeSet<_> = ledger
            .pending_results()
            .filter(|item| !except.contains(item))
            .map(|item| item.span)
            .chain(ledger.lost_results.iter().copied())
            .collect();
        for span in pending {
            self.error(
                Code::E0720,
                span,
                "fallible result has not been inspected on normal exit",
            );
        }
    }

    pub(super) fn check_linear(&mut self, ledger: &Ledger, except: &BTreeSet<LinearOccurrence>) {
        let pending: BTreeSet<_> = ledger
            .pending_linear()
            .filter(|item| !except.contains(*item))
            .map(|item| item.span)
            .collect();
        for span in pending {
            self.error(
                Code::E0625,
                span,
                "must-consume linear value has not been consumed on exit",
            );
        }
    }

    pub(super) fn discard(&mut self, ledger: &Ledger, value: &Datum) {
        for item in value
            .results()
            .iter()
            .filter(|item| !ledger.result_inspected(item))
        {
            self.error(Code::E0720, item.span, "discarded fallible result");
        }
        for item in value
            .all_linear()
            .iter()
            .filter(|item| !ledger.linear_consumed.contains(*item))
        {
            self.error(Code::E0625, item.span, "discarded must-consume value");
        }
    }

    pub(super) fn run_defers(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        target_depth: usize,
    ) {
        if ctx.defers.len() <= target_depth {
            return;
        }
        let actions: Vec<_> = ctx
            .defers
            .get(target_depth..)
            .unwrap_or_default()
            .iter()
            .rev()
            .cloned()
            .collect();
        for action in actions {
            ledger.holds.truncate(action.holds_len);
            let mut defer_ctx = ctx.clone();
            defer_ctx.file = action.file;
            defer_ctx.scope = action.span;
            defer_ctx.handlers = action.handlers;
            defer_ctx.no_ctl = Some(action.span);
            defer_ctx.ctl_boundary = action.ctl_boundary;
            defer_ctx.defers.clear();
            defer_ctx.reachable = true;
            let result = self.expr(&mut defer_ctx, ledger, action.expr);
            self.discard(ledger, &result);
            self.checked_defers.insert(action.span);
        }
    }
}
