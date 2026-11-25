use super::*;

impl Analyzer<'_> {
    pub(super) fn statement(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        id: StmtId,
        tail: bool,
    ) -> Datum {
        let ast = self.ast(ctx.file);
        let node = ast.stmt(id);
        match &node.value.kind {
            StmtKind::Function(fun) => self.function(fun, ledger),
            StmtKind::Sub { items, .. } => {
                for &item in items {
                    self.statement(ctx, ledger, item, false);
                }
            }
            StmtKind::Binding {
                pattern,
                storage,
                ty,
                value,
                fallback,
                resource,
                ..
            } => {
                if let Some(ty) = ty {
                    self.shadow_type(ctx, ledger, *ty);
                }
                let Some(value_id) = value else {
                    return Datum::default();
                };
                let span = ast.expr(*value_id).span;
                let mut value = self.expr(ctx, ledger, *value_id);
                if let Some(adjustments) = self.program.receptions.get(&span) {
                    for adjustment in adjustments {
                        if !value.requires_new
                            || !Self::retarget(
                                &mut value,
                                &adjustment.path,
                                Access::from_mode(adjustment.mode),
                            )
                        {
                            self.error(
                                Code::E0522,
                                span,
                                "existing container members must retain their access modes",
                            );
                        }
                    }
                }
                if !ctx.reachable {
                    return Datum::default();
                }
                if *resource {
                    self.cleanup(ctx, ledger, &mut value, span, node.span, storage.mode);
                }
                let site = if *resource {
                    BindingSite::Resource
                } else {
                    BindingSite::Declaration
                };
                if let Some(fallback) = fallback {
                    for (mut failed, _) in self.pattern_paths(ctx, ledger, *pattern, &value, false)
                    {
                        let mut failure = ctx.clone();
                        self.expr(&mut failure, &mut failed, *fallback);
                        ctx.return_values = failure.return_values;
                    }
                    if !self.bind_on_match(ctx, ledger, *pattern, storage, &value, site) {
                        ledger.no_continuation = true;
                        ctx.reachable = false;
                    }
                } else {
                    self.pattern_tests(ctx, ledger, *pattern, &value)
                        .inspect(ledger, true);
                    self.bind(ctx, ledger, *pattern, storage, value, site);
                }
            }
            StmtKind::With(handlers) => self.handlers(ctx, ledger, handlers),
            StmtKind::Expr(expr) => {
                let value = self.expr(ctx, ledger, *expr);
                if tail {
                    return value;
                }
                self.discard(ledger, &value);
            }
            StmtKind::Type(decl) => {
                if let TypeDefinition::Data(ty) = decl.definition {
                    self.shadow_type(ctx, ledger, ty);
                }
            }
            StmtKind::Effect { .. } | StmtKind::Import(_) | StmtKind::Error => {}
        }
        Datum::default()
    }

    pub(super) fn expr(&mut self, ctx: &mut Context, ledger: &mut Ledger, id: ExprId) -> Datum {
        self.expr_with_truth(ctx, ledger, id, None)
    }

    pub(super) fn expr_with_truth(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        id: ExprId,
        truth: Option<bool>,
    ) -> Datum {
        let ast = self.ast(ctx.file);
        let node = ast.expr(id);
        let span = node.span;
        if let Some((base, steps)) = ast.navigation_chain(id) {
            return self.navigate(ctx, ledger, base, &steps, span);
        }
        let mut value = match &node.value {
            Expr::Path(path) => self.read(ctx, ledger, path),
            Expr::Unary { op, value } => {
                let operand_truth = if op.value == "!" {
                    truth.map(|truth| !truth)
                } else {
                    None
                };
                let mut value = self.expr_with_truth(ctx, ledger, *value, operand_truth);
                match op.value.as_str() {
                    "new" => self.handoff(ctx, ledger, &mut value, span),
                    "ref" => {
                        for root in &mut value.roots {
                            root.fix_mode(Access::Ref);
                            root.new &= value.requires_new;
                        }
                        value.requires_new = false;
                    }
                    "^mut" => {
                        if !value.writers() {
                            self.error(Code::E0520, span, "sharing requires writable authority");
                        }
                        self.require_schema(ctx, &value, SchemaRequirement::Writable);
                        for root in &mut value.roots {
                            root.new &= value.requires_new || root.explicit_share;
                            root.fix_mode(Access::Shared);
                            root.explicit_share = true;
                        }
                        value.requires_new = false;
                    }
                    "?" => {
                        value = self.propagated(ctx, ledger, value, op.span);
                    }
                    _ => value = Datum::default(),
                }
                value
            }
            Expr::Binary { op, left, right } => {
                // These predicate outcomes require both operands to be evaluated.
                let both = matches!(
                    (op.value.as_str(), truth),
                    ("&&", Some(true)) | ("||", Some(false))
                );
                let operand_truth = truth.filter(|_| both);
                let lhs = self.expr_with_truth(ctx, ledger, *left, operand_truth);
                let literal = self.literal_bool(ctx, *left);
                let skip = matches!(
                    (op.value.as_str(), literal),
                    ("&&", Some(false)) | ("||", Some(true))
                );
                let fallible = op.value == "??" && self.ty(ast.expr(*left).span).is_result();
                if fallible {
                    ledger.inspect_root(&lhs);
                }
                let optional_rhs = op.value == "??"
                    || !both && matches!((op.value.as_str(), literal), ("&&" | "||", None));
                let rhs = if skip {
                    let mut dead = ctx.clone();
                    dead.reachable = false;
                    self.expr(&mut dead, &mut ledger.clone(), *right)
                } else if optional_rhs {
                    let before = ledger.clone();
                    let mut skipped = before.clone();
                    skipped.take_choice(span, 0);
                    ledger.take_choice(span, 1);
                    let mut rhs_ctx = ctx.clone();
                    let result = if fallible {
                        self.fallback_handler(&mut rhs_ctx, ledger, *right, span)
                    } else {
                        self.expr(&mut rhs_ctx, ledger, *right)
                    };
                    ctx.return_values = rhs_ctx.return_values;
                    let mut taken = ledger.clone();
                    taken.no_continuation |= self.ty(ast.expr(*right).span) == &Ty::Never;
                    ledger.merge(&before, &[skipped, taken]);
                    result
                } else {
                    self.expr_with_truth(ctx, ledger, *right, operand_truth)
                };
                if is_assignment(&op.value) {
                    let place = self.place(ctx, ledger, *left, lhs);
                    self.write(ctx, ledger, *left, &place, rhs, span);
                    Datum::default()
                } else if op.value == "??" {
                    ledger
                        .project(&lhs, Coordinate::Index("0".into()), Access::Immutable)
                        .joined(rhs)
                } else {
                    if matches!(op.value.as_str(), "==" | "!=")
                        && (self.result_constructor(ctx, *right)
                            || self.result_constructor(ctx, *left))
                    {
                        ledger.inspect_root(&lhs);
                        ledger.inspect_root(&rhs);
                    }
                    Datum::default()
                }
            }
            Expr::Record { fields, .. } => {
                let mut record = Datum::source(span, Access::Mut, true);
                for field in fields {
                    let coordinate = Coordinate::Field(field.name.value.clone());
                    let value = if let Some(expr) = field.value {
                        self.expr(ctx, ledger, expr)
                    } else {
                        self.read_span(ctx, ledger, field.name.span)
                    };
                    let access = self.member_schema(span, &coordinate).0;
                    let value = self.receive_member(
                        ctx,
                        ledger,
                        value,
                        access,
                        field.value.map_or(field.name.span, |id| ast.expr(id).span),
                    );
                    record.members.insert(coordinate, value);
                }
                record
            }
            Expr::Tuple(items) | Expr::Array(items) => {
                let mut sequence = Datum::source(span, Access::Mut, true);
                if let Ty::Array(member) = self.ty(span) {
                    if higher_order::carries_callable(self.program, &member.ty) {
                        ledger.record_array_length(span, items.len());
                    }
                    if results::carries_result(self.program, &member.ty) {
                        sequence.array_len = Some(items.len());
                    }
                }
                for (i, &item) in items.iter().enumerate() {
                    let coordinate = Coordinate::Index(i.to_string());
                    let value = self.expr(ctx, ledger, item);
                    let access = self.member_schema(span, &coordinate).0;
                    let value =
                        self.receive_member(ctx, ledger, value, access, ast.expr(item).span);
                    sequence.members.insert(coordinate, value);
                }
                sequence
            }
            Expr::Map(entries) => {
                let mut map = Datum::source(span, Access::Mut, true);
                let keys: Option<Vec<_>> = entries
                    .iter()
                    .map(|&(id, _)| self.constant_map_key(ctx, id))
                    .collect();
                let keys = keys.or_else(|| (entries.len() == 1).then(|| vec![Coordinate::Dynamic]));
                let mut ordered_keys = Vec::new();
                for (index, &(key, value)) in entries.iter().enumerate() {
                    let mut key_value = self.expr(ctx, ledger, key);
                    if !key_value.roots.is_empty() {
                        // A later duplicate replaces the value while retaining the first key.
                        if index > 0 {
                            key_value.forget_results();
                        }
                        let key_value = self.receive_member(
                            ctx,
                            ledger,
                            key_value,
                            Access::Immutable,
                            ast.expr(key).span,
                        );
                        let slot = map.members.entry(Coordinate::MapKey).or_default();
                        *slot = std::mem::take(slot).joined(key_value);
                    }
                    let coordinate = keys
                        .as_ref()
                        .and_then(|keys| keys.get(index))
                        .cloned()
                        .unwrap_or(Coordinate::Dynamic);
                    let access = self.member_schema(span, &coordinate).0;
                    let mut datum = self.expr(ctx, ledger, value);
                    if keys.is_none() && index + 1 < entries.len() {
                        // An unknown later key may replace this occurrence.
                        datum.forget_results();
                    }
                    let datum =
                        self.receive_member(ctx, ledger, datum, access, ast.expr(value).span);
                    if keys.is_some() {
                        if map.members.insert(coordinate.clone(), datum).is_none() {
                            ordered_keys.push(coordinate);
                        }
                    } else {
                        let slot = map.members.entry(coordinate).or_default();
                        *slot = std::mem::take(slot).joined(datum);
                    }
                }
                if results::carries_result(self.program, self.ty(span)) {
                    map.map_keys = keys.map(|_| ordered_keys);
                }
                map
            }
            Expr::Member { base, member, .. } => {
                let value = self.expr(ctx, ledger, *base);
                let coordinate = self.coordinate(ctx, ledger, member);
                let (mode, variable) = self.schema_mode(self.ty(ast.expr(*base).span), &coordinate);
                let mode = if variable && self.ty(span).is_value() {
                    Mode::Mut
                } else {
                    mode
                };
                self.project_observed(ctx, ledger, &value, (coordinate, mode, span))
            }
            Expr::Index { base, index, .. } => {
                let value = self.expr(ctx, ledger, *base);
                self.expr(ctx, ledger, *index);
                let ty = self.ty(ast.expr(*base).span);
                self.project_index(ctx, ledger, &value, (ty, *index, span))
            }
            Expr::Block {
                statements,
                helpers,
            } => {
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
                let prior = ledger.slots.keys().copied().collect::<BTreeSet<_>>();
                let prior_iter = ledger.iteration.len();
                let prior_holds = ledger.holds.len();
                let mut result = Datum::default();
                for (i, &item) in statements.iter().enumerate() {
                    let is_tail = i + 1 == statements.len();
                    result = self.statement(&mut local_ctx, ledger, item, is_tail);
                    if let StmtKind::Expr(expr) = ast.stmt(item).value.kind
                        && self.ty(ast.expr(expr).span) == &Ty::Never
                    {
                        local_ctx.reachable = false;
                    }
                }
                for &helper in helpers {
                    self.statement(&mut local_ctx, ledger, helper, false);
                }
                if result.origins().any(|origin| {
                    origin
                        .confined
                        .is_some_and(|id| span.start <= id.start && id.end <= span.end)
                }) {
                    self.error(Code::E0604, span, "resource or draft escapes its block");
                }
                ledger.slots.retain(|id, _| prior.contains(id));
                ledger.iteration.truncate(prior_iter);
                ledger.holds.truncate(prior_holds);
                ctx.return_values
                    .extend(local_ctx.return_values.into_iter().skip(start_returns));
                result
            }
            Expr::If { condition, yes, no } => {
                let before = ledger.clone();
                let literal = match condition {
                    Condition::Expr(test) => self.literal_bool(ctx, *test),
                    _ => None,
                };
                let mut then_ledger = before.clone();
                then_ledger.take_choice(span, 0);
                let mut yes_ctx = ctx.clone();
                yes_ctx.scope = ast.expr(*yes).span;
                yes_ctx.reachable &= literal != Some(false);
                let takes_yes = self.condition(&mut yes_ctx, &mut then_ledger, condition, true);
                let yes_value = if takes_yes {
                    self.expr(&mut yes_ctx, &mut then_ledger, *yes)
                } else {
                    Datum::default()
                };
                let mut else_ledger = before.clone();
                else_ledger.take_choice(span, 1);
                let mut no_ctx = ctx.clone();
                no_ctx.reachable &= literal != Some(true);
                let takes_no = self.condition(&mut no_ctx, &mut else_ledger, condition, false);
                let no_value = no
                    .filter(|_| takes_no)
                    .map(|expr| self.expr(&mut no_ctx, &mut else_ledger, expr))
                    .unwrap_or_default();
                let count = ctx.return_values.len();
                ctx.return_values
                    .extend(yes_ctx.return_values.into_iter().skip(count));
                ctx.return_values
                    .extend(no_ctx.return_values.into_iter().skip(count));
                let can_yes = literal != Some(false) && self.ty(ast.expr(*yes).span) != &Ty::Never;
                let can_no = literal != Some(true)
                    && no.is_none_or(|no| self.ty(ast.expr(no).span) != &Ty::Never);
                let mut alternatives = Vec::new();
                let can_yes_continue = can_yes && takes_yes && !then_ledger.no_continuation;
                let can_no_continue = can_no && takes_no && !else_ledger.no_continuation;
                if can_yes_continue {
                    alternatives.push(then_ledger);
                }
                if can_no_continue {
                    alternatives.push(else_ledger);
                }
                ledger.merge(&before, &alternatives);
                match (can_yes_continue, can_no_continue) {
                    (true, true) => yes_value.joined(no_value),
                    (true, false) => yes_value,
                    (false, true) => no_value,
                    _ => Datum::default(),
                }
            }
            Expr::While { condition, body } => {
                let literal = match condition {
                    Condition::Expr(test) => self.literal_bool(ctx, *test),
                    Condition::Binding { .. } => None,
                };
                self.check_loop(
                    ctx,
                    ledger,
                    LoopSyntax {
                        owner: span,
                        repeated: span,
                        body: *body,
                        extent: LoopExtent::Repeat,
                        exact_elements: false,
                    },
                    |this, local, inside, _| {
                        if matches!(condition, Condition::Binding { .. }) {
                            let mut failed = inside.clone();
                            let mut failed_ctx = local.clone();
                            let exits =
                                this.condition(&mut failed_ctx, &mut failed, condition, false)
                                    && failed_ctx.reachable;
                            local.reachable &= this.condition(local, inside, condition, true);
                            (exits.then_some(failed), None)
                        } else {
                            this.condition(local, inside, condition, true);
                            let exit =
                                (literal != Some(true) && local.reachable).then(|| inside.clone());
                            local.reachable &= literal != Some(false);
                            (exit, None)
                        }
                    },
                );
                Datum::default()
            }
            Expr::For {
                iterable,
                pattern,
                body,
                mode,
            } => {
                let value = self.expr(ctx, ledger, *iterable);
                let storage = Storage {
                    mode: *mode,
                    ..Storage::default()
                };
                let iterable_type = self.ty(ast.expr(*iterable).span);
                let schema = self.schema_mode(iterable_type, &Coordinate::Dynamic).0;
                let traverse = |this: &mut Self,
                                ctx: &mut Context,
                                ledger: &mut Ledger,
                                value: Datum| {
                    let length = value
                        .array_len
                        .or_else(|| value.map_keys.as_ref().map(Vec::len));
                    let extent = length
                        .map_or_else(|| this.iterable_extent(ctx, *iterable), LoopExtent::Exact);
                    this.check_loop(
                        ctx,
                        ledger,
                        LoopSyntax {
                            owner: span,
                            repeated: ast.pattern(*pattern).span.join(ast.expr(*body).span),
                            body: *body,
                            extent,
                            exact_elements: length.is_some(),
                        },
                        |this, local, inside, index| {
                            let exit = (extent != LoopExtent::Exact(1)).then(|| inside.clone());
                            local.reachable &= extent != LoopExtent::Exact(0);
                            inside.iteration.push(value.clone());
                            let coordinate = match (&value.map_keys, index) {
                                (Some(keys), Some(index)) => {
                                    keys.get(index).cloned().unwrap_or(Coordinate::Dynamic)
                                }
                                (None, Some(index)) => Coordinate::Index(index.to_string()),
                                (_, None) => Coordinate::Dynamic,
                            };
                            let mut child = inside.project_schema(&value, coordinate, schema);
                            let pattern_span = ast.pattern(*pattern).span;
                            if let Ty::Map(key_ty, value_ty) = iterable_type {
                                let key = if key_ty.is_value() {
                                    Datum::default()
                                } else {
                                    inside.project_schema(&value, Coordinate::MapKey, Mode::Plain)
                                };
                                let mut pair = Datum::source(pattern_span, Access::Mut, true);
                                pair.members.insert(Coordinate::Index("0".into()), key);
                                pair.members.insert(
                                    Coordinate::Index("1".into()),
                                    if value_ty.ty.is_value() {
                                        Datum::default()
                                    } else {
                                        child
                                    },
                                );
                                child = pair;
                            }
                            let traversal =
                                if matches!(iterable_type, Ty::Array(_) | Ty::Map(..) | Ty::Set(_))
                                    && local.reachable
                                {
                                    results::CollectionTraversal::enter(
                                        this.program,
                                        inside,
                                        this.ty(pattern_span),
                                        &value,
                                        &mut child,
                                        pattern_span,
                                    )
                                } else {
                                    None
                                };
                            this.pattern_tests(local, inside, *pattern, &child)
                                .inspect(inside, true);
                            this.bind(
                                local,
                                inside,
                                *pattern,
                                &storage,
                                child,
                                BindingSite::ScopedPattern,
                            );
                            (exit, traversal)
                        },
                    );
                };
                let paths = ledger.iterable_result_paths(&value);
                if paths.is_empty() {
                    traverse(self, ctx, ledger, value);
                } else {
                    let before = ledger.clone();
                    let alternatives: Vec<_> = paths
                        .into_iter()
                        .map(|(mut path, selected)| {
                            traverse(self, ctx, &mut path, selected);
                            path
                        })
                        .collect();
                    ledger.merge(&before, &alternatives);
                }
                Datum::default()
            }
            Expr::Match { mode, value, arms } => {
                let value = self.expr(ctx, ledger, *value);
                let paths = ledger.variant_paths(&value);
                if paths.is_empty() {
                    self.match_value(ctx, ledger, *mode, &value, arms, span)
                } else {
                    let before = ledger.clone();
                    let mut alternatives = Vec::with_capacity(paths.len());
                    let mut output = None;
                    for (mut branch, selected) in paths {
                        let value =
                            self.match_value(ctx, &mut branch, *mode, &selected, arms, span);
                        if !branch.no_continuation {
                            output = Some(match output {
                                Some(previous) => value.joined(previous),
                                None => value,
                            });
                            alternatives.push(branch);
                        }
                    }
                    ledger.merge(&before, &alternatives);
                    output.unwrap_or_default()
                }
            }
            Expr::Call { callee, args } => self.call(ctx, ledger, *callee, args, span),
            Expr::Pipeline {
                value,
                mode,
                target,
                propagate,
            } => {
                let mut args = vec![ril_frontend::syntax::Argument {
                    value: *value,
                    mode: *mode,
                    name: None,
                }];
                let callee = if let Expr::Call { callee, args: rest } = &ast.expr(*target).value {
                    args.extend(rest.iter().cloned());
                    *callee
                } else {
                    *target
                };
                let result = self.call(ctx, ledger, callee, &args, span);
                if *propagate {
                    self.propagated(ctx, ledger, result, span)
                } else {
                    result
                }
            }
            Expr::Transfer { kind, value } => {
                let value = value
                    .map(|value| self.expr(ctx, ledger, value))
                    .unwrap_or_default();
                if ctx.reachable {
                    match kind {
                        Transfer::Return => {
                            self.returned(ctx, ledger, value, span);
                            self.check_results(ledger, &BTreeSet::new());
                        }
                        Transfer::Break | Transfer::Continue => {
                            if let Some(owner) = ctx.loop_owner {
                                let exits = self.loop_transfers.entry(owner).or_default();
                                let paths = if *kind == Transfer::Break {
                                    &mut exits.breaks
                                } else {
                                    &mut exits.continues
                                };
                                paths.push(ledger.clone());
                            }
                        }
                    }
                }
                ledger.no_continuation = true;
                Datum::default()
            }
            Expr::Closure { .. } => self.closure(ctx, ledger, id, false),
            Expr::Cast { value, .. } => self.expr(ctx, ledger, *value),
            Expr::Interpolated(parts) => {
                for part in parts {
                    if let ril_frontend::syntax::StringPart::Interpolation(expr) = part {
                        self.expr(ctx, ledger, *expr);
                    }
                }
                Datum::default()
            }
            Expr::Range { start, end, .. } => {
                for &id in start.iter().chain(end) {
                    self.expr(ctx, ledger, id);
                }
                Datum::default()
            }
            Expr::Quote(_) | Expr::Literal(_) | Expr::Unit | Expr::Accessor(_) | Expr::Hole => {
                Datum::default()
            }
        };
        ctx.reachable &= !ledger.no_continuation;
        if ctx.reachable
            && (self.ty(span).is_result()
                || matches!(self.ty(span), Ty::Task(inner) if inner.is_result()))
            && !value.has_root_result()
            && !matches!(node.value, Expr::Path(_))
        {
            ledger.record_result(&mut value, span);
        }
        if self.ty(span).is_value() {
            value.roots.clear();
            value.members.clear();
            value.requires_new = false;
        }
        if matches!(
            node.value,
            Expr::Member { .. } | Expr::Index { .. } | Expr::Call { .. } | Expr::Pipeline { .. }
        ) {
            for root in &mut value.roots {
                root.explicit_share = false;
                root.from_variable = false;
            }
        }
        ledger.stamp(&mut value);
        value
    }

    pub(super) fn read(&mut self, ctx: &Context, ledger: &Ledger, path: &Path) -> Datum {
        self.read_span(ctx, ledger, path.span)
    }

    pub(super) fn read_span(&mut self, ctx: &Context, ledger: &Ledger, span: Span) -> Datum {
        let Some(id) = self.definition(span) else {
            return Datum::default();
        };
        if self.program.meta_parameters.contains(&id) {
            return Datum::default();
        }
        let definition = self.program.hir.definition(id);
        let decl = definition.name.span;
        if let Some(slot) = ledger.slots.get(&decl) {
            self.check_live(
                ctx,
                ledger,
                &slot.value,
                span,
                "source path was ended by new handoff",
            );
            if ctx.in_function
                && decl.start < ctx.owner.start
                && !ctx.formals.contains(&Some(decl))
                && self
                    .definition(span)
                    .is_some_and(|id| self.program.hir.definition(id).kind == DefinitionKind::Local)
            {
                self.seed(ctx, Obligation::ReadUp(decl));
            }
            let mut value = slot.value.clone();
            ctx.mark_capture(slot, &mut value);
            for root in &mut value.roots {
                root.explicit_share = false;
                root.from_variable = slot.variable;
                root.anchor_scopes.clear();
                root.anchor_scopes.extend(self.binding_scopes.get(&decl));
            }
            value
        } else if self.program.hir.unit_constructor(id)
            || matches!(definition.kind, DefinitionKind::Primitive(_))
                && definition.name.value == "None"
                && matches!(self.ty(span), Ty::Option(_))
            || matches!(definition.kind, DefinitionKind::Variant(_))
                && matches!(self.ty(span), Ty::Adt(adt) if matches!(adt.kind, AdtKind::Sum | AdtKind::OpaqueSum))
        {
            let mut value = Datum::source(span, Access::Mut, true);
            value.set_variant(&definition.name.value);
            value
        } else if !self.ty(span).is_value()
            && matches!(
                self.program.hir.definition(id).kind,
                DefinitionKind::Constant | DefinitionKind::Function
            )
        {
            let mut value = Datum::source(decl, Access::Immutable, false);
            if definition.kind == DefinitionKind::Function {
                for root in &mut value.roots {
                    root.snapshot_provider = Some(decl);
                }
                value.live_callable_state = self.named_value_has_live_state(id, ctx, ledger);
            }
            value
        } else {
            Datum::default()
        }
    }
}
