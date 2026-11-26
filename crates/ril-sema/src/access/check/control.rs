use super::*;

impl Analyzer<'_> {
    pub(super) fn bind(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        id: PatternId,
        storage: &Storage,
        mut value: Datum,
        site: BindingSite,
    ) {
        let resource = site == BindingSite::Resource;
        let node = self.ast(ctx.file).pattern(id);
        match &node.value {
            Pattern::Binding(own, name) => {
                self.check_resource_binding(name.span, &value, resource);
                let binding = self
                    .definition(name.span)
                    .unwrap_or_else(|| ril_source::ice!("unresolved binding pattern"));
                let declaration = self.program.hir.definition(binding).name.span;
                if ctx.in_function {
                    self.binding_scopes.insert(declaration, ctx.scope);
                }
                let mode = if own.mode == Mode::Plain {
                    storage.mode
                } else {
                    own.mode
                };
                let variable = own.variable || storage.variable;
                let access = if resource && mode != Mode::Mut {
                    Access::Ref
                } else {
                    Access::from_mode(mode)
                };
                if variable {
                    self.requirement(
                        ctx,
                        name.span,
                        Obligation::Replace(declaration),
                        "var requires reachable slot replacement",
                    );
                }
                if matches!(mode, Mode::Mut | Mode::Shared) {
                    self.require_schema(ctx, &value, SchemaRequirement::Writable);
                    self.requirement(
                        ctx,
                        name.span,
                        Obligation::Write(declaration),
                        "writable binding requires reachable use",
                    );
                }
                match mode {
                    Mode::Mut if site == BindingSite::Declaration => {
                        self.check_exclusive_reception(&value, name.span);
                    }
                    Mode::Mut if !value.requires_new && !value.writers() => self.error(
                        Code::E0520,
                        name.span,
                        "binding cannot manufacture write authority",
                    ),
                    Mode::Shared => self.require_shared_local(ctx, declaration, &value),
                    Mode::Ref if !resource => {
                        self.check_ref_binding(name.span, &value, variable);
                        if variable {
                            self.check_ref_scope(name.span, &value, ctx.scope);
                        }
                    }
                    Mode::Via if ctx.via.is_empty() && !ctx.member_via => {
                        self.error(Code::E0412, name.span, "let via requires a mode template");
                    }
                    Mode::Via
                        if !value.origins().any(|origin| {
                            origin.inherits_mode
                                || origin
                                    .callback_result
                                    .is_some_and(|result| result.cap.is_none())
                                || !origin.reception.is_empty()
                        }) =>
                    {
                        self.error(
                            Code::E0550,
                            name.span,
                            "let via requires mode-dependent provenance",
                        );
                    }
                    _ => {}
                }
                if let Some(ty) = self.program.bindings.get(&binding) {
                    if ty.is_value() && matches!(mode, Mode::Mut | Mode::Shared | Mode::Ref) {
                        self.error(
                            Code::E0402,
                            name.span,
                            "value-type binding cannot carry live access",
                        );
                    } else if matches!(ty, Ty::Adt(adt) if adt.kind == AdtKind::Foreign) && variable
                    {
                        self.error(
                            Code::E0532,
                            name.span,
                            "foreign handle cannot be stored in a reassignable slot",
                        );
                    } else if matches!(ty, Ty::Adt(adt) if adt.kind == AdtKind::Foreign)
                        && mode == Mode::Plain
                        && !resource
                    {
                        self.error(Code::E0535, name.span, "foreign handle cannot be frozen");
                    }
                }
                if mode == Mode::Plain && !resource {
                    self.freeze_value(ctx, ledger, &mut value, name.span);
                } else if mode != Mode::Via {
                    value.receive_binding(access);
                } else {
                    value.forget_collection_layout();
                }
                value.transform(&mut |origin| {
                    origin.dependencies.insert(declaration.into());
                });
                ledger.stamp(&mut value);
                ledger.slots.insert(
                    declaration,
                    Slot {
                        decl: declaration,
                        variable,
                        mode,
                        value,
                    },
                );
            }
            Pattern::Wildcard => {
                if resource && storage.mode == Mode::Mut {
                    self.error(
                        Code::E0527,
                        node.span,
                        "use mut _ cannot use write authority",
                    );
                }
                self.discard(ledger, &value);
            }
            Pattern::Tuple(items) => {
                for (i, &item) in items.iter().enumerate() {
                    let coordinate = Coordinate::Index(i.to_string());
                    let mode = self.schema_mode(self.ty(node.span), &coordinate).0;
                    let span = self.ast(ctx.file).pattern(item).span;
                    let child =
                        self.project_observed(ctx, ledger, &value, (coordinate, mode, span));
                    if let Pattern::Binding(own, name) = &self.ast(ctx.file).pattern(item).value {
                        let requested = if own.mode == Mode::Plain {
                            storage.mode
                        } else {
                            own.mode
                        };
                        let member_mode = Access::from_mode(mode);
                        if matches!(requested, Mode::Mut | Mode::Shared)
                            && mode != Mode::Via
                            && !member_mode.writes()
                            && !child.origins().any(|origin| origin.draft)
                        {
                            self.error(
                                Code::E0551,
                                name.span,
                                "tuple slot cannot decompose with writable authority",
                            );
                        }
                    }
                    self.bind(ctx, ledger, item, storage, child, site);
                }
            }
            Pattern::Slice { text, elements } => {
                let ast = self.ast(ctx.file);
                let (before, rest, after) = ast.slice_parts(elements);
                let mode = self.schema_mode(self.ty(node.span), &Coordinate::Dynamic).0;
                for (index, &item) in before.iter().enumerate() {
                    let child = self.project_observed(
                        ctx,
                        ledger,
                        &value,
                        (
                            Coordinate::Index(index.to_string()),
                            mode,
                            ast.pattern(item).span,
                        ),
                    );
                    self.bind(ctx, ledger, item, storage, child, site);
                }
                for &item in after {
                    let child = self.project_observed(
                        ctx,
                        ledger,
                        &value,
                        (Coordinate::Dynamic, mode, ast.pattern(item).span),
                    );
                    self.bind(ctx, ledger, item, storage, child, site);
                }
                if let Some(rest) = rest
                    && let Pattern::Rest(Some(name)) = &ast.pattern(rest).value
                {
                    let decl = self.declaration(name.span).unwrap_or(name.span);
                    if ctx.in_function {
                        self.binding_scopes.insert(decl, ctx.scope);
                    }
                    let mut slice = if let Ty::Array(element) = self.ty(node.span) {
                        let end = self
                            .slice_source_length(ledger, &value)
                            .and_then(|len| len.checked_sub(after.len()));
                        self.array_slice(
                            ctx,
                            ledger,
                            &value,
                            element,
                            (Some(before.len()), end),
                            ast.pattern(rest).span,
                        )
                    } else {
                        Datum::default()
                    };
                    self.check_resource_binding(name.span, &slice, resource);
                    slice.transform(&mut |origin| {
                        origin.dependencies.insert(decl.into());
                    });
                    ledger.slots.insert(
                        decl,
                        Slot {
                            decl,
                            variable: false,
                            mode: if *text { Mode::Plain } else { Mode::New },
                            value: slice,
                        },
                    );
                }
            }
            Pattern::Constructor(path, payload) => {
                let items = payload.as_deref().unwrap_or(&[]);
                if self
                    .program
                    .hir
                    .resolve(path.span)
                    .and_then(Resolution::definition)
                    .is_some_and(|id| self.program.is_nominal_record(id))
                    && let [inner] = items
                {
                    self.bind(ctx, ledger, *inner, storage, value, site);
                    return;
                }
                for (i, &item) in items.iter().enumerate() {
                    let child = self.project_observed(
                        ctx,
                        ledger,
                        &value,
                        (
                            Coordinate::Index(i.to_string()),
                            Mode::Plain,
                            self.ast(ctx.file).pattern(item).span,
                        ),
                    );
                    if items.len() > 1
                        && let Pattern::Binding(own, name) = &self.ast(ctx.file).pattern(item).value
                    {
                        let requested = if own.mode == Mode::Plain {
                            storage.mode
                        } else {
                            own.mode
                        };
                        if matches!(requested, Mode::Mut | Mode::Shared)
                            && !child.origins().any(|origin| origin.draft)
                        {
                            self.error(
                                Code::E0551,
                                name.span,
                                "variant payload slot cannot decompose with writable authority",
                            );
                        }
                    }
                    self.bind(ctx, ledger, item, storage, child, site);
                }
            }
            Pattern::Record { fields, .. } => {
                for field in fields {
                    let coordinate = Coordinate::Field(field.name.value.clone());
                    let mode = self.schema_mode(self.ty(node.span), &coordinate).0;
                    let member_mode = Access::from_mode(mode);
                    let span = field.pattern.map_or(field.name.span, |item| {
                        self.ast(ctx.file).pattern(item).span
                    });
                    let child =
                        self.project_observed(ctx, ledger, &value, (coordinate, mode, span));
                    let mut received = field.storage.clone();
                    if received.mode == Mode::Plain {
                        received.mode = storage.mode;
                    }
                    let requested = field
                        .pattern
                        .and_then(|id| match &self.ast(ctx.file).pattern(id).value {
                            Pattern::Binding(binding, _) if binding.mode != Mode::Plain => {
                                Some(binding.mode)
                            }
                            _ => None,
                        })
                        .unwrap_or(received.mode);
                    if matches!(requested, Mode::Mut | Mode::Shared)
                        && !(child.writers()
                            && (member_mode.writes() || child.origins().any(|origin| origin.draft)))
                    {
                        self.error(
                            Code::E0521,
                            field.name.span,
                            "pattern field cannot receive writable authority",
                        );
                    }
                    if let Some(pattern) = field.pattern {
                        if field.storage.mode == Mode::Via {
                            self.check_via_pattern(ctx, pattern, Mode::Via);
                        }
                        self.bind(ctx, ledger, pattern, &received, child, site);
                    } else {
                        let mut child = child;
                        let decl = self.declaration(field.name.span).unwrap_or(field.name.span);
                        if requested == Mode::Via {
                            if ctx.via.is_empty() && !ctx.member_via {
                                self.error(
                                    Code::E0412,
                                    field.name.span,
                                    "let via requires a mode template",
                                );
                            } else if !child.origins().any(|origin| {
                                origin.inherits_mode
                                    || origin
                                        .callback_result
                                        .is_some_and(|result| result.cap.is_none())
                                    || !origin.reception.is_empty()
                            }) {
                                self.error(
                                    Code::E0550,
                                    field.name.span,
                                    "let via requires mode-dependent provenance",
                                );
                            } else {
                                child.forget_collection_layout();
                            }
                        }
                        if child.writers() {
                            match requested {
                                Mode::Mut if site == BindingSite::Declaration => {
                                    self.check_exclusive_reception(&child, decl);
                                }
                                Mode::Shared => self.require_shared_local(ctx, decl, &child),
                                _ => {}
                            }
                        }
                        if ctx.in_function {
                            self.binding_scopes.insert(decl, ctx.scope);
                        }
                        self.check_resource_binding(field.name.span, &child, resource);
                        child.transform(&mut |origin| {
                            origin.dependencies.insert(decl.into());
                        });
                        ledger.slots.insert(
                            decl,
                            Slot {
                                decl,
                                variable: received.variable,
                                mode: requested,
                                value: child,
                            },
                        );
                    }
                }
            }
            Pattern::Or(items) => {
                let mut alternatives = Vec::new();
                for (index, &item) in items.iter().enumerate() {
                    let mut branch = ledger.clone();
                    branch.take_choice(node.span, index);
                    let mut value = value.clone();
                    branch.stamp(&mut value);
                    self.bind(ctx, &mut branch, item, storage, value, site);
                    alternatives.push(branch);
                }
                ledger.merge_bindings(&alternatives);
            }
            Pattern::Subset {
                binding: Some(id), ..
            } => self.bind(ctx, ledger, *id, storage, value, site),
            _ => {}
        }
    }

    pub(super) fn pattern_has_binding(ast: &Ast, id: PatternId) -> bool {
        match &ast.pattern(id).value {
            Pattern::Binding(..) | Pattern::Rest(Some(_)) => true,
            Pattern::Wildcard
            | Pattern::Unit
            | Pattern::Literal(_)
            | Pattern::Range { .. }
            | Pattern::Type(_)
            | Pattern::TypeBinding(_)
            | Pattern::Rest(None) => false,
            Pattern::Tuple(items) | Pattern::Slice { elements: items, .. } | Pattern::Or(items) => {
                items.iter().any(|&item| Self::pattern_has_binding(ast, item))
            }
            Pattern::Constructor(_, payload) => payload
                .as_deref()
                .unwrap_or(&[])
                .iter()
                .any(|&item| Self::pattern_has_binding(ast, item)),
            Pattern::Record { fields, .. } => fields
                .iter()
                .any(|field| field.pattern.is_none_or(|p| Self::pattern_has_binding(ast, p))),
            Pattern::Subset { binding, .. } => {
                binding.is_some_and(|p| Self::pattern_has_binding(ast, p))
            }
        }
    }

    pub(super) fn check_via_pattern(&mut self, ctx: &Context, id: PatternId, mode: Mode) {
        if mode != Mode::Via {
            return;
        }
        let ast = self.ast(ctx.file);
        if !Self::pattern_has_binding(ast, id) {
            let span = ast.pattern(id).span;
            if ctx.via.is_empty() && !ctx.member_via {
                self.error(Code::E0412, span, "via pattern requires a mode template");
            } else {
                self.error(
                    Code::E0550,
                    span,
                    "via is redundant on a pattern that introduces no bindings",
                );
            }
        }
    }

    pub(super) fn match_value(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        mode: Mode,
        value: &Datum,
        arms: &[MatchArm],
        span: Span,
    ) -> Datum {
        let ast = self.ast(ctx.file);
        if mode == Mode::Via
            && !arms
                .iter()
                .any(|arm| Self::pattern_has_binding(ast, arm.pattern))
        {
            if ctx.via.is_empty() && !ctx.member_via {
                self.error(Code::E0412, span, "match via requires a mode template");
            } else {
                self.error(
                    Code::E0550,
                    span,
                    "via is redundant on a match that introduces no bindings",
                );
            }
        }
        let before = ledger.clone();
        let mut missed = Some(BTreeSet::new());
        let mut alternatives = Vec::new();
        let mut output = None;
        for (index, arm) in arms.iter().enumerate() {
            let Some(prefix) = missed else { break };
            let tests = self
                .pattern_tests(ctx, &before, arm.pattern, value)
                .after(&prefix);
            missed = tests.missed;
            let Some(inspected) = tests.matched else {
                continue;
            };
            let mut inside = before.clone();
            inside.mark_inspected(inspected);
            inside.take_choice(span, index);
            let mut local_ctx = ctx.clone();
            local_ctx.scope = ast.pattern(arm.pattern).span.join(ast.expr(arm.body).span);
            let storage = Storage {
                mode,
                ..Storage::default()
            };
            self.bind(
                &local_ctx,
                &mut inside,
                arm.pattern,
                &storage,
                value.clone(),
                BindingSite::ScopedPattern,
            );
            if let Some(guard) = arm.guard {
                self.expr(&mut local_ctx, &mut inside, guard);
                let truth = self.literal_bool(&local_ctx, guard);
                if truth != Some(true) && !inside.no_continuation {
                    missed = results::alternatives(missed, Some(inside.inspected.clone()));
                }
                if truth == Some(false) {
                    continue;
                }
            }
            let body = self.expr(&mut local_ctx, &mut inside, arm.body);
            let prior = ctx.return_values.len();
            ctx.return_values
                .extend(local_ctx.return_values.into_iter().skip(prior));
            if self.ty(ast.expr(arm.body).span) != &Ty::Never && !inside.no_continuation {
                output = Some(
                    output.map_or_else(|| body.clone(), |value: Datum| value.joined(body.clone())),
                );
                alternatives.push(inside);
            }
        }
        ledger.merge(&before, &alternatives);
        output.unwrap_or_default()
    }

    pub(super) fn bind_on_match(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        pattern: PatternId,
        storage: &Storage,
        value: &Datum,
        site: BindingSite,
    ) -> bool {
        let paths = self.pattern_paths(ctx, ledger, pattern, value, true);
        let alternatives = paths
            .into_iter()
            .map(|(mut path, selected)| {
                self.bind(ctx, &mut path, pattern, storage, selected, site);
                path
            })
            .collect();
        ledger.continue_at_pattern(alternatives)
    }

    pub(super) fn condition(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        condition: &Condition,
        matched: bool,
    ) -> bool {
        match condition {
            Condition::Expr(value) => {
                self.expr(ctx, ledger, *value);
            }
            Condition::Binding {
                mode,
                pattern,
                value,
            } => {
                let value = self.expr(ctx, ledger, *value);
                if matched {
                    self.check_via_pattern(ctx, *pattern, *mode);
                    return self.bind_on_match(
                        ctx,
                        ledger,
                        *pattern,
                        &Storage {
                            mode: *mode,
                            ..Storage::default()
                        },
                        &value,
                        BindingSite::ScopedPattern,
                    );
                }
                let alternatives = self
                    .pattern_paths(ctx, ledger, *pattern, &value, false)
                    .into_iter()
                    .map(|(ledger, _)| ledger)
                    .collect();
                return ledger.continue_at_pattern(alternatives);
            }
        }
        true
    }

    pub(super) fn check_loop(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        syntax: LoopSyntax,
        prepare: impl Fn(
            &mut Self,
            &mut Context,
            &mut Ledger,
            Option<usize>,
        ) -> (Option<Ledger>, Option<results::CollectionTraversal>),
    ) {
        let LoopSyntax {
            owner,
            repeated,
            body,
            extent,
            exact_elements,
        } = syntax;
        let entry = ledger.clone();
        let body_span = self.ast(ctx.file).expr(body).span;
        let falls_through = self.ty(body_span) != &Ty::Never;
        let scope = ctx.scope;
        let program = self.program;
        let local_data = |span: Span| {
            span.file == scope.file
                && span.start >= scope.start
                && span.end <= scope.end
                && program.types.get(&span).is_some_and(|ty| {
                    !matches!(
                        ty,
                        Ty::Callable(_) | Ty::Unknown | Ty::Param(_) | Ty::Infer(_)
                    )
                })
        };
        // The ledger expands paths structurally. Bound loops that keep creating
        // deeper access paths or callback compositions instead of diverging here.
        let max_passes = 64 + entry.slots.len();
        let exact = match extent {
            LoopExtent::Exact(length) if length > 0 && (exact_elements || length <= max_passes) => {
                Some(length)
            }
            _ => None,
        };
        let mut head = entry.clone();
        if exact.is_none() && extent != LoopExtent::Exact(0) {
            head.take_choice(owner, 0);
        }
        let mut exact_exits = Vec::new();
        let mut size_limit = None;
        for iteration in 1..=exact.unwrap_or(max_passes) {
            let mut inside = head.clone();
            let mut local = ctx.clone();
            local.scope = body_span;
            let index = (exact.is_some() && exact_elements).then_some(iteration - 1);
            let (mut exit, traversal) = prepare(self, &mut local, &mut inside, index);
            local.loop_owner = Some(owner);
            if local.reachable {
                self.expr(&mut local, &mut inside, body);
            }
            let LoopTransfers {
                mut breaks,
                mut continues,
            } = self.loop_transfers.remove(&owner).unwrap_or_default();
            if local.reachable && falls_through {
                continues.push(inside);
            }
            if let Some(traversal) = traversal {
                traversal.finish(&mut exit, &mut breaks, &mut continues);
            }
            if let Some(length) = exact {
                ctx.return_values = std::mem::take(&mut local.return_values);
                exact_exits.append(&mut breaks);
                if iteration == length || continues.is_empty() {
                    exact_exits.extend(continues);
                    ledger.merge(&entry, &exact_exits);
                    return;
                }
            } else {
                breaks.extend(exit);
            }
            if !continues.is_empty() {
                let final_iteration = exact.map(|_| continues.clone());
                for backedge in &mut continues {
                    backedge.loop_backedge(owner, repeated, &entry, local_data, exact.is_none());
                    backedge.take_choice(owner, 1);
                }
                if let Some(final_iteration) = final_iteration {
                    let mut next = head.clone();
                    next.merge(&entry, &continues);
                    if next == head && !exact_elements {
                        // The remaining iterations have the same incoming
                        // ledger and produce the same transfers.
                        exact_exits.extend(final_iteration);
                        ledger.merge(&entry, &exact_exits);
                        return;
                    }
                    head = next;
                    continue;
                }
                continues.push(head.clone());
                let mut next = head.clone();
                next.merge(&entry, &continues);
                if next != head {
                    let size = next.size();
                    let limit = *size_limit
                        .get_or_insert_with(|| (entry.size() + size).saturating_mul(8).max(4096));
                    if size > limit {
                        break;
                    }
                    head = next;
                    continue;
                }
            }
            ctx.return_values = local.return_values;
            ledger.merge(&entry, &breaks);
            return;
        }
        self.diagnostics.push(Diagnostic::unsupported_at(
            owner,
            "could not stabilize loop provenance",
        ));
    }

    pub(super) fn iterable_extent(&self, ctx: &Context, id: ExprId) -> LoopExtent {
        let ast = self.ast(ctx.file);
        match &ast.expr(id).value {
            Expr::Array(items) => LoopExtent::Exact(items.len()),
            Expr::Literal(value) => match ty::literal(value) {
                Ok(Value::Bytes(bytes)) => LoopExtent::Exact(bytes.len()),
                Ok(Value::Str(text)) => LoopExtent::Exact(text.chars().count()),
                _ => LoopExtent::Repeat,
            },
            Expr::Range {
                start: Some(start),
                end: Some(end),
                inclusive,
            } => {
                let int = |id| match &ast.expr(id).value {
                    Expr::Literal(value) => match ty::literal(value) {
                        Ok(Value::Int(number)) => Some(number),
                        _ => None,
                    },
                    _ => None,
                };
                let (Some(start), Some(end)) = (int(*start), int(*end)) else {
                    return LoopExtent::Repeat;
                };
                if start > end {
                    LoopExtent::Exact(0)
                } else {
                    let distance = end - start + u8::from(*inclusive);
                    usize::try_from(distance).map_or(LoopExtent::Repeat, LoopExtent::Exact)
                }
            }
            _ => LoopExtent::Repeat,
        }
    }

    pub(super) fn literal_bool(&self, ctx: &Context, id: ExprId) -> Option<bool> {
        match &self.ast(ctx.file).expr(id).value {
            Expr::Literal(value) if value.kind == LiteralKind::Bool => Some(value.text == "true"),
            Expr::Unary { op, value } if op.value == "!" => {
                self.literal_bool(ctx, *value).map(|value| !value)
            }
            _ => None,
        }
    }

    pub(super) fn result_constructor(&self, ctx: &Context, id: ExprId) -> bool {
        let ast = self.ast(ctx.file);
        let Expr::Call { callee, .. } = ast.expr(id).value else {
            return false;
        };
        matches!(&ast.expr(callee).value, Expr::Path(path) if path.segments.last().is_some_and(|s| matches!(s.name.value.as_str(), "Ok" | "Err")))
    }
}
