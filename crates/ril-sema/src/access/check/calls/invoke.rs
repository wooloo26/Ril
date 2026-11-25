use super::*;

impl Analyzer<'_> {
    pub(super) fn call_value(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        callee_id: ExprId,
        args: &[Argument],
        span: Span,
        id: Option<DefinitionId>,
    ) -> Datum {
        let ast = self.ast(ctx.file);
        let callee = ast.expr(callee_id);
        let def = id.map(|id| self.program.hir.definition(id));
        let name = def.map_or("", |def| def.name.value.as_str());
        let primitive = def.is_some_and(|def| matches!(def.kind, DefinitionKind::Primitive(_)));
        let module = id.and_then(|id| self.program.hir.primitive_module(id));
        let concurrent = matches!(module, Some("Fiber" | "Channel"));
        let sig = id
            .and_then(|id| self.program.callables.get(&id).map(|s| s.as_ref()))
            .or_else(|| match self.ty(callee.span) {
                Ty::Callable(sig) => Some(sig.as_ref()),
                _ => None,
            });
        let target = (id.is_none() || def.is_some_and(|def| def.kind == DefinitionKind::Local))
            .then(|| self.expr(ctx, ledger, callee_id));
        let closures = target
            .as_ref()
            .map_or_else(BTreeMap::new, |receiver| self.known_closures(receiver));
        let has_via_closures = closures
            .values()
            .any(|modes| !modes.via.is_empty() || !modes.member_axes.is_empty());
        let all_closures_known = target.as_ref().is_some_and(|target| {
            !target.roots.is_empty()
                && target
                    .roots
                    .iter()
                    .all(|root| Self::known_closure(&closures, root).is_some())
        });
        let aliases: BTreeMap<_, _> = target
            .iter()
            .flat_map(|target| &target.roots)
            .filter(|root| root.region.selection.is_empty() && root.storage_read.is_none())
            .filter_map(|root| {
                let owner = root.region.source;
                let id = self.definition(owner)?;
                if self.program.hir.definition(id).kind != DefinitionKind::Function {
                    return None;
                }
                let fun = self.function_syntax(id)?;
                // The body can be replayed without resolving a captured environment.
                ((fun.body.is_some() || self.program.imported_functions.contains_key(&id))
                    && !fun.is_meta
                    && fun
                        .signature
                        .obligations
                        .state
                        .iter()
                        .all(|clause| clause.kind != StateKind::Environment))
                .then_some((owner, (id, fun)))
            })
            .collect();
        let all_aliases_known = !aliases.is_empty()
            && target.as_ref().is_some_and(|target| {
                target.roots.iter().all(|root| {
                    Self::known_closure(&closures, root).is_some()
                        || root.storage_read.is_none()
                            && root.region.selection.is_empty()
                            && aliases.contains_key(&root.region.source)
                })
            });
        if let Some(target) = &target {
            let requires_writer = sig.is_some_and(|sig| sig.state.iter().any(|s| s == "up"));
            if requires_writer && target.invocations.is_empty() {
                self.mutate(ctx, ledger, target, callee.span);
            } else if requires_writer && !target.writers() {
                self.error(
                    Code::E0520,
                    callee.span,
                    "callable requires a writable path",
                );
            }
            self.invoke_callable_obligations(ctx, ledger, target, span);
        }
        let syntax = id.and_then(|id| self.function_syntax(id));
        let indirect_template = target.as_ref().is_some_and(|target| {
            target.roots.iter().any(|root| {
                ctx.formals.contains(&Some(root.region.source))
                    || root.region.selection.is_empty()
                        && self.definition(root.region.source).is_some_and(|id| {
                            self.program.hir.definition(id).kind == DefinitionKind::Function
                        })
            })
        });
        let is_constructor = def.is_some_and(data_constructor);
        let mut given = vec![false; sig.map_or(args.len(), |signature| signature.parameters.len())];
        let mut values = Vec::new();
        let mut value_spans = Vec::new();
        let mut choices = Vec::new();
        let refining_assert = primitive
            && name == "assert"
            && args
                .get(1)
                .is_none_or(|arg| matches!(ast.expr(arg.value).value, Expr::Literal(_)));
        for (position, arg) in args.iter().enumerate() {
            let node = ast.expr(arg.value);
            let value = if matches!(node.value, Expr::Closure { .. }) {
                self.closure(ctx, ledger, arg.value, true)
            } else if refining_assert && position == 0 {
                self.expr_with_truth(ctx, ledger, arg.value, Some(true))
            } else {
                self.expr(ctx, ledger, arg.value)
            };
            let Some(index) = arg
                .name
                .as_ref()
                .and_then(|name| {
                    sig.and_then(|sig| {
                        sig.parameters
                            .iter()
                            .position(|p| p.label.as_deref() == Some(&name.value))
                    })
                })
                .or_else(|| given.iter().position(|given| !given))
            else {
                continue;
            };
            if let Some(given) = given.get_mut(index) {
                *given = true;
            }
            let parameter = sig.and_then(|sig| sig.parameters.get(index));
            let inferred = parameter.is_some_and(|p| p.mode == Mode::Via);
            let mode = if inferred {
                let mode = match arg.mode {
                    Mode::Plain if value.requires_new => Mode::New,
                    Mode::Plain
                        if (syntax.is_some_and(|fun| fun.body.is_some())
                            || (primitive && name != "derive")
                            || id.is_some_and(|id| {
                                self.program.imported_functions.contains_key(&id)
                            })
                            || has_via_closures
                            || all_aliases_known
                            || indirect_template)
                            && Self::forwards_via(ctx, &value) =>
                    {
                        Mode::Via
                    }
                    Mode::Plain
                        if indirect_template
                            && !value.roots.is_empty()
                            && value.roots.iter().all(|root| root.inherits_mode) =>
                    {
                        Mode::Via
                    }
                    mode => mode,
                };
                if mode != Mode::Via {
                    choices.push((
                        index,
                        Input::from_mode(mode).unwrap_or(Input::Plain),
                        node.span,
                    ));
                }
                mode
            } else {
                parameter.map_or(arg.mode, |p| p.mode)
            };
            let mut value = value;
            let movable_task = concurrent && matches!(name, "join" | "cancel") && index == 1;
            let channel_payload = module == Some("Channel")
                && matches!(name, "send" | "try_send")
                && index == 1
                && !self.ty(node.span).is_value();
            if channel_payload
                && ledger
                    .loop_snapshot(&value)
                    .origins()
                    .any(|origin| !origin.new)
            {
                self.error(
                    Code::E0548,
                    node.span,
                    "channel payload requires a complete new graph",
                );
            }
            if movable_task {
                if mode == Mode::New {
                    value.transform(&mut |origin| {
                        origin.confined = None;
                    });
                } else if value.writers() {
                    self.error(
                        Code::E0535,
                        node.span,
                        "exclusive task handles require a new handoff",
                    );
                }
                ledger.inspect(&value);
            }
            let mode = if channel_payload { Mode::New } else { mode };
            let value = if primitive && name == "derive" && index == 0 {
                let mut snapshot = ledger.snapshot(&value);
                let message = "derive requires an immutable snapshot";
                if mode != Mode::Plain {
                    self.error(Code::E0536, node.span, message);
                } else {
                    self.require_snapshot(
                        (ctx, ledger),
                        &snapshot,
                        Code::E0536,
                        node.span,
                        message,
                    );
                }
                snapshot.freeze();
                snapshot
            } else {
                self.prepare_argument(ctx, ledger, arg, value, node.span, mode)
            };
            // Packing preserves inspection obligations in the payload.
            if !is_constructor {
                if parameter.is_some_and(|p| p.ty.is_result()) {
                    ledger.inspect(&value);
                } else if !value.results().is_empty()
                    && (!primitive
                        || !matches!(
                            name,
                            "inner" | "len" | "join" | "cancel" | "send" | "try_send"
                        ))
                {
                    self.discard(ledger, &value);
                }
            }
            if parameter.is_some_and(|p| p.is_meta) && !ctx.shadow {
                ledger.inspect(&value);
            }
            for (_, _, previous) in &values {
                self.check_live(
                    ctx,
                    ledger,
                    previous,
                    node.span,
                    "argument handoff ended an earlier argument path",
                );
            }
            values.push((index, mode, value));
            value_spans.push(node.span);
        }
        // Constructors store identities. Materialize the argument graph for
        // overlap checks, but keep the original edges in the constructed value.
        let fields = is_constructor.then(|| values.clone());
        for (_, _, value) in &mut values {
            *value = ledger.snapshot(value);
        }
        self.check_capture_overlap(
            ctx,
            syntax,
            target.as_ref(),
            &CallEntry {
                arguments: &values,
                spans: &value_spans,
                ledger,
                span,
                invocation: &[],
                environment: None,
            },
        );
        for (i, ((_, mode, value), &argument_span)) in values.iter().zip(&value_spans).enumerate() {
            for conflict in ledger.hold_conflicts(value, *mode) {
                self.check_conflict(
                    ctx,
                    conflict,
                    None,
                    argument_span,
                    "argument authority overlaps an active handler hold",
                );
            }
            for (_, previous_mode, previous) in values.iter().take(i) {
                for conflict in conflicts(value, *mode, previous, *previous_mode) {
                    self.check_conflict(
                        ctx,
                        conflict,
                        None,
                        argument_span,
                        "argument source overlaps incompatible live authority",
                    );
                }
            }
        }
        if !choices.is_empty() {
            if all_aliases_known {
                self.mode_uses
                    .extend(aliases.values().map(|&(callee, _)| ModeUse {
                        callee,
                        choices: choices.clone(),
                    }));
            } else if let Some(callee) = id {
                self.mode_uses.push(ModeUse { callee, choices });
            }
        }
        if let Some(target) = &target {
            self.check_live(
                ctx,
                ledger,
                target,
                callee.span,
                "argument handoff ended the callable path",
            );
        }
        if !all_aliases_known && let (Some(target), Some(signature)) = (&target, sig) {
            self.record_snapshot_invocation(ctx, ledger, target, (&values, &value_spans), span);
            self.record_indirect_modes(
                ctx,
                target,
                signature,
                &values,
                &value_spans,
                (span, ledger),
            );
        }
        for (&owner, modes) in &closures {
            self.record_snapshot_call(
                ctx,
                (owner, &modes.formals),
                (span, ledger),
                (&values, &value_spans),
            );
            if let Some(signature) = sig {
                self.record_callable_arguments(
                    ctx,
                    (owner, &modes.formals),
                    signature,
                    &values,
                    &value_spans,
                    (span, ledger),
                );
            }
            for ((index, mode, argument), &argument_span) in values.iter().zip(&value_spans) {
                for (_, axis) in modes
                    .member_axes
                    .iter()
                    .filter(|(position, _)| position == index)
                {
                    self.link_schema_argument(ctx, owner, axis.clone(), argument, argument_span);
                }
                if let Some(formal) = modes.formals.get(*index).copied().flatten() {
                    self.apply_closure_input(
                        ctx,
                        ledger,
                        (owner, formal),
                        (*mode, argument, argument_span),
                        (
                            modes.via.contains(&formal),
                            (all_closures_known || all_aliases_known) && modes.models_publication,
                        ),
                    );
                }
            }
        }
        if let Some(fields) = fields {
            let mut result = constructor(span, fields);
            if matches!(self.ty(span), Ty::Option(_) | Ty::Result(_, _))
                || def.is_some_and(|def| matches!(def.kind, DefinitionKind::Variant(_)))
            {
                result.set_variant(name);
            }
            return result;
        }
        if let Some(module @ ("Fiber" | "Channel")) = module {
            return self.concurrent(ctx, ledger, (module, name, sig), &values, args, span);
        }
        if primitive {
            let inserted = match (module, name) {
                (Some("Array"), "push") | (Some("Set"), "insert") => Some(1),
                (Some("Array" | "Map"), "insert") => Some(2),
                _ => None,
            };
            if let Some(inserted) = inserted
                && let Some(((.., mode, value), &value_span)) = values
                    .iter()
                    .zip(&value_spans)
                    .find(|((index, _, _), _)| *index == inserted)
            {
                self.check_stored_views(value, *mode == Mode::Ref, value_span);
                if let Some(((.., target), &target_span)) = values
                    .iter()
                    .zip(&value_spans)
                    .find(|((index, ..), _)| *index == 0)
                {
                    self.check_draft_insertion(ctx, ledger, target, value, value_span);
                    if module == Some("Array") && name == "push" {
                        self.mutate(ctx, ledger, target, span);
                        if ctx.reachable
                            && let Some(member) =
                                self.schema_member(self.ty(target_span), &Coordinate::Dynamic)
                            && crate::access::check::higher_order::carries_callable(
                                self.program,
                                &member.ty,
                            )
                        {
                            let coordinate = ledger.append_coordinate(target, true);
                            let place = target.slot_projection(coordinate);
                            self.store_member(
                                (ctx, ledger),
                                &place,
                                value.clone(),
                                Access::from_mode(member.mode.mode),
                                value_span,
                            );
                        }
                        return Datum::default();
                    }
                }
            }
            return self.primitive(ctx, ledger, (name, sig), &values, args, span);
        }
        if let (Some(id), Expr::Path(path)) = (id, &callee.value)
            && let Some(operation) = self.operation(id, path.span)
        {
            self.use_effect(
                ctx,
                ledger,
                Obligation::Operation(operation.clone()),
                span,
                None,
            );
            if let Some(handler) = ctx.handlers.get(&operation) {
                let closures = self.known_closures(handler);
                let entry = CallEntry {
                    arguments: &values,
                    spans: &value_spans,
                    ledger,
                    span,
                    invocation: &[],
                    environment: None,
                };
                if let Some(after) = self.closure_storage(ctx, &closures, handler, &entry, false) {
                    *ledger = after;
                }
            }
        }
        if syntax.is_none()
            && !all_aliases_known
            && let Some(sig) = sig
        {
            self.charge_call_effects(ctx, ledger, sig, None, span);
            if sig.open_effects
                && !ctx.shadow
                && let Ty::Callable(actual) = self.ty(callee.span)
            {
                for effect in &actual.effects {
                    self.effect(ctx, ledger, effect, span);
                }
            }
        }
        if let Some(fun) = syntax {
            return self.named_call(ctx, ledger, fun, sig, (&values, &value_spans), (span, &[]));
        }
        let carries_callable =
            crate::access::check::higher_order::carries_callable(self.program, self.ty(span));
        if all_aliases_known && let Some(receiver) = &target {
            let before = ledger.clone();
            let mut alternatives = Vec::new();
            let mut outputs = Vec::new();
            for &(id, fun) in aliases.values() {
                let mut after = before.clone();
                let actual = self
                    .program
                    .callables
                    .get(&id)
                    .map(|signature| signature.as_ref());
                let mut result = self.named_call(
                    ctx,
                    &mut after,
                    fun,
                    actual,
                    (&values, &value_spans),
                    (span, &[]),
                );
                if !after.no_continuation {
                    if sig.is_some_and(|signature| signature.result_mode == Mode::Plain)
                        && fun.signature.result_mode == Mode::New
                    {
                        if carries_callable {
                            self.freeze_value(ctx, &after, &mut result, span);
                        } else {
                            result = self.snapshot_value(span);
                        }
                    }
                    outputs.push(result);
                    alternatives.push(after);
                }
            }
            if !closures.is_empty() {
                let entry = CallEntry {
                    arguments: &values,
                    spans: &value_spans,
                    ledger: &before,
                    span,
                    invocation: &[],
                    environment: None,
                };
                let mut receiver = receiver.clone();
                receiver
                    .roots
                    .retain(|root| Self::known_closure(&closures, root).is_some());
                let after = self
                    .closure_storage(ctx, &closures, &receiver, &entry, false)
                    .unwrap_or_else(|| before.clone());
                let observed = before.with_storage_samples(&after);
                let entry = CallEntry {
                    ledger: &observed,
                    ..entry
                };
                let mut result = self
                    .callback_return(&receiver, &entry)
                    .unwrap_or_else(|| self.snapshot_value(span));
                if sig.is_some_and(|signature| signature.result_mode == Mode::Plain)
                    && result.requires_new
                {
                    if carries_callable {
                        self.freeze_value(ctx, &before, &mut result, span);
                    } else {
                        result = self.snapshot_value(span);
                    }
                }
                outputs.push(result);
                alternatives.push(after);
            }
            ledger.merge(&before, &alternatives);
            return outputs
                .into_iter()
                .reduce(Datum::joined)
                .unwrap_or_default();
        }
        let before_updates = if let Some(receiver) = &target {
            self.closure_storage(
                ctx,
                &closures,
                receiver,
                &CallEntry {
                    arguments: &values,
                    spans: &value_spans,
                    ledger,
                    span,
                    invocation: &[],
                    environment: None,
                },
                sig.is_some_and(|signature| {
                    signature.open_state
                        || signature
                            .state
                            .iter()
                            .any(|state| matches!(state.as_str(), "mut" | "^mut" | "up"))
                }) || receiver
                    .roots
                    .iter()
                    .any(|root| root.storage_read.is_some()),
            )
        } else {
            None
        }
        .map(|after| {
            std::mem::replace(ledger, after)
                .with_storage_samples(ledger)
                .into_owned()
        });
        if (has_via_closures || carries_callable)
            && all_closures_known
            && let Some(target) = &target
        {
            let entry = CallEntry {
                arguments: &values,
                spans: &value_spans,
                ledger: before_updates.as_ref().unwrap_or(ledger),
                span,
                invocation: &[],
                environment: None,
            };
            if let Some(result) = self.callback_return(target, &entry) {
                return result;
            }
        }
        if let Some(sig) = sig {
            if sig.state.iter().any(|state| state == "mut") {
                for (_, mode, value) in &values {
                    if matches!(mode, Mode::Mut | Mode::Shared) {
                        self.mutate(ctx, ledger, value, span);
                    }
                }
            }
            if (sig.result_mode == Mode::Infer || carries_callable)
                && let Some(receiver) = target
                && !receiver.roots.is_empty()
                && !self.ty(span).is_value()
            {
                let entry = CallEntry {
                    arguments: &values,
                    spans: &value_spans,
                    ledger: before_updates.as_ref().unwrap_or(ledger),
                    span,
                    invocation: &[],
                    environment: None,
                };
                if let Some(result) = self.callback_return(&receiver, &entry) {
                    return result;
                }
                let mut result = self.defer_callback_result(
                    CallbackResult {
                        receiver,
                        arguments: values,
                        spans: value_spans,
                        site: vec![InvocationSite { span, ordinal: 0 }],
                        ordinal: 0,
                    },
                    span,
                );
                match sig.result_mode {
                    Mode::Plain => result.freeze(),
                    Mode::New => {
                        for root in &mut result.roots {
                            root.mode = Access::Mut;
                            root.new = true;
                        }
                        result.requires_new = true;
                    }
                    Mode::Ref | Mode::Shared => {
                        for root in &mut result.roots {
                            root.fix_mode(Access::from_mode(sig.result_mode));
                        }
                    }
                    _ => {}
                }
                return result;
            }
            if sig.result_mode == Mode::New {
                return Datum::source(span, Access::Mut, true);
            }
        }
        self.snapshot_value(span)
    }
}
