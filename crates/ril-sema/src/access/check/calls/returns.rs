use super::*;

impl Analyzer<'_> {
    pub(super) fn instantiate_return(
        &mut self,
        formals: &[Option<Span>],
        via_formals: &BTreeSet<Span>,
        entry: &CallEntry<'_>,
        template: &Datum,
        output_path: &mut Vec<Coordinate>,
    ) -> Datum {
        let mut captured = None;
        if let Some(environment) = entry.environment
            && !template
                .roots
                .iter()
                .any(|root| root.detached_snapshot || root.storage_read.is_some())
        {
            for (path, &definite) in &template.capture_paths {
                if path.owner != environment.owner {
                    continue;
                }
                if let Some((base, ty)) = self.capture_binding(entry, path.region.source) {
                    let mut value =
                        self.project_entry_path(entry.ledger, base, ty, &path.region.selection);
                    let access = template
                        .roots
                        .iter()
                        .map(|root| root.mode)
                        .max()
                        .unwrap_or(Access::Immutable);
                    value.transform(&mut |origin| {
                        origin.fix_mode(access.project(origin.mode));
                        origin.new &= template.requires_new;
                    });
                    value.requires_new &= template.requires_new;
                    if definite {
                        return value;
                    }
                    captured = Some(match captured {
                        Some(previous) => value.joined(previous),
                        None => value,
                    });
                }
            }
        }
        let mut sampled = 0;
        let mut output = template
            .roots
            .iter()
            .filter_map(|origin| {
                if let Some(read) = &origin.storage_read {
                    if let Some(mut value) = entry
                        .ledger
                        .sampled_storage((entry.span, entry.invocation), read)
                    {
                        value.transform(&mut |projected| {
                            projected.fix_mode(origin.mode.project(projected.mode));
                            projected.new &= origin.new;
                        });
                        value.requires_new &= template.requires_new;
                        sampled += 1;
                        return Some(value);
                    }
                    return Some(Datum {
                        roots: vec![origin.clone()],
                        requires_new: template.requires_new,
                        ..Datum::default()
                    });
                }
                if let Some(result) = origin.callback_result
                    && self.resolving_callback_results.insert(result.template)
                {
                    let (mut value, callback_ledger) = self.instantiate_callback_result(
                        result.template,
                        formals,
                        via_formals,
                        entry,
                    );
                    self.resolving_callback_results.remove(&result.template);
                    let mut ty = self.ty(origin.region.source).clone();
                    for step in &origin.region.selection {
                        let member = self.schema_member(&ty, step);
                        let mode = member
                            .as_ref()
                            .map_or(Mode::Plain, |member| member.mode.mode);
                        value = callback_ledger.project_schema(&value, step.clone(), mode);
                        ty = member.map_or(Ty::Unknown, |member| member.ty);
                    }
                    if let Some(cap) = result.cap {
                        for root in &mut value.roots {
                            root.fix_mode(cap.project(root.mode));
                            root.new = false;
                        }
                        value.requires_new = false;
                    }
                    return Some(match callback_ledger {
                        Cow::Owned(ledger) => ledger.snapshot(&value),
                        Cow::Borrowed(_) => value,
                    });
                }
                let formal = formals
                    .iter()
                    .position(|formal| *formal == Some(origin.region.source));
                if let Some(index) = formal {
                    let ((_, receiver, actual), &argument_span) = entry
                        .arguments
                        .iter()
                        .zip(entry.spans)
                        .find(|((position, ..), _)| *position == index)?;
                    let via = via_formals.contains(&origin.region.source);
                    let mut actual = actual.clone();
                    if via && *receiver != Mode::Via {
                        for root in &mut actual.roots {
                            root.fix_mode(Access::from_mode(*receiver));
                        }
                    }
                    if origin.reception.is_empty() {
                        for (index, coordinate) in origin.region.selection.iter().enumerate() {
                            let cap = if index + 1 == origin.region.selection.len() {
                                origin.mode
                            } else {
                                Access::Mut
                            };
                            actual = entry.ledger.project(&actual, coordinate.clone(), cap);
                        }
                    } else {
                        let mut ty = self.ty(argument_span).clone();
                        for coordinate in &origin.region.selection {
                            let member = self.schema_member(&ty, coordinate);
                            let mode = member
                                .as_ref()
                                .map_or(Mode::Plain, |member| member.mode.mode);
                            actual = entry
                                .ledger
                                .project_schema(&actual, coordinate.clone(), mode);
                            ty = member.map_or(Ty::Unknown, |member| member.ty);
                        }
                        for projected in &mut actual.roots {
                            if !origin.mode.writes() {
                                projected.project_mode(origin.mode.as_mode());
                            }
                            projected.new &= origin.new;
                        }
                        actual.requires_new &= origin.new;
                    }
                    if via && origin.new {
                        actual.detach_handed_off_paths();
                    } else if via
                        && origin.region.selection.is_empty()
                        && origin.mode != Access::Mut
                    {
                        actual.transform(&mut |member| {
                            member.fix_mode(origin.mode.project(member.mode));
                            member.new = false;
                        });
                        actual.requires_new = false;
                    } else if !via && origin.reception.is_empty() {
                        actual.transform(&mut |member| {
                            member.fix_mode(member.mode.project(origin.mode));
                            member.new &= origin.new;
                        });
                        actual.requires_new &= origin.new;
                    }
                    if origin.call_scoped_access {
                        for root in &mut actual.roots {
                            root.call_scoped_access |= root.mode.writes();
                        }
                    }
                    if origin.detached_snapshot {
                        actual.transform(&mut |root| {
                            root.detached_snapshot = true;
                        });
                    }
                    Some(actual)
                } else {
                    let mut mapped = origin.clone();
                    mapped.branches.clear();
                    if mapped.new || mapped.return_allocation.is_some() {
                        mapped.region = if let Some(identity) = mapped.return_allocation.take() {
                            Region::returned(entry.span, identity)
                        } else {
                            let mut region = Region::allocation(entry.span);
                            region.selection.clone_from(output_path);
                            region
                        };
                        mapped.region.set_invocation(entry.invocation);
                        mapped.dependencies.clear();
                        mapped.anchor_scopes.clear();
                        mapped.confined = None;
                    }
                    Some(Datum {
                        roots: vec![mapped],
                        requires_new: template.requires_new,
                        ..Datum::default()
                    })
                }
            })
            .reduce(Datum::joined)
            .unwrap_or_default();
        if sampled == 0 || sampled != template.roots.len() {
            for (coordinate, member) in &template.members {
                output_path.push(coordinate.clone());
                let specialized =
                    self.instantiate_return(formals, via_formals, entry, member, output_path);
                output_path.pop();
                let slot = output.members.entry(coordinate.clone()).or_default();
                *slot = if sampled == 0 {
                    specialized
                } else {
                    std::mem::take(slot).joined(specialized)
                };
            }
        }
        output.array_len = template.array_len;
        output
            .latent_effects
            .extend(template.latent_effects.iter().cloned());
        output.live_callable_state |= template.live_callable_state;
        output.result_fresh |= template.result_fresh;
        if !template.environments.is_empty() {
            output.environments.insert(entry.span);
        }
        for (&owner, captures) in &template.invocations {
            let instance = output.invocations.entry(owner).or_default();
            for (&source, targets) in captures {
                let mapped = instance.entry(source).or_default();
                for &target in targets {
                    let formal = formals.iter().position(|formal| *formal == Some(target));
                    if let Some(index) = formal {
                        if let Some((_, _, value)) = entry
                            .arguments
                            .iter()
                            .find(|(position, _, _)| *position == index)
                        {
                            mapped.extend(value.root_dependencies());
                        }
                    } else {
                        mapped.insert(target);
                    }
                }
            }
        }
        match captured {
            Some(value) => output.joined(value),
            None => output,
        }
    }

    pub(super) fn defer_callback_result(
        &mut self,
        mut callback: CallbackResult,
        span: Span,
    ) -> Datum {
        fn widen_recursive(datum: &mut Datum, span: Span) {
            for origin in &mut datum.roots {
                if origin.region.source == span && origin.callback_result.is_some() {
                    origin.callback_result = None;
                }
            }
            datum.roots.sort_unstable();
            datum.roots.dedup();
            for member in datum.members.values_mut() {
                widen_recursive(member, span);
            }
        }
        for (_, _, value) in &mut callback.arguments {
            widen_recursive(value, span);
        }
        let mut result = Datum::source(span, Access::Ref, false);
        let dependencies: BTreeSet<_> = callback
            .values()
            .flat_map(Datum::origins)
            .flat_map(|origin| origin.dependencies.iter().copied())
            .collect();
        let template = self.callback_template(callback);
        for origin in &mut result.roots {
            origin.callback_result = Some(CallbackOrigin {
                template,
                cap: None,
            });
            origin.dependencies.clone_from(&dependencies);
        }
        result
    }

    pub(super) fn callback_template(&mut self, template: CallbackResult) -> usize {
        intern_callback(&mut self.callback_results, template)
    }

    pub(in crate::access::check) fn callback_return_contracts(
        &self,
        formals: &[Option<Span>],
        value: &Datum,
    ) -> Vec<CallbackReturn> {
        let formal_index = |source| formals.iter().position(|formal| *formal == Some(source));
        let mut contracts = BTreeSet::new();
        value.visit_origins(&mut Vec::new(), &mut |result_path, origin| {
            let Some(pending) = origin.callback_result else {
                return;
            };
            let Some(template) = self.callback_results.get(pending.template) else {
                return;
            };
            let mut arguments: Vec<_> = template
                .arguments
                .iter()
                .map(|argument| self.describe_callback_operand(formals, argument))
                .collect();
            arguments.sort_unstable();
            for receiver in &template.receiver.roots {
                if let Some(formal) = formal_index(receiver.region.source) {
                    contracts.insert(CallbackReturn {
                        invocation: template.ordinal,
                        receiver: formal,
                        receiver_path: receiver.region.selection.clone(),
                        source_path: origin.region.selection.clone(),
                        result_path: result_path.to_vec(),
                        cap: pending.cap,
                        arguments: arguments.clone(),
                    });
                }
            }
        });
        contracts.into_iter().collect()
    }

    pub(super) fn describe_callback_operand(
        &self,
        formals: &[Option<Span>],
        (position, mode, value): &CallArgument,
    ) -> CallbackArgument {
        let formal_index = |source| formals.iter().position(|formal| *formal == Some(source));
        let modes = if let Some(input) = Input::from_mode(*mode) {
            vec![InvocationMode::Input(input)]
        } else {
            value
                .roots
                .iter()
                .filter(|root| root.inherits_mode)
                .filter_map(|root| formal_index(root.region.source).map(InvocationMode::Formal))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect()
        };
        let mut sources = BTreeSet::new();
        value.visit_origins(&mut Vec::new(), &mut |path, root| {
            if let Some(formal) = formal_index(root.region.source) {
                sources.insert(ReturnSource {
                    formal,
                    source_path: root.region.selection.clone(),
                    result_path: path.to_vec(),
                    access: root.mode,
                });
            }
        });
        CallbackArgument {
            position: *position,
            modes,
            sources: sources.into_iter().collect(),
            callback_returns: self.callback_return_contracts(formals, value),
            snapshot_projections: self.snapshot_argument_providers(formals, value),
            allocations: Datum::return_allocations(std::slice::from_ref(value)),
            constructs: value.requires_new,
        }
    }

    pub(super) fn instantiate_callback_result<'e>(
        &mut self,
        template: usize,
        formals: &[Option<Span>],
        via: &BTreeSet<Span>,
        entry: &CallEntry<'e>,
    ) -> (Datum, Cow<'e, Ledger>) {
        let CallbackResult {
            receiver,
            mut arguments,
            mut spans,
            site,
            ..
        } = self
            .callback_results
            .get(template)
            .cloned()
            .unwrap_or_else(|| ril_source::ice!("missing callback return template"));
        let receiver = self.instantiate_return(formals, via, entry, &receiver, &mut Vec::new());
        self.specialize_callback_arguments(formals, via, entry, (&mut arguments, &mut spans));
        let mut ledger = Cow::Borrowed(entry.ledger);
        for (_, _, argument) in &arguments {
            if argument.has_call_graph(entry.span) {
                ledger.to_mut().remember_return_graph(argument, entry.span);
            }
        }
        let mut trace = entry.invocation.to_vec();
        trace.extend(site);
        let invocation = CallEntry {
            arguments: &arguments,
            spans: &spans,
            ledger: &ledger,
            span: entry.span,
            invocation: &trace,
            environment: None,
        };
        let result = self
            .callback_return(&receiver, &invocation)
            .unwrap_or_else(|| {
                trace.insert(
                    0,
                    InvocationSite {
                        span: entry.span,
                        ordinal: 0,
                    },
                );
                self.defer_callback_result(
                    CallbackResult {
                        receiver,
                        arguments,
                        spans,
                        site: trace,
                        ordinal: 0,
                    },
                    entry.span,
                )
            });
        if result.has_call_graph(entry.span) {
            ledger.to_mut().remember_return_graph(&result, entry.span);
        }
        (result, ledger)
    }

    pub(super) fn specialize_callback_arguments(
        &mut self,
        formals: &[Option<Span>],
        via: &BTreeSet<Span>,
        entry: &CallEntry<'_>,
        (arguments, spans): (&mut [CallArgument], &mut [Span]),
    ) {
        for ((_, mode, argument), span) in arguments.iter_mut().zip(spans) {
            if let [origin] = argument.roots.as_slice()
                && origin.region.selection.is_empty()
                && let Some(index) = formals
                    .iter()
                    .position(|formal| *formal == Some(origin.region.source))
                && let Some(((_, received, _), received_span)) = entry
                    .arguments
                    .iter()
                    .zip(entry.spans)
                    .find(|((position, _, _), _)| *position == index)
            {
                *span = *received_span;
                if *mode == Mode::Via && origin.inherits_mode {
                    *mode = *received;
                }
            }
            if *mode == Mode::Mut {
                for root in &mut argument.roots {
                    let draft_formal = formals
                        .iter()
                        .position(|formal| *formal == Some(root.region.source))
                        .and_then(|formal| {
                            entry
                                .arguments
                                .iter()
                                .find(|(position, ..)| *position == formal)
                        })
                        .is_some_and(|(_, _, actual)| {
                            actual.roots.iter().any(|origin| origin.draft)
                        });
                    if draft_formal {
                        // A mutable argument selects the draft path. A read
                        // of the same field may have sampled its data value.
                        root.storage_read = None;
                    }
                }
            }
            *argument = self.instantiate_return(formals, via, entry, argument, &mut Vec::new());
            if matches!(mode, Mode::Ref | Mode::Shared) {
                for root in &mut argument.roots {
                    root.fix_mode(root.mode.project(Access::from_mode(*mode)));
                    root.new = false;
                }
                argument.requires_new = false;
            }
        }
    }

    pub(super) fn callback_return(
        &mut self,
        receiver: &Datum,
        entry: &CallEntry<'_>,
    ) -> Option<Datum> {
        let mut outputs = Vec::new();
        for target in &receiver.roots {
            let span = snapshot_invocations::known_provider(target)?;
            if let Some(result) = self.replay_snapshot_provider_result(span, entry) {
                outputs.push(result);
                continue;
            }
            if let Some(closure) = self.closure_modes.get(&span).cloned() {
                let captures = Self::closure_captures(entry.ledger, receiver, target, &closure);
                let entry = CallEntry {
                    environment: Some(CallEnvironment {
                        owner: span,
                        bindings: Some(&captures),
                    }),
                    ..*entry
                };
                for value in &closure.returns {
                    outputs.push(self.instantiate_return(
                        &closure.formals,
                        &closure.via,
                        &entry,
                        value,
                        &mut Vec::new(),
                    ));
                }
                continue;
            }
            let id = self.definition(span)?;
            if self.program.hir.definition(id).kind != DefinitionKind::Function {
                return None;
            }
            let fun = self.function_syntax(id)?;
            if fun.body.is_none()
                && let Some(export) = self.program.imported_functions.get(&id)
            {
                let signature = self.program.callables.get(&id)?;
                outputs.push(self.imported_callback_result(fun, signature, export, entry)?);
                continue;
            }
            self.function(fun, entry.ledger);
            let mut result = self.return_template(fun, entry)?;
            if matches!(fun.signature.result_mode, Mode::Ref | Mode::Shared) {
                result.requires_new = false;
                for root in &mut result.roots {
                    root.fix_mode(Access::from_mode(fun.signature.result_mode));
                    root.new = false;
                }
            }
            outputs.push(result);
        }
        outputs.into_iter().reduce(Datum::joined)
    }
}
