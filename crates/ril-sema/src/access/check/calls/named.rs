use super::*;

impl<'program> Analyzer<'program> {
    pub(super) fn named_call(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        fun: &Function,
        sig: Option<&'program Callable>,
        (values, value_spans): (&[(usize, Mode, Datum)], &[Span]),
        (span, invocation): (Span, &[InvocationSite]),
    ) -> Datum {
        if fun.body.is_none()
            && let Some(id) = self.definition(fun.name.span)
        {
            if let Some(export) = self.program.imported_functions.get(&id) {
                return self.imported_call(
                    ctx,
                    ledger,
                    fun,
                    sig,
                    export,
                    (values, value_spans, span, invocation),
                );
            }
            if self.program.hir.file(fun.name.span.file).is_interface()
                && self.program.hir.operation_effect(id).is_none()
            {
                self.error(
                    Code::E0552,
                    span,
                    "imported function has no published call summary",
                );
                return self.snapshot_value(span);
            }
        }
        if let Some(sig) = sig {
            self.charge_call_effects(ctx, ledger, sig, fun.body.map(|_| fun.name.span), span);
        }
        let lexical = fun
            .signature
            .obligations
            .state
            .iter()
            .filter(|clause| clause.kind == StateKind::Environment)
            .flat_map(|clause| &clause.bindings)
            .filter_map(|(_, path)| self.declaration(path.span))
            .map(|decl| (decl, BTreeSet::from([decl])))
            .collect();
        let enclosing = Datum {
            invocations: BTreeMap::from([(fun.name.span, lexical)]),
            ..Datum::default()
        };
        self.link_invocation(ctx, &enclosing);
        let has_body = fun.body.is_some();
        let formals: Vec<_> = fun
            .signature
            .params
            .iter()
            .map(|param| param.name.as_ref().map(|name| name.span))
            .collect();
        if has_body {
            self.record_snapshot_call(
                ctx,
                (fun.name.span, &formals),
                (span, ledger),
                (values, value_spans),
            );
        }
        let mut before_updates = None;
        let mut modeled_stores = false;
        let mut normal_exit = true;
        if has_body && ctx.reachable && !ctx.shadow {
            self.function(fun, ledger);
            let checked = self
                .functions
                .iter()
                .find(|checked| checked.owner == fun.name.span)
                .map(CallStorage::updates_of);
            let storage = checked.or_else(|| {
                if !fun.is_meta {
                    self.recursive_calls.insert(fun.name.span);
                }
                self.recursive_storage.get(&fun.name.span).cloned()
            });
            if let Some(storage) = storage {
                normal_exit =
                    self.recursive_storage.is_empty() || fun.is_meta || storage.normal_exit;
                modeled_stores = true;
                if !storage.updates.is_empty() || storage.flow.is_some() {
                    let frozen = ledger.clone();
                    modeled_stores = self.apply_callable_storage(
                        ctx,
                        storage,
                        &CallEntry {
                            arguments: values,
                            spans: value_spans,
                            ledger: &frozen,
                            span,
                            invocation,
                            environment: Some(CallEnvironment {
                                owner: fun.name.span,
                                bindings: None,
                            }),
                        },
                        ledger,
                        false,
                    );
                    before_updates = Some(frozen.with_storage_samples(ledger).into_owned());
                }
            }
        }
        if has_body && let Some(signature) = sig {
            self.record_callable_arguments(
                ctx,
                (fun.name.span, &formals),
                signature,
                values,
                value_spans,
                (span, ledger),
            );
            for (index, axis) in member_axes(signature, &formals) {
                if let Some(((.., argument), &argument_span)) = values
                    .iter()
                    .zip(value_spans)
                    .find(|((position, ..), _)| *position == index)
                {
                    self.link_schema_argument(ctx, fun.name.span, axis, argument, argument_span);
                }
            }
        }
        for ((index, mode, value), &arg_span) in values.iter().zip(value_spans) {
            let formal = fun
                .signature
                .params
                .get(*index)
                .and_then(|param| param.name.as_ref())
                .map(|name| name.span);
            if let Some(formal) = formal.filter(|_| has_body) {
                let no_ctl_premise = Fact {
                    owner: fun.name.span,
                    obligation: Obligation::NoCtlParam(formal),
                };
                if ctx.reachable && !ctx.shadow {
                    if self.has_unhandled_ctl(ctx, value, self.ty(arg_span)) {
                        self.deferred_errors.push((
                            vec![no_ctl_premise.clone()],
                            Diagnostic::error(
                                Code::E0616,
                                arg_span,
                                "callable using unhandled ctl effect cannot be passed to a no_ctl parameter",
                            ),
                        ));
                    }
                    if matches!(self.ty(arg_span), Ty::Callable(c) if c.open_effects) {
                        for root in &value.roots {
                            if ctx.formals.contains(&Some(root.region.source)) {
                                self.rules.push(Rule {
                                    premises: vec![no_ctl_premise.clone()],
                                    conclusion: Fact {
                                        owner: ctx.owner,
                                        obligation: Obligation::NoCtlParam(root.region.source),
                                    },
                                });
                            }
                        }
                    }
                }
                let invocation = Fact {
                    owner: fun.name.span,
                    obligation: Obligation::Invoke(formal),
                };
                if *mode == Mode::Via {
                    self.forward_via_input(ctx, ledger, value, (fun.name.span, formal), span);
                }
                self.link_invocation_if(ctx, value, Some(&invocation));
                if ctx.reachable && !ctx.shadow {
                    for source in value.root_dependencies() {
                        self.rules.push(Rule {
                            premises: vec![invocation.clone()],
                            conclusion: Fact {
                                owner: ctx.owner,
                                obligation: Obligation::Invoke(source),
                            },
                        });
                    }
                    if matches!(mode, Mode::Mut | Mode::Shared | Mode::New | Mode::Via) {
                        let existing: BTreeSet<_> = value
                            .origins()
                            .filter(|origin| {
                                origin.mode.writes()
                                    && (!origin.new
                                        || *mode == Mode::New
                                            && ctx.formals.contains(&Some(origin.region.source)))
                            })
                            .flat_map(|origin| {
                                std::iter::once(Obligation::WriteExisting(origin.region.source))
                                    .chain(origin.dependency_spans().map(Obligation::Write))
                            })
                            .collect();
                        for obligation in existing {
                            self.rules.push(Rule {
                                premises: vec![Fact {
                                    owner: fun.name.span,
                                    obligation: Obligation::WriteExisting(formal),
                                }],
                                conclusion: Fact {
                                    owner: ctx.owner,
                                    obligation,
                                },
                            });
                        }
                    }
                }
            }
            if matches!(mode, Mode::Mut | Mode::Shared | Mode::New | Mode::Via) {
                let origins: BTreeSet<_> = value.root_dependencies().collect();
                for source in origins {
                    if let Some(formal) = formal
                        && has_body
                        && ctx.reachable
                        && !ctx.shadow
                    {
                        self.rules.push(Rule {
                            premises: vec![Fact {
                                owner: fun.name.span,
                                obligation: Obligation::Write(formal),
                            }],
                            conclusion: Fact {
                                owner: ctx.owner,
                                obligation: Obligation::Write(source),
                            },
                        });
                        if matches!(mode, Mode::Shared | Mode::Via) {
                            let causes = [
                                Some(Obligation::Share(formal)),
                                (!modeled_stores).then_some(Obligation::StoreShare(formal)),
                            ];
                            for cause in causes.into_iter().flatten() {
                                for obligation in
                                    [Obligation::Retain(source), Obligation::Share(source)]
                                {
                                    self.rules.push(Rule {
                                        premises: vec![Fact {
                                            owner: fun.name.span,
                                            obligation: cause.clone(),
                                        }],
                                        conclusion: Fact {
                                            owner: ctx.owner,
                                            obligation,
                                        },
                                    });
                                }
                            }
                        }
                    } else if sig.is_some_and(|sig| sig.state.iter().any(|state| state == "mut")) {
                        self.seed(ctx, Obligation::Write(source));
                    }
                }
            }
        }
        ledger.no_continuation |= !normal_exit;
        if fun.is_meta {
            return self.snapshot_value(span);
        }
        if matches!(
            fun.signature.result_mode,
            Mode::New | Mode::Infer | Mode::Ref | Mode::Shared
        ) || crate::access::check::results::carries_result(
            self.program,
            self.hir_scope(ctx),
            self.ty(span),
        ) || crate::access::check::higher_order::carries_callable(self.program, self.ty(span))
        {
            self.function(fun, ledger);
            let entry = CallEntry {
                arguments: values,
                spans: value_spans,
                ledger: before_updates.as_ref().unwrap_or(ledger),
                span,
                invocation,
                environment: Some(CallEnvironment {
                    owner: fun.name.span,
                    bindings: None,
                }),
            };
            if let Some(mut result) = self.return_template(fun, &entry) {
                if matches!(fun.signature.result_mode, Mode::Ref | Mode::Shared) {
                    result.requires_new = false;
                    for root in &mut result.roots {
                        root.fix_mode(Access::from_mode(fun.signature.result_mode));
                        root.new = false;
                    }
                }
                return result;
            }
        }
        let sources = self.declared_sources(&fun.signature);
        let mut result = match fun.signature.result_mode {
            Mode::New => Datum::source(span, Access::Mut, true),
            Mode::Ref | Mode::Shared => {
                let selected = fun
                    .signature
                    .result_sources
                    .iter()
                    .filter_map(|name| self.declaration(name.span));
                let mut result = self
                    .source_args(fun, values, selected)
                    .reduce(Datum::joined)
                    .unwrap_or_default();
                result.transform(&mut |origin| {
                    origin.fix_mode(Access::from_mode(fun.signature.result_mode));
                    origin.new = false;
                });
                result.requires_new = false;
                result
            }
            Mode::Infer => self.inferred_forwarding(fun, values, span),
            _ => self.snapshot_value(span),
        };
        for (index, (mode, source)) in sources.into_iter().enumerate() {
            if let Some(mut value) = self
                .source_args(fun, values, std::iter::once(source))
                .next()
            {
                value.transform(&mut |origin| {
                    origin.fix_mode(mode);
                    origin.new = false;
                });
                result
                    .members
                    .insert(Coordinate::Index(index.to_string()), value);
            }
        }
        result
    }

    pub(super) fn applied_effect<'p>(
        &'p self,
        declaration: usize,
        template: &'p str,
        span: Span,
    ) -> &'p str {
        self.program
            .effect_applications
            .get(&span)
            .and_then(|effects| effects.get(declaration))
            .map_or(template, String::as_str)
    }

    pub(super) fn charge_call_effects(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        signature: &Callable,
        owner: Option<Span>,
        span: Span,
    ) {
        for (index, template) in signature.effects.iter().enumerate() {
            let applied = self.applied_effect(index, template, span).to_owned();
            if let Some(owner) = owner {
                self.link_effects(ctx, ledger, owner, template, &applied, span);
            } else {
                self.effect(ctx, ledger, &applied, span);
            }
        }
    }

    pub(in crate::access::check) fn link_invocation(&mut self, ctx: &Context, target: &Datum) {
        self.link_invocation_if(ctx, target, None);
    }

    pub(super) fn invoke_callable_obligations(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        target: &Datum,
        span: Span,
    ) {
        self.link_invocation(ctx, target);
        for source in target.root_dependencies() {
            self.seed(ctx, Obligation::Invoke(source));
        }
        self.charge_latent_effects(ctx, ledger, target, span);
    }

    pub(super) fn check_capture_overlap(
        &mut self,
        ctx: &Context,
        function: Option<&ril_syntax::syntax::Function>,
        target: Option<&Datum>,
        entry: &CallEntry<'_>,
    ) {
        let declared = function
            .into_iter()
            .flat_map(|function| &function.signature.obligations.state)
            .filter(|clause| clause.kind == StateKind::Environment)
            .flat_map(|clause| &clause.bindings);
        for (storage, path) in declared {
            let Some(slot) = self
                .declaration(path.span)
                .and_then(|decl| entry.ledger.slots.get(&decl))
            else {
                continue;
            };
            let mut captured = entry.ledger.snapshot(&slot.value);
            ctx.mark_capture(slot, &mut captured);
            self.check_live(
                ctx,
                entry.ledger,
                &captured,
                entry.span,
                "argument handoff ended a captured path",
            );
            if captured
                .origins()
                .all(|root| root.mode == Access::Immutable)
            {
                continue;
            }
            let access = if storage.mode == Mode::Plain {
                Mode::Ref
            } else {
                storage.mode
            };
            for ((_, mode, argument), &span) in entry.arguments.iter().zip(entry.spans) {
                for conflict in conflicts(argument, *mode, &captured, access) {
                    self.check_conflict(
                        ctx,
                        conflict,
                        None,
                        span,
                        "argument authority overlaps a callable capture",
                    );
                }
            }
        }
        if let Some(target) = target {
            for (&owner, captures) in &target.invocations {
                for (index, &source) in captures.keys().enumerate() {
                    let Some(captured) = target.members.get(&Coordinate::Index(index.to_string()))
                    else {
                        continue;
                    };
                    let captured = entry.ledger.snapshot(captured);
                    if captured
                        .origins()
                        .all(|root| root.mode == Access::Immutable)
                    {
                        continue;
                    }
                    let writable = if captured
                        .roots
                        .iter()
                        .all(|root| root.mode == Access::Shared)
                    {
                        Mode::Shared
                    } else {
                        Mode::Mut
                    };
                    for ((_, mode, argument), &span) in entry.arguments.iter().zip(entry.spans) {
                        for (access, written) in [(Mode::Ref, false), (writable, true)] {
                            for conflict in conflicts(argument, *mode, &captured, access) {
                                self.check_conflict(
                                    ctx,
                                    conflict,
                                    Some((
                                        Fact {
                                            owner,
                                            obligation: Obligation::Write(source),
                                        },
                                        written,
                                    )),
                                    span,
                                    "argument authority overlaps a callable capture",
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    pub(in crate::access::check) fn link_invocation_if(
        &mut self,
        ctx: &Context,
        target: &Datum,
        if_exercised: Option<&Fact>,
    ) {
        if !ctx.reachable || ctx.shadow {
            return;
        }
        let receiver: BTreeSet<_> = if target.writers() {
            target.root_dependencies().collect()
        } else {
            BTreeSet::new()
        };
        for (&owner, captures) in &target.invocations {
            for (&source, writes) in captures {
                for (obligation, targets) in [
                    (Obligation::Write(source), writes),
                    (Obligation::Replace(source), &BTreeSet::from([source])),
                    (
                        Obligation::SharedReception(source),
                        &BTreeSet::from([source]),
                    ),
                    (Obligation::Invoke(source), writes),
                ] {
                    let premises = std::iter::once(Fact {
                        owner,
                        obligation: obligation.clone(),
                    })
                    .chain(if_exercised.cloned())
                    .collect::<Vec<_>>();
                    let receiver_writes =
                        matches!(obligation, Obligation::Write(_) | Obligation::Replace(_));
                    let conclusions = targets
                        .iter()
                        .map(|&decl| match obligation {
                            Obligation::Replace(_) => Obligation::Replace(decl),
                            Obligation::SharedReception(_) => Obligation::SharedReception(decl),
                            Obligation::Write(_) => Obligation::Write(decl),
                            _ => Obligation::Invoke(decl),
                        })
                        .chain(
                            receiver
                                .iter()
                                .copied()
                                .filter(|_| receiver_writes)
                                .map(Obligation::Write),
                        );
                    for obligation in conclusions {
                        self.rules.push(Rule {
                            premises: premises.clone(),
                            conclusion: Fact {
                                owner: ctx.owner,
                                obligation,
                            },
                        });
                    }
                }
            }
        }
    }

    pub(super) fn link_effects(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        owner: Span,
        template: &str,
        applied: &str,
        span: Span,
    ) {
        self.use_effect(
            ctx,
            ledger,
            Obligation::Effect(applied.into()),
            span,
            Some(Fact {
                owner,
                obligation: Obligation::Effect(template.into()),
            }),
        );
        let template_includes = self
            .program
            .effect_instances
            .get(template)
            .map(|instance| &instance.includes);
        let applied_includes = self
            .program
            .effect_instances
            .get(applied)
            .map(|instance| &instance.includes);
        for included in template_includes.into_iter().flatten() {
            let Some(origin) = self.program.effect_definition(included) else {
                continue;
            };
            if let Some(label) = applied_includes
                .into_iter()
                .flatten()
                .find(|label| self.program.effect_definition(label) == Some(origin))
            {
                self.use_effect(
                    ctx,
                    ledger,
                    Obligation::Effect(label.clone()),
                    span,
                    Some(Fact {
                        owner,
                        obligation: Obligation::Effect(included.clone()),
                    }),
                );
            }
        }
        let applied = self.effect_operations(applied);
        for from in self.effect_operations(template) {
            if let Some(to) = applied.iter().find(|op| op.id == from.id) {
                self.use_effect(
                    ctx,
                    ledger,
                    Obligation::Operation(to.clone()),
                    span,
                    Some(Fact {
                        owner,
                        obligation: Obligation::Operation(from),
                    }),
                );
            }
        }
    }
}
