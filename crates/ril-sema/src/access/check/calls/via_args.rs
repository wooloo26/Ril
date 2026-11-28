use super::*;

impl Analyzer<'_> {
    pub(super) fn link_schema_argument(
        &mut self,
        ctx: &Context,
        owner: Span,
        axis: Region,
        argument: &Datum,
        span: Span,
    ) {
        let mut ty = self.ty(span).clone();
        let mut mode = Mode::Plain;
        for coordinate in &axis.selection {
            let Some(member) = self.schema_member(&ty, coordinate) else {
                return;
            };
            mode = member.mode.mode;
            ty = member.ty;
        }
        let forwarded: Option<Vec<_>> = if mode == Mode::Via && !argument.roots.is_empty() {
            argument
                .roots
                .iter()
                .map(|root| {
                    let mut actual = root.region.clone();
                    actual.selection.extend_from_slice(&axis.selection);
                    self.schema_axis(&actual).cloned()
                })
                .collect()
        } else {
            None
        };
        for required in [
            SchemaRequirement::Writable,
            SchemaRequirement::Exclusive,
            SchemaRequirement::Shared,
        ] {
            let premise = Fact {
                owner,
                obligation: Obligation::Schema(axis.clone(), required),
            };
            if let Some(axes) = &forwarded {
                if ctx.reachable && !ctx.shadow {
                    for axis in axes {
                        self.rules.push(Rule {
                            premises: vec![premise.clone()],
                            conclusion: Fact {
                                owner: ctx.owner,
                                obligation: Obligation::Schema(axis.clone(), required),
                            },
                        });
                    }
                }
            } else if mode == Mode::Via || !required.accepts(Access::from_mode(mode)) {
                self.deferred_errors.push((
                    vec![premise],
                    Diagnostic::error(
                        Code::E0520,
                        span,
                        "via application requires a compatible member schema",
                    ),
                ));
            }
        }
    }

    pub(super) fn forward_needs_sharing(
        &mut self,
        ctx: &Context,
        value: &Datum,
        (owner, formal): (Span, Span),
    ) {
        if !ctx.reachable || ctx.shadow {
            return;
        }
        for root in &value.roots {
            self.rules.push(Rule {
                premises: vec![Fact {
                    owner,
                    obligation: Obligation::NeedsSharing(formal),
                }],
                conclusion: Fact {
                    owner: ctx.owner,
                    obligation: Obligation::NeedsSharing(root.region.source),
                },
            });
        }
    }

    pub(super) fn link_via_projection(
        &mut self,
        ctx: &Context,
        value: &Datum,
        owner: Span,
        formal: Span,
        span: Span,
    ) {
        for (obligation, required) in [
            (Obligation::Write(formal), SchemaRequirement::Writable),
            (Obligation::Share(formal), SchemaRequirement::Shared),
            (Obligation::StoreShare(formal), SchemaRequirement::Shared),
            (Obligation::NeedsSharing(formal), SchemaRequirement::Shared),
        ] {
            let premise = Fact { owner, obligation };
            if !value.writers() {
                self.deferred_errors.push((
                    vec![premise],
                    Diagnostic::error(
                        Code::E0520,
                        span,
                        "via application requires a writable projection",
                    ),
                ));
            } else if ctx.reachable && !ctx.shadow {
                for obligation in self.schema_requirements(value, required) {
                    self.rules.push(Rule {
                        premises: vec![premise.clone()],
                        conclusion: Fact {
                            owner: ctx.owner,
                            obligation,
                        },
                    });
                }
            }
        }
    }

    pub(super) fn forward_via_input(
        &mut self,
        ctx: &Context,
        _ledger: &mut Ledger,
        value: &Datum,
        (owner, formal): (Span, Span),
        span: Span,
    ) {
        if value.roots.iter().all(|origin| origin.inherits_mode) {
            self.forward_needs_sharing(ctx, value, (owner, formal));
        } else {
            self.link_via_projection(ctx, value, owner, formal, span);
        }
    }

    pub(super) fn apply_closure_input(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        (owner, formal): (Span, Span),
        (mode, value, span): (Mode, &Datum, Span),
        (via, modeled_stores, formal_open_effects): (bool, bool, bool),
    ) {
        let write = Fact {
            owner,
            obligation: Obligation::Write(formal),
        };
        let share = Fact {
            owner,
            obligation: Obligation::Share(formal),
        };
        let store_share = Fact {
            owner,
            obligation: Obligation::StoreShare(formal),
        };
        if via {
            if mode == Mode::Via {
                self.forward_via_input(ctx, ledger, value, (owner, formal), span);
            } else {
                for (allowed, cause, code, message) in [
                    (
                        mode == Mode::Shared,
                        share.clone(),
                        Code::E0520,
                        "via application requires shared writable reception",
                    ),
                    (
                        mode == Mode::Shared,
                        store_share.clone(),
                        Code::E0520,
                        "via application requires shared writable reception",
                    ),
                    (
                        mode == Mode::Shared,
                        Fact {
                            owner,
                            obligation: Obligation::NeedsSharing(formal),
                        },
                        Code::E0520,
                        "via application requires shared writable reception",
                    ),
                    (
                        Access::from_mode(mode).writes(),
                        write.clone(),
                        Code::E0520,
                        "via application requires a writable source",
                    ),
                ] {
                    if !allowed {
                        self.deferred_errors
                            .push((vec![cause], Diagnostic::error(code, span, message)));
                    }
                }
            }
        }
        let invocation = Fact {
            owner,
            obligation: Obligation::Invoke(formal),
        };
        self.link_invocation_if(ctx, value, Some(&invocation));
        if ctx.reachable && !ctx.shadow {
            if formal_open_effects {
                self.charge_latent_effects_if(ctx, ledger, value, span, Some(&invocation));
                let arg_ty = self.ty(span).clone();
                if let Ty::Callable(actual) = &arg_ty {
                    for effect in &actual.effects {
                        self.use_effect(
                            ctx,
                            ledger,
                            Obligation::Effect(effect.clone()),
                            span,
                            Some(invocation.clone()),
                        );
                    }
                    for &var in &actual.effect_vars {
                        self.use_effect_var(ctx, ledger, var, span);
                    }
                    if actual.open_effects || actual.direct_open_effects {
                        self.use_open_effect(
                            ctx,
                            ledger,
                            actual.direct_open_effects && !actual.open_effects,
                            span,
                        );
                    }
                }
            }
            for source in value.root_dependencies().collect::<BTreeSet<_>>() {
                self.rules.push(Rule {
                    premises: vec![invocation.clone()],
                    conclusion: Fact {
                        owner: ctx.owner,
                        obligation: Obligation::Invoke(source),
                    },
                });
            }
        }
        if !ctx.reachable || ctx.shadow || !Access::from_mode(mode).writes() {
            return;
        }
        for source in value.root_dependencies().collect::<BTreeSet<_>>() {
            self.rules.push(Rule {
                premises: vec![write.clone()],
                conclusion: Fact {
                    owner: ctx.owner,
                    obligation: Obligation::Write(source),
                },
            });
            if matches!(mode, Mode::Via | Mode::Shared) {
                for cause in
                    std::iter::once(&share).chain((!modeled_stores).then_some(&store_share))
                {
                    for obligation in [Obligation::Retain(source), Obligation::Share(source)] {
                        self.rules.push(Rule {
                            premises: vec![cause.clone()],
                            conclusion: Fact {
                                owner: ctx.owner,
                                obligation,
                            },
                        });
                    }
                }
            }
        }
        let existing: BTreeSet<_> = value
            .roots
            .iter()
            .filter(|origin| {
                origin.mode.writes()
                    && (!origin.new
                        || mode == Mode::New && ctx.formals.contains(&Some(origin.region.source)))
            })
            .map(|origin| origin.region.source)
            .collect();
        for source in existing {
            self.rules.push(Rule {
                premises: vec![Fact {
                    owner,
                    obligation: Obligation::WriteExisting(formal),
                }],
                conclusion: Fact {
                    owner: ctx.owner,
                    obligation: Obligation::WriteExisting(source),
                },
            });
        }
    }

    pub(in crate::access::check) fn forwards_via(ctx: &Context, value: &Datum) -> bool {
        !value.roots.is_empty()
            && value.roots.iter().all(|origin| {
                (origin.inherits_mode
                    && origin.region.selection.is_empty()
                    && ctx.via.contains(&origin.region.source))
                    || (ctx.member_via && !origin.reception.is_empty())
                    || origin
                        .callback_result
                        .is_some_and(|result| result.cap.is_none())
            })
    }

    pub(in crate::access::check) fn prepare_argument(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        arg: &Argument,
        mut value: Datum,
        span: Span,
        mode: Mode,
    ) -> Datum {
        if !matches!(mode, Mode::Via | Mode::Plain) {
            for root in &mut value.roots {
                root.inherits_mode = false;
            }
        }
        match mode {
            Mode::New => {
                if ledger
                    .loop_snapshot(&value)
                    .origins()
                    .any(|origin| origin.confined.is_some())
                {
                    self.error(
                        Code::E0604,
                        span,
                        "resource or draft cannot satisfy a new parameter",
                    );
                } else if !value.requires_new {
                    let mut diag = Diagnostic::error(
                        Code::E0548,
                        span,
                        "new parameter requires an unbound freshly created shared object",
                    );
                    if let Some(decl) = value
                        .roots
                        .first()
                        .and_then(|root| root.dependency_spans().next())
                    {
                        diag = diag.with_label(
                            decl,
                            "binding declared here cannot be passed to a `new` parameter",
                        );
                    }
                    diag = diag.with_help(
                        "construct the shared object inline, pass a `-> new` call, or return it from an exiting block",
                    );
                    self.error_diag(diag);
                }
            }
            Mode::Mut | Mode::Shared => {
                if !self.mutable_argument_place(ctx, arg.value, mode) {
                    self.error(
                        Code::E0410,
                        span,
                        "mutable argument requires an addressable path",
                    );
                } else if !value.writers() {
                    self.error(Code::E0520, span, "argument path has no writable authority");
                }
                self.require_schema(
                    ctx,
                    &value,
                    if mode == Mode::Mut {
                        SchemaRequirement::Exclusive
                    } else {
                        SchemaRequirement::Writable
                    },
                );
                if mode == Mode::Shared && value.origins().any(|origin| origin.confined.is_some()) {
                    self.error(Code::E0604, span, "resource authority cannot be retained");
                }
                if mode == Mode::Shared {
                    if value.roots.iter().any(|origin| origin.call_scoped_access) {
                        self.error(Code::E0528, span, "a call-scoped writer cannot be retained");
                    }
                    for root in &mut value.roots {
                        root.fix_mode(Access::Shared);
                        root.new = false;
                    }
                    value.requires_new = false;
                }
            }
            Mode::Ref => {
                for root in &mut value.roots {
                    root.fix_mode(Access::Ref);
                    root.new &= value.requires_new;
                }
                value.requires_new = false;
            }
            Mode::Plain
                if matches!(self.ty(span), Ty::Callable(_))
                    || self.program.is_must_consume(self.ty(span)) =>
            {
                for root in &mut value.roots {
                    root.inherits_mode = false;
                }
            }
            Mode::Plain => self.freeze_value(ctx, ledger, &mut value, span),
            _ => {}
        }
        value
    }

    pub(super) fn mutable_argument_place(&self, ctx: &Context, id: ExprId, mode: Mode) -> bool {
        let ast = self.ast(ctx.file);
        match &ast.expr(id).value {
            Expr::Path(_) => true,
            Expr::Member { .. } | Expr::Index { .. } => ast.navigation_chain(id).is_none(),
            Expr::Call { callee, args } if matches!(mode, Mode::Mut | Mode::Shared) => {
                matches!(
                    &ast.expr(*callee).value,
                    Expr::Path(path)
                        if self.definition(path.span).is_some_and(|def| {
                            let def = self.program.hir.definition(def);
                            matches!(def.kind, DefinitionKind::Primitive(_)) && def.name.value == "inner"
                        })
                ) && matches!(args.as_slice(), [arg] if arg.mode == Mode::Mut || (mode == Mode::Shared && arg.mode == Mode::Shared))
            }
            _ => false,
        }
    }

    pub(in crate::access::check) fn snapshot_value(&self, span: Span) -> Datum {
        if self.program.is_value(self.ty(span)) && !self.program.is_must_consume(self.ty(span)) {
            Datum::default()
        } else {
            Datum::source(span, Access::Immutable, false)
        }
    }
}
