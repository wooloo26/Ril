use super::*;

impl Analyzer<'_> {
    fn apply_primitive_signature(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        sig: Option<&crate::ty::Callable>,
        args: &[(usize, Mode, Datum)],
        span: Span,
    ) {
        let Some(sig) = sig else {
            return;
        };
        self.charge_call_effects(ctx, ledger, sig, None, span);
        if sig.state.iter().any(|s| s == "mut" || s == "^mut") {
            for (index, _, value) in args {
                if sig
                    .parameters
                    .get(*index)
                    .is_some_and(|p| matches!(p.mode, Mode::Mut | Mode::Shared))
                {
                    self.mutate(ctx, ledger, value, span);
                }
            }
        }
    }

    pub(super) fn primitive(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        (name, sig): (&str, Option<&crate::ty::Callable>),
        args: &[(usize, Mode, Datum)],
        syntax: &[Argument],
        span: Span,
    ) -> Datum {
        self.apply_primitive_signature(ctx, ledger, sig, args, span);
        let first = args
            .iter()
            .find(|(index, _, _)| *index == 0)
            .map(|(_, _, v)| v);
        match name {
            "panic" => {
                if !ctx.defers.is_empty() && ctx.reachable && !ctx.shadow {
                    let mut unwind_ledger = ledger.clone();
                    let mut unwind_ctx = ctx.clone();
                    self.run_defers(&mut unwind_ctx, &mut unwind_ledger, 0);
                }
                self.publish_at_exit(ctx, ledger, false);
            }
            "abort" => {
                if let Some(k) = first {
                    self.link_invocation(ctx, k);
                    ledger.consume_datum_linear(k);
                }
                if let Some(arg) = syntax.first()
                    && let Ty::Callable(c) = self.ty(self.ast(ctx.file).expr(arg.value).span)
                {
                    for effect in &c.effects {
                        if effect == "io" {
                            self.effect(ctx, ledger, "io", span);
                        } else {
                            for op in self.effect_operations(effect) {
                                if !self.program.hir.is_ctl_operation(op.id) {
                                    self.use_effect(
                                        ctx,
                                        ledger,
                                        crate::access::check::Obligation::Operation(op),
                                        span,
                                        None,
                                    );
                                }
                            }
                        }
                    }
                }
                return Datum::default();
            }
            "clone" => {
                if let Some(value) = first {
                    return self.clone_storage(
                        ctx,
                        ledger,
                        value,
                        (span, &[]),
                        crate::access::check::storage::ReadSite::Clone(span),
                    );
                }
                return Datum::source(span, Access::Mut, true);
            }
            "inner" => {
                return first.cloned().unwrap_or_default();
            }
            "derive" => {
                if let Some((_, _, callback)) = args.iter().find(|(i, _, _)| *i == 1) {
                    let cb_ty = syntax.get(1).map_or(&Ty::Unknown, |arg| {
                        self.ty(self.ast(ctx.file).expr(arg.value).span)
                    });
                    if callback.uses_ctl_handler || self.has_unhandled_ctl(ctx, callback, cb_ty) {
                        self.error(
                            Code::E0607,
                            span,
                            "derive callback cannot invoke outer ctl effects",
                        );
                    }
                    self.invoke_callable_obligations(ctx, ledger, callback, span);
                    if let Some(base) = first
                        && ctx.runtime
                        && ctx.reachable
                        && !ctx.shadow
                    {
                        let index = self.storage_read_index(
                            crate::access::check::storage::ReadSite::Derive(span),
                        );
                        return self.derive_storage(
                            ctx,
                            ledger,
                            (base, callback),
                            (span, &[], index),
                        );
                    }
                }
            }
            "absorb_panic" => {
                let has_forbidden_outer_handle = syntax.first().is_some_and(|arg| {
                    let arg_span = self.ast(ctx.file).expr(arg.value).span;
                    self.program
                        .hir
                        .references_within(arg_span)
                        .any(|(ref_span, def_id)| {
                            let def = self.program.hir.definition(def_id);
                            let is_outer = def.name.span.start < arg_span.start
                                || def.name.span.end > arg_span.end;
                            is_outer
                                && self.program.is_must_consume(
                                    self.program
                                        .types
                                        .get(&ref_span)
                                        .or_else(|| self.program.bindings.get(&def_id))
                                        .unwrap_or(&Ty::Unknown),
                                )
                        })
                });
                if has_forbidden_outer_handle
                    || first.is_some_and(|value| {
                        !value.latent_effects.is_empty()
                            || !value.latent_operations.is_empty()
                            || value.live_callable_state
                            || value.uses_ctl_handler
                            || value.roots.iter().any(|origin| {
                                origin.mode != Access::Immutable
                                    && (!origin.new || !origin.dependencies.is_empty())
                            })
                            || value
                                .members
                                .values()
                                .flat_map(Datum::origins)
                                .any(|origin| origin.mode != Access::Immutable)
                    })
                {
                    self.error(
                        Code::E0608,
                        span,
                        "panic containment cannot capture live state, outer ctl/must-consume handles, invoke ctl handlers, or emit an outward effect",
                    );
                }
                let mut result = Datum::source(span, Access::Mut, true);
                let fresh = first.is_some_and(|value| value.result_fresh)
                    || syntax.first().is_some_and(|arg| {
                        matches!(
                            self.ty(self.ast(ctx.file).expr(arg.value).span),
                            Ty::Callable(sig) if sig.result_mode == Mode::New
                        )
                    });
                let payload = if fresh {
                    Datum::source(span, Access::Mut, true)
                } else {
                    self.snapshot_value(span)
                };
                result
                    .members
                    .insert(Coordinate::Index("0".into()), payload);
                return result;
            }
            _ => {}
        }
        if sig.is_some_and(|sig| sig.result_mode == Mode::New)
            && !self.program.is_value(self.ty(span))
        {
            return Datum::source(span, Access::Mut, true);
        }
        self.snapshot_value(span)
    }
}
