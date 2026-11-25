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
            "panic" => self.publish_at_exit(ctx, ledger, false),
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
                let Some(value) = first else {
                    return Datum::default();
                };
                if matches!(self.ty(span), Ty::Record(..)) {
                    return value.clone();
                }
                if let Ty::Tuple(parts) = self.ty(span) {
                    if args
                        .iter()
                        .any(|(index, mode, _)| *index == 0 && *mode == Mode::Mut)
                    {
                        return value.clone();
                    }
                    let mut tuple = Datum::source(span, Access::Mut, true);
                    for index in 0..parts.len() {
                        let coordinate = Coordinate::Index(index.to_string());
                        let member = ledger.project(value, coordinate.clone(), Access::Immutable);
                        tuple.members.insert(coordinate, member);
                    }
                    return tuple;
                }
                return ledger.project(value, Coordinate::Index("0".into()), Access::Mut);
            }
            "derive" => {
                if let Some((_, _, callback)) = args.iter().find(|(i, _, _)| *i == 1) {
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
                                && Self::contains_panic_unsafe_handle(
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
                            || value.live_callable_state
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
                        "panic containment cannot capture live state, outer channel/foreign handles, or emit an outward effect",
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
        if sig.is_some_and(|sig| sig.result_mode == Mode::New) && !self.ty(span).is_value() {
            return Datum::source(span, Access::Mut, true);
        }
        self.snapshot_value(span)
    }

    pub(super) fn concurrent(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        (module, name, sig): (&str, &str, Option<&crate::ty::Callable>),
        values: &[(usize, Mode, Datum)],
        syntax: &[Argument],
        span: Span,
    ) -> Datum {
        self.apply_primitive_signature(ctx, ledger, sig, values, span);
        let first = values
            .iter()
            .find(|(i, _, _)| *i == 0)
            .map(|(_, _, datum)| datum);
        let second = values
            .iter()
            .find(|(i, _, _)| *i == 1)
            .map(|(_, _, datum)| datum);
        if module == "Fiber" {
            if matches!(
                name,
                "run"
                    | "spawn"
                    | "supervise"
                    | "zip"
                    | "try_zip"
                    | "race"
                    | "timeout_ms"
                    | "map"
                    | "try_map"
            ) {
                let multi_run = matches!(name, "map" | "try_map");
                for (i, _, callback) in values.iter().filter(|(_, _, v)| {
                    v.live_callable_state || !v.latent_effects.is_empty() || !v.members.is_empty()
                }) {
                    let argument = syntax
                        .get(*i)
                        .map(|arg| self.ast(ctx.file).expr(arg.value).span);
                    let mut moved = BTreeSet::new();
                    if let Some(argument) = argument {
                        for expr in self.ast(ctx.file).expressions().filter(|expr| {
                            expr.span.start >= argument.start && expr.span.end <= argument.end
                        }) {
                            if let Expr::Unary { op, value } = &expr.value
                                && op.value == "new"
                                && let Expr::Path(path) = &self.ast(ctx.file).expr(*value).value
                                && let Some(decl) = self.declaration(path.span)
                            {
                                moved.insert(decl);
                            }
                        }
                    }
                    if callback.live_callable_state {
                        self.error(
                            Code::E0615,
                            argument.unwrap_or(span),
                            "a stateful lexical handler cannot cross the fiber boundary",
                        );
                    }
                    if name == "supervise"
                        && callback
                            .latent_effects
                            .iter()
                            .any(|effect| effect != "fiber")
                    {
                        self.error(
                            Code::E0608,
                            argument.unwrap_or(span),
                            "supervised task has outward effects",
                        );
                    }
                    for origin in callback.members.values().flat_map(Datum::origins) {
                        if origin.confined.is_some()
                            || origin.mode != Access::Immutable
                                && (multi_run
                                    || !origin.dependency_spans().any(|id| moved.contains(&id)))
                        {
                            let target_span = argument.unwrap_or(span);
                            let mut diag = Diagnostic::error(
                                Code::E0601,
                                target_span,
                                "fiber closure captures live or confined state",
                            );
                            if origin.region.source != target_span {
                                diag = diag.with_label(
                                    origin.region.source,
                                    "live or confined source originated here",
                                );
                            }
                            diag = diag.with_help(
                                "hand off a `new` value or pass an immutable snapshot across the fiber boundary",
                            );
                            self.error_diag(diag);
                        }
                    }
                    for &decl in &moved {
                        if multi_run {
                            self.error(
                                Code::E0601,
                                argument.unwrap_or(span),
                                "multi-item fiber closure cannot hand off an outer new binding",
                            );
                        } else if let Some(slot) = ledger.slots.get(&decl)
                            && slot.variable
                        {
                            let target_span = argument.unwrap_or(span);
                            let mut diag = Diagnostic::error(
                                Code::E0601,
                                target_span,
                                "fiber closure captures a replaceable slot",
                            );
                            if slot.decl != target_span {
                                diag = diag
                                    .with_label(slot.decl, "replaceable `var` slot declared here");
                            }
                            self.error_diag(diag);
                        } else {
                            ledger.revoke(decl.into(), None, None);
                        }
                    }
                }
            }
            for arg in values {
                if matches!(name, "scope" | "try_scope" | "uncancellable") {
                    self.link_invocation(ctx, &arg.2);
                }
                for effect in &arg.2.latent_effects {
                    if name != "run" || effect != "fiber" {
                        self.effect(ctx, ledger, effect, span);
                    }
                }
            }
            if name == "spawn" {
                let scope = first
                    .and_then(|value| value.roots.first())
                    .map(|origin| origin.region.source);
                let mut output = Datum::source(span, Access::Mut, true);
                output.task_scope = scope;
                output.result_fresh = second.is_some_and(|work| work.result_fresh)
                    || syntax.get(1).is_some_and(|argument| {
                        matches!(self.ty(self.ast(ctx.file).expr(argument.value).span), Ty::Callable(sig) if sig.result_mode == Mode::New)
                    });
                output.transform(&mut |origin| {
                    origin.confined = scope;
                });
                return output;
            }
            if matches!(name, "join" | "cancel") {
                if let (Some(scope), Some(task)) = (first, second)
                    && task.task_scope.is_some()
                    && scope
                        .roots
                        .iter()
                        .all(|root| task.task_scope != Some(root.region.source))
                {
                    self.error(Code::E0604, span, "task does not belong to this scope");
                }
                if let Some(value) = second {
                    ledger.inspect(value);
                }
                let fresh = second.is_some_and(|task| task.result_fresh);
                if name == "cancel" {
                    let mut result = Datum::source(span, Access::Mut, true);
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
                if fresh
                    && values
                        .iter()
                        .any(|(index, mode, _)| *index == 1 && *mode == Mode::New)
                {
                    return Datum::source(span, Access::Mut, true);
                }
            }
            if matches!(
                name,
                "run"
                    | "scope"
                    | "try_scope"
                    | "uncancellable"
                    | "supervise"
                    | "timeout_ms"
                    | "zip"
                    | "try_zip"
                    | "map"
                    | "try_map"
                    | "race"
            ) {
                let callback_fresh = |idx: usize| {
                    values
                        .iter()
                        .find(|(i, _, _)| *i == idx)
                        .is_some_and(|(_, _, cb)| cb.result_fresh)
                        || syntax.get(idx).is_some_and(|argument| {
                            matches!(
                                self.ty(self.ast(ctx.file).expr(argument.value).span),
                                Ty::Callable(sig) if sig.result_mode == Mode::New
                            )
                        })
                };
                match name {
                    "run" | "scope" | "try_scope" | "uncancellable" => {
                        if callback_fresh(0) {
                            return Datum::source(span, Access::Mut, true);
                        }
                    }
                    "supervise" | "timeout_ms" => {
                        let work_idx = usize::from(name == "timeout_ms");
                        let mut result = Datum::source(span, Access::Mut, true);
                        let payload = if callback_fresh(work_idx) {
                            Datum::source(span, Access::Mut, true)
                        } else {
                            self.snapshot_value(span)
                        };
                        result
                            .members
                            .insert(Coordinate::Index("0".into()), payload);
                        return result;
                    }
                    "zip" | "try_zip" => {
                        let mut record = Datum::source(span, Access::Mut, true);
                        let first_payload = if callback_fresh(0) {
                            Datum::source(span, Access::Mut, true)
                        } else {
                            self.snapshot_value(span)
                        };
                        let second_payload = if callback_fresh(1) {
                            Datum::source(span, Access::Mut, true)
                        } else {
                            self.snapshot_value(span)
                        };
                        record
                            .members
                            .insert(Coordinate::Field("first".into()), first_payload);
                        record
                            .members
                            .insert(Coordinate::Field("second".into()), second_payload);
                        if name == "try_zip" {
                            let mut result = Datum::source(span, Access::Mut, true);
                            result.members.insert(Coordinate::Index("0".into()), record);
                            return result;
                        }
                        return record;
                    }
                    "map" | "try_map" => {
                        let mut array = Datum::source(span, Access::Mut, true);
                        if callback_fresh(1) {
                            array.members.insert(
                                Coordinate::Dynamic,
                                Datum::source(span, Access::Mut, true),
                            );
                        }
                        if name == "try_map" {
                            let mut result = Datum::source(span, Access::Mut, true);
                            result.members.insert(Coordinate::Index("0".into()), array);
                            return result;
                        }
                        return array;
                    }
                    "race" if callback_fresh(0) && callback_fresh(1) => {
                        return Datum::source(span, Access::Mut, true);
                    }
                    _ => {}
                }
            }
            return self.snapshot_value(span);
        }
        if name == "drain"
            && let Some(consumer) = second
        {
            self.invoke_callable_obligations(ctx, ledger, consumer, span);
            self.link_invocation(ctx, consumer);
            for effect in &consumer.latent_effects {
                self.effect(ctx, ledger, effect, span);
            }
        }
        match name {
            "bounded" | "unbounded" => {
                let mut pair = Datum::source(span, Access::Mut, true);
                for key in ["tx", "rx"] {
                    pair.members.insert(
                        Coordinate::Field(key.into()),
                        Datum::source(span, Access::Mut, true)
                            .project(Coordinate::Field(key.into()), Access::Mut),
                    );
                }
                pair
            }
            "send" | "try_send" => Datum::source(span, Access::Mut, true),
            _ if sig.is_some_and(|sig| sig.result_mode == Mode::New)
                && !self.ty(span).is_value() =>
            {
                Datum::source(span, Access::Mut, true)
            }
            _ => Datum::default(),
        }
    }

    fn contains_panic_unsafe_handle(ty: &Ty) -> bool {
        match ty {
            Ty::Sender(_) | Ty::Receiver(_) | Ty::Scope | Ty::Task(_) => true,
            Ty::Adt(adt) => adt.kind == crate::ty::AdtKind::Foreign,
            Ty::Option(inner) | Ty::Draft(inner) => Self::contains_panic_unsafe_handle(inner),
            Ty::Result(ok, err) => {
                Self::contains_panic_unsafe_handle(ok) || Self::contains_panic_unsafe_handle(err)
            }
            Ty::Array(item) => Self::contains_panic_unsafe_handle(&item.ty),
            Ty::Map(k, v) => {
                Self::contains_panic_unsafe_handle(k) || Self::contains_panic_unsafe_handle(&v.ty)
            }
            Ty::Tuple(items) => items
                .iter()
                .any(|m| Self::contains_panic_unsafe_handle(&m.ty)),
            Ty::Record(fields, _) => fields
                .values()
                .any(|m| Self::contains_panic_unsafe_handle(&m.ty)),
            _ => false,
        }
    }
}
