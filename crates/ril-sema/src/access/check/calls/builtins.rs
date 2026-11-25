use super::*;

impl Analyzer<'_> {
    pub(super) fn primitive(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        name: &str,
        args: &[(usize, Mode, Datum)],
        span: Span,
    ) -> Datum {
        let first = args
            .iter()
            .find(|(index, _, _)| *index == 0)
            .map(|(_, _, v)| v);
        match name {
            "println" | "print" => self.effect(ctx, ledger, "io", span),
            "panic" => self.publish_at_exit(ctx, ledger, false),
            "push" | "pop" | "insert" | "remove" | "clear" => {
                if let Some(value) = first {
                    self.mutate(ctx, ledger, value, span);
                }
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
                if first.is_some_and(|value| {
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
                }) {
                    self.error(
                        Code::E0608,
                        span,
                        "panic containment cannot capture live state or emit an outward effect",
                    );
                }
                return Datum::source(span, Access::Mut, true);
            }
            "yield" | "sleep" | "scope" | "spawn" | "join" | "send" | "recv" => {
                self.effect(ctx, ledger, "fiber", span);
            }
            "read" | "open" | "close" | "write" => self.effect(ctx, ledger, "io", span),
            _ => {}
        }
        self.snapshot_value(span)
    }

    pub(super) fn concurrent(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        (module, name): (&str, &str),
        values: &[(usize, Mode, Datum)],
        syntax: &[Argument],
        span: Span,
    ) -> Datum {
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
                "scope"
                    | "try_scope"
                    | "join"
                    | "cancel"
                    | "yield"
                    | "yield_now"
                    | "sleep"
                    | "sleep_ms"
                    | "is_cancelled"
                    | "timeout_ms"
                    | "supervise"
                    | "zip"
                    | "try_zip"
                    | "race"
                    | "map"
                    | "try_map"
            ) {
                self.effect(ctx, ledger, "fiber", span);
            }
            if matches!(name, "sleep" | "sleep_ms" | "timeout_ms") {
                self.effect(ctx, ledger, "io", span);
            }
            if matches!(name, "spawn" | "join" | "cancel" | "cancel_scope")
                && let Some(scope) = first
            {
                self.mutate(ctx, ledger, scope, span);
            }
            if matches!(
                name,
                "run" | "spawn" | "supervise" | "zip" | "try_zip" | "race" | "timeout_ms"
            ) {
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
                                && !origin.dependency_spans().any(|id| moved.contains(&id))
                        {
                            self.error(
                                Code::E0601,
                                argument.unwrap_or(span),
                                "fiber closure captures live or confined state",
                            );
                        }
                    }
                    for &decl in &moved {
                        if let Some(slot) = ledger.slots.get(&decl)
                            && slot.variable
                        {
                            self.error(
                                Code::E0601,
                                argument.unwrap_or(span),
                                "fiber closure captures a replaceable slot",
                            );
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
            return self.snapshot_value(span);
        }
        if matches!(name, "send" | "recv") {
            self.effect(ctx, ledger, "fiber", span);
        }
        if matches!(name, "send" | "try_send" | "recv" | "try_recv")
            && let Some(value) = first
        {
            self.mutate(ctx, ledger, value, span);
        }
        match name {
            "bounded" | "unbounded" | "mpsc" => {
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
            "send" | "try_send" | "recv" | "try_recv" | "clone" => {
                Datum::source(span, Access::Mut, true)
            }
            _ => Datum::default(),
        }
    }
}
