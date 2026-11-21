use std::collections::BTreeSet;

use ril_base::{diag::Code, span::Span};
use ril_frontend::{
    hir::DefinitionKind,
    syntax::{Argument, Expr, ExprId, Handler, Mode, StateKind, StmtKind},
};

use crate::ty::Ty;

use super::{
    Access, Analyzer, Context, Coordinate, Datum, Fact, Input, Ledger, ModeUse, Obligation, Rule,
    Slot, conflicts,
};

impl Analyzer<'_> {
    pub(super) fn fallback_handler(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        handler: ExprId,
        span: Span,
    ) -> Datum {
        let node = self.ast(ctx.file).expr(handler);
        let inline = matches!(node.value, Expr::Closure { .. });
        let callable = if inline {
            self.closure(ctx, ledger, handler, true)
        } else {
            self.expr(ctx, ledger, handler)
        };
        self.link_invocation(ctx, &callable);
        for effect in &callable.latent_effects {
            self.effect(ctx, effect, span);
        }
        if !inline && let Ty::Callable(signature) = self.ty(node.span) {
            for effect in &signature.effects {
                self.effect(ctx, effect, span);
            }
        }
        self.snapshot_value(span)
    }

    pub(super) fn call(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        callee_id: ExprId,
        args: &[Argument],
        span: Span,
    ) -> Datum {
        let ast = self.ast(ctx.file);
        let callee = ast.expr(callee_id);
        let id = if let Expr::Path(path) = &callee.value {
            self.definition(path.span)
        } else {
            None
        };
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
        if let Expr::Path(path) = &callee.value
            && def.is_some_and(|def| def.kind == DefinitionKind::Local)
        {
            let target = self.read_span(ctx, ledger, path.span);
            self.link_invocation(ctx, &target);
            if let Some(formal) = self.declaration(path.span)
                && ctx.reachable
                && !ctx.shadow
            {
                for (&owner, sources) in &target.invocations {
                    for &source in sources {
                        for obligation in [Obligation::Write(source), Obligation::Replace(source)] {
                            self.rules.push(Rule {
                                premises: vec![Fact { owner, obligation }],
                                conclusion: Fact {
                                    owner: ctx.owner,
                                    obligation: Obligation::Write(formal),
                                },
                            });
                        }
                    }
                }
            }
            for effect in &target.latent_effects {
                self.effect(ctx, effect, span);
            }
        }
        let syntax = id.and_then(|id| {
            let def = self.program.hir.definition(id);
            let stmt = def.stmt?;
            match &self.ast(def.name.span.file).stmt(stmt).value.kind {
                StmtKind::Function(fun) => Some(fun),
                _ => None,
            }
        });
        let mut given = vec![false; sig.map_or(args.len(), |signature| signature.parameters.len())];
        let mut values = Vec::new();
        let mut choices = Vec::new();
        for arg in args {
            let node = ast.expr(arg.value);
            let value = if matches!(node.value, Expr::Closure { .. }) {
                self.closure(ctx, ledger, arg.value, true)
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
                let mode = if arg.mode == Mode::Plain && value.requires_new {
                    Mode::New
                } else {
                    arg.mode
                };
                choices.push((
                    index,
                    match mode {
                        Mode::Ref => Input::Ref,
                        Mode::Mut => Input::Mut,
                        Mode::Shared => Input::Shared,
                        Mode::New => Input::New,
                        _ => Input::Plain,
                    },
                    node.span,
                ));
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
            if channel_payload && value.origins().any(|origin| !origin.new) {
                self.error(
                    Code::E0548,
                    node.span,
                    "channel payload requires a complete new graph",
                );
            }
            if movable_task {
                value.transform(&mut |origin| {
                    origin.confined = None;
                });
                ledger.inspect(&value);
            }
            let mode = if channel_payload { Mode::New } else { mode };
            let value = self.prepare_argument(ctx, ledger, arg, value, node.span, mode);
            if parameter.is_some_and(|p| p.ty.is_result()) {
                ledger.inspect(&value);
            } else if !value.results().is_empty()
                && (!primitive
                    || !matches!(
                        name,
                        "Some" | "Ok" | "Err" | "join" | "cancel" | "send" | "try_send"
                    ))
            {
                self.discard(ledger, &value);
            }
            if parameter.is_some_and(|p| p.is_meta) && !ctx.shadow {
                ledger.inspect(&value);
            }
            for (_, previous_mode, previous) in &values {
                if let Some(mutating) = conflicts(&value, mode, previous, *previous_mode) {
                    self.error(
                        if mutating { Code::E0523 } else { Code::E0524 },
                        node.span,
                        "argument source overlaps incompatible live authority",
                    );
                }
                if ledger.dead(previous) {
                    self.error(
                        Code::E0549,
                        node.span,
                        "argument handoff ended an earlier argument path",
                    );
                }
            }
            values.push((index, mode, value));
        }
        if !choices.is_empty()
            && let Some(callee) = id
        {
            self.mode_uses.push(ModeUse { callee, choices });
        }
        if let Some(module @ ("Fiber" | "Channel")) = module {
            return self.concurrent(ctx, ledger, (module, name), &values, args, span);
        }
        if primitive {
            if id.is_some_and(|id| self.program.hir.text_builtin(id).is_some()) {
                return if self.ty(span).is_value() {
                    Datum::default()
                } else {
                    Datum::source(span, Access::Mut, true)
                };
            }
            return self.primitive(ctx, ledger, name, &values, span);
        }
        if let Some(id) = id
            && self.program.hir.operation_effect(id).is_some()
        {
            self.use_effect(ctx, Obligation::Operation(id), span, None);
        }
        if let Some(sig) = sig {
            for effect in &sig.effects {
                if let Some(fun) = syntax.filter(|fun| fun.body.is_some()) {
                    self.link_effects(ctx, fun.name.span, effect, span);
                } else {
                    self.effect(ctx, effect, span);
                }
            }
            if sig.open_effects
                && !ctx.shadow
                && let Ty::Callable(actual) = self.ty(callee.span)
            {
                for effect in &actual.effects {
                    self.effect(ctx, effect, span);
                }
            }
        }
        if let Some(fun) = syntax {
            let lexical: BTreeSet<_> = fun
                .signature
                .obligations
                .state
                .iter()
                .filter(|clause| clause.kind == StateKind::Environment)
                .flat_map(|clause| &clause.bindings)
                .filter_map(|(_, path)| self.declaration(path.span))
                .collect();
            let enclosing = Datum {
                invocations: std::collections::BTreeMap::from([(fun.name.span, lexical)]),
                ..Datum::default()
            };
            self.link_invocation(ctx, &enclosing);
            let has_body = fun.body.is_some();
            for (index, mode, value) in &values {
                let formal = fun
                    .signature
                    .params
                    .get(*index)
                    .and_then(|param| param.name.as_ref())
                    .map(|name| name.span);
                if matches!(mode, Mode::Mut | Mode::Shared | Mode::New) {
                    let origins: BTreeSet<_> = value
                        .roots
                        .iter()
                        .flat_map(|origin| {
                            origin
                                .dependencies
                                .iter()
                                .copied()
                                .chain(std::iter::once(origin.region.source))
                        })
                        .collect();
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
                            if *mode == Mode::Shared {
                                for obligation in
                                    [Obligation::Retain(source), Obligation::Share(source)]
                                {
                                    self.rules.push(Rule {
                                        premises: vec![Fact {
                                            owner: fun.name.span,
                                            obligation: Obligation::Share(formal),
                                        }],
                                        conclusion: Fact {
                                            owner: ctx.owner,
                                            obligation,
                                        },
                                    });
                                }
                            }
                        } else if sig
                            .is_some_and(|sig| sig.state.iter().any(|state| state == "mut"))
                        {
                            self.seed(ctx, Obligation::Write(source));
                        }
                    }
                }
            }
            if fun.is_meta {
                return self.snapshot_value(span);
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
                        .source_args(fun, &values, selected)
                        .reduce(Datum::joined)
                        .unwrap_or_default();
                    result.transform(&mut |origin| {
                        origin.mode = Access::from_mode(fun.signature.result_mode);
                        origin.new = false;
                    });
                    result.requires_new = false;
                    result
                }
                Mode::Infer => self.inferred_forwarding(fun, &values, span),
                _ => self.snapshot_value(span),
            };
            for (index, (mode, source)) in sources.into_iter().enumerate() {
                if let Some(mut value) = self
                    .source_args(fun, &values, std::iter::once(source))
                    .next()
                {
                    value.transform(&mut |origin| {
                        origin.mode = mode;
                        origin.new = false;
                    });
                    result
                        .members
                        .insert(Coordinate::Index(index.to_string()), value);
                }
            }
            return result;
        }
        if let Some(def) = def
            && matches!(def.kind, DefinitionKind::Type | DefinitionKind::Variant(_))
        {
            return constructor(span, values);
        }
        if let Some(sig) = sig {
            if sig.state.iter().any(|state| state == "mut") {
                for (_, mode, value) in &values {
                    if matches!(mode, Mode::Mut | Mode::Shared) {
                        self.mutate(ctx, ledger, value, span);
                    }
                }
            }
            if sig.result_mode == Mode::New {
                return Datum::source(span, Access::Mut, true);
            }
        }
        self.snapshot_value(span)
    }

    pub(super) fn link_invocation(&mut self, ctx: &Context, target: &Datum) {
        self.link_invocation_if(ctx, target, None);
    }

    pub(super) fn link_invocation_if(
        &mut self,
        ctx: &Context,
        target: &Datum,
        if_exercised: Option<&Fact>,
    ) {
        if !ctx.reachable || ctx.shadow {
            return;
        }
        for (&owner, sources) in &target.invocations {
            for &source in sources {
                for obligation in [Obligation::Write(source), Obligation::Replace(source)] {
                    self.rules.push(Rule {
                        premises: std::iter::once(Fact {
                            owner,
                            obligation: obligation.clone(),
                        })
                        .chain(if_exercised.cloned())
                        .collect(),
                        conclusion: Fact {
                            owner: ctx.owner,
                            obligation,
                        },
                    });
                }
            }
        }
    }

    fn link_effects(&mut self, ctx: &Context, owner: Span, effect: &str, span: Span) {
        let hir = &self.program.hir;
        let obligations = hir.effect_by_label(effect).map_or_else(
            || vec![Obligation::Effect(effect.into())],
            |id| {
                hir.included_effects(id)
                    .map(|id| Obligation::Effect(hir.effect_label(id)))
                    .chain(hir.effect_operations(id).map(Obligation::Operation))
                    .collect()
            },
        );
        for obligation in obligations {
            let prerequisite = Fact {
                owner,
                obligation: obligation.clone(),
            };
            self.use_effect(ctx, obligation, span, Some(prerequisite));
        }
    }

    fn source_args<'a>(
        &self,
        fun: &'a ril_frontend::syntax::Function,
        values: &'a [(usize, Mode, Datum)],
        sources: impl Iterator<Item = Span> + 'a,
    ) -> impl Iterator<Item = Datum> + 'a {
        sources.filter_map(move |name| {
            let i = fun
                .signature
                .params
                .iter()
                .position(|param| param.name.as_ref().is_some_and(|n| n.span == name))?;
            values
                .iter()
                .find(|(index, _, _)| *index == i)
                .map(|(_, _, value)| value.clone())
        })
    }

    fn inferred_forwarding(
        &self,
        fun: &ril_frontend::syntax::Function,
        values: &[(usize, Mode, Datum)],
        span: Span,
    ) -> Datum {
        // The flow of a single via input is preserved even across local rebinding.
        let mut inputs = fun
            .signature
            .params
            .iter()
            .enumerate()
            .filter(|(_, param)| param.mode == Mode::Via);
        if let (Some((index, _)), None) = (inputs.next(), inputs.next())
            && let Some((_, mode, value)) = values.iter().find(|(formal, _, _)| *formal == index)
        {
            let mut result = value.clone();
            for root in &mut result.roots {
                root.mode = Access::from_mode(*mode);
            }
            return result;
        }
        self.snapshot_value(span)
    }

    fn prepare_argument(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        arg: &Argument,
        mut value: Datum,
        span: Span,
        mode: Mode,
    ) -> Datum {
        match mode {
            Mode::New => self.handoff(ctx, ledger, &mut value, span),
            Mode::Mut | Mode::Shared => {
                if !matches!(
                    self.ast(ctx.file).expr(arg.value).value,
                    Expr::Path(_) | Expr::Member { .. } | Expr::Index { .. }
                ) {
                    self.error(
                        Code::E0410,
                        span,
                        "mutable argument requires an addressable path",
                    );
                } else if !value.writers() {
                    self.error(Code::E0520, span, "argument path has no writable authority");
                }
                if mode == Mode::Shared && value.origins().any(|origin| origin.confined.is_some()) {
                    self.error(Code::E0604, span, "resource authority cannot be retained");
                }
            }
            Mode::Plain
                if matches!(self.ty(span), Ty::Callable(_)) || value.task_scope.is_some() => {}
            Mode::Plain => {
                if !value.requires_new
                    && !self.ty(span).is_value()
                    && value
                        .origins()
                        .any(|origin| origin.mode != Access::Immutable)
                {
                    self.error(
                        Code::E0535,
                        span,
                        "live authority cannot enter a plain argument",
                    );
                }
                value.transform(&mut |origin| {
                    origin.mode = Access::Immutable;
                });
                value.requires_new = false;
            }
            _ => {}
        }
        value
    }

    fn snapshot_value(&self, span: Span) -> Datum {
        if self.ty(span).is_value() {
            Datum::default()
        } else {
            Datum::source(span, Access::Immutable, false)
        }
    }

    fn primitive(
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
            "println" | "print" => self.effect(ctx, "io", span),
            "push" | "pop" | "insert" | "remove" | "clear" => {
                if let Some(value) = first {
                    self.mutate(ctx, ledger, value, span);
                }
            }
            "clone" => {
                if first.is_some_and(|value| {
                    value.creates_environment()
                        && value
                            .origins()
                            .any(|origin| origin.mode != Access::Immutable)
                }) {
                    self.error(Code::E0530, span, "cannot clone live callable authority");
                }
                return Datum::source(span, Access::Mut, true);
            }
            "inner" => {
                return first
                    .map(|value| value.project(Coordinate::Index("0".into()), Access::Mut))
                    .unwrap_or_default();
            }
            "derive" => {
                if let Some((_, _, callback)) = args.iter().find(|(i, _, _)| *i == 1) {
                    self.link_invocation(ctx, callback);
                    for effect in &callback.latent_effects {
                        self.effect(ctx, effect, span);
                    }
                }
                if first.is_some_and(|value| {
                    value
                        .origins()
                        .any(|origin| origin.mode != Access::Immutable)
                }) {
                    self.error(Code::E0536, span, "derive requires an immutable snapshot");
                }
            }
            "absorb_panic" => {
                if first.is_some_and(|value| {
                    !value.latent_effects.is_empty()
                        || value.stateful_handler
                        || value
                            .origins()
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
            "Some" | "Ok" | "Err" => return constructor(span, args.iter().cloned()),
            "yield" | "sleep" | "scope" | "spawn" | "join" | "send" | "recv" => {
                self.effect(ctx, "fiber", span);
            }
            "read" | "open" | "close" | "write" => self.effect(ctx, "io", span),
            _ => {}
        }
        self.snapshot_value(span)
    }

    fn concurrent(
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
                self.effect(ctx, "fiber", span);
            }
            if matches!(name, "sleep" | "sleep_ms" | "timeout_ms") {
                self.effect(ctx, "io", span);
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
                    v.stateful_handler || !v.latent_effects.is_empty() || !v.members.is_empty()
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
                    if callback.stateful_handler {
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
                                && !origin.dependencies.iter().any(|id| moved.contains(id))
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
                            ledger.revoked.insert(decl);
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
                        self.effect(ctx, effect, span);
                    }
                }
            }
            if name == "spawn" {
                let scope = first
                    .and_then(|value| value.roots.first())
                    .map(|origin| origin.region.source);
                let mut output = Datum::source(span, Access::Mut, true);
                output.task_scope = scope;
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
            }
            return self.snapshot_value(span);
        }
        if matches!(name, "send" | "recv") {
            self.effect(ctx, "fiber", span);
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

    pub(super) fn handlers(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        handlers: &[Handler],
    ) {
        let mut operations = BTreeSet::new();
        let mut installed = std::collections::BTreeMap::new();
        for handler in handlers {
            let id = self.definition(handler.operation.span);
            let span = handler.operation.span;
            if let Some(id) = id
                && self.program.hir.operation_effect(id).is_some()
            {
                if !operations.insert(id) {
                    self.error(Code::E0622, span, "duplicate operation in handler group");
                }
            } else {
                self.error(
                    Code::E0621,
                    span,
                    "handler must target a user effect operation",
                );
            }
            let value = if matches!(
                self.ast(ctx.file).expr(handler.value).value,
                Expr::Closure { .. }
            ) {
                self.closure(ctx, ledger, handler.value, true)
            } else {
                self.expr(ctx, ledger, handler.value)
            };
            if matches!(handler.mode, Mode::Ref | Mode::Mut | Mode::Shared) {
                ledger.holds.push(value.clone());
            }
            if let Some(id) = id {
                installed.insert(id, value);
            }
        }
        ctx.handlers.extend(installed);
    }

    pub(super) fn closure(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        id: ExprId,
        contextual: bool,
    ) -> Datum {
        let node = self.ast(ctx.file).expr(id);
        let Expr::Closure {
            params,
            body,
            obligations,
        } = &node.value
        else {
            return Datum::default();
        };
        let mut locals = ledger.clone();
        let mut inner = Context::new(node.span);
        inner.in_function = true;
        inner.runtime = ctx.runtime;
        inner.shadow = ctx.shadow;
        inner.reachable = ctx.reachable;
        inner.handlers.clone_from(&ctx.handlers);
        inner.via.clone_from(&ctx.via);
        inner.formals = params
            .iter()
            .map(|param| param.name.as_ref().map(|name| name.span))
            .collect();
        if obligations.open_effects || obligations.open_state {
            self.error(
                Code::E0547,
                node.span,
                "closure definition cannot open its annotations",
            );
        }
        if obligations
            .state
            .iter()
            .any(|clause| clause.kind == StateKind::Environment && !clause.bindings.is_empty())
        {
            self.error(Code::E0538, node.span, "closure captures are inferred");
        }
        for p in params {
            if let Some(name) = &p.name {
                let mode = Access::from_mode(p.mode);
                let mut value = Datum::source(name.span, mode, p.mode == Mode::New);
                let param_ty = self
                    .definition(name.span)
                    .and_then(|id| self.program.bindings.get(&id));
                value.transform(&mut |origin| {
                    origin.dependencies.insert(name.span);
                    if matches!(param_ty, Some(Ty::Scope | Ty::Draft(_))) {
                        origin.confined = Some(node.span);
                        origin.draft = matches!(param_ty, Some(Ty::Draft(_)));
                    }
                });
                locals.slots.insert(
                    name.span,
                    Slot {
                        decl: name.span,
                        variable: false,
                        mode: p.mode,
                        value,
                    },
                );
                let exempt = contextual && name.value.starts_with('_');
                if matches!(p.mode, Mode::Mut | Mode::Shared) && !exempt {
                    self.requirement(
                        &inner,
                        name.span,
                        if p.mode == Mode::Shared {
                            Obligation::Retain(name.span)
                        } else {
                            Obligation::Write(name.span)
                        },
                        "closure parameter authority is unused",
                    );
                }
            }
        }
        let before = self.rules.len();
        let output = self.expr(&mut inner, &mut locals, *body);
        if output.origins().any(|origin| origin.draft) {
            self.error(Code::E0607, node.span, "draft escapes update callback");
        } else if output.origins().any(|origin| origin.confined.is_some()) {
            self.error(
                Code::E0604,
                node.span,
                "closure result escapes its confinement",
            );
        }
        let used: BTreeSet<_> = self
            .rules
            .iter()
            .skip(before)
            .filter_map(|rule| {
                if rule.conclusion.owner == inner.owner
                    && let Obligation::ReadUp(span) = rule.conclusion.obligation
                {
                    Some(span)
                } else {
                    None
                }
            })
            .collect();
        let mut closure = Datum::source(node.span, Access::Immutable, false);
        for (index, slot) in used
            .iter()
            .filter_map(|span| ledger.slots.get(span))
            .enumerate()
        {
            if slot.value.origins().any(|origin| origin.confined.is_some()) {
                self.error(
                    Code::E0604,
                    node.span,
                    "closure cannot capture a scoped resource",
                );
            }
            let mut value = slot.value.clone();
            if slot.variable {
                let mut origin = Datum::source(slot.decl, Access::Mut, false);
                origin.transform(&mut |origin| {
                    origin.dependencies.insert(slot.decl);
                });
                value = value.joined(origin);
            }
            closure
                .members
                .insert(Coordinate::Index(index.to_string()), value);
        }
        closure.latent_effects = self
            .rules
            .iter()
            .skip(before)
            .filter(|rule| rule.conclusion.owner == inner.owner)
            .filter_map(|rule| match &rule.conclusion.obligation {
                Obligation::Effect(effect) => Some(effect.clone()),
                Obligation::Operation(operation) => self
                    .program
                    .hir
                    .operation_effect(*operation)
                    .map(|effect| self.program.hir.effect_label(effect)),
                _ => None,
            })
            .collect();
        if !closure.members.is_empty() {
            closure.environments.insert(node.span);
            closure.invocations.insert(inner.owner, used);
        }
        closure.stateful_handler = self.rules.iter().skip(before).any(|rule| {
            rule.conclusion.owner == inner.owner
                && rule.conclusion.obligation == Obligation::StatefulHandler
        });
        closure
    }
}

fn constructor(span: Span, values: impl IntoIterator<Item = (usize, Mode, Datum)>) -> Datum {
    let mut result = Datum::source(span, Access::Mut, true);
    for (index, _, value) in values {
        result
            .members
            .insert(Coordinate::Index(index.to_string()), value);
    }
    result
}
