use std::collections::BTreeSet;

use ril_base::{diag::Code, span::Span};
use ril_frontend::{
    hir::DefinitionKind,
    syntax::{Argument, Expr, ExprId, Handler, Mode, StateKind, StmtKind},
};

use crate::ty::Ty;

use super::{
    Access, Analyzer, Context, Coordinate, Datum, Fact, Ledger, Obligation, Rule, Slot, conflicts,
};

impl Analyzer<'_> {
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
        let sig = id
            .and_then(|id| self.program.callables.get(&id).map(|s| s.as_ref()))
            .or_else(|| match self.ty(callee.span) {
                Ty::Callable(sig) => Some(sig.as_ref()),
                _ => None,
            });
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
            let mode = if parameter.is_some_and(|p| p.mode == Mode::Via) {
                arg.mode
            } else {
                parameter.map_or(arg.mode, |p| p.mode)
            };
            let value = self.prepare_argument(ctx, ledger, arg, value, node.span, mode);
            if parameter.is_some_and(|p| p.ty.is_result()) {
                ledger.inspect(&value);
            } else if !value.results().is_empty()
                && (!primitive || !matches!(name, "Some" | "Ok" | "Err"))
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
        if primitive {
            return self.primitive(ctx, ledger, name, &values, span);
        }
        if let Some(id) = id
            && let Some(effect) = self.program.hir.effect_of(id)
        {
            self.effect(ctx, effect, span);
        }
        if let Some(sig) = sig {
            for effect in &sig.effects {
                self.effect(ctx, effect, span);
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
                return Datum::source(span, Access::Mut, true);
            }
            "inner" => {
                return first
                    .map(|value| value.project(Coordinate::Index("0".into()), Access::Mut))
                    .unwrap_or_default();
            }
            "derive" => {
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
                    value
                        .origins()
                        .any(|origin| origin.mode != Access::Immutable)
                }) {
                    self.error(
                        Code::E0608,
                        span,
                        "panic containment cannot capture live outer state",
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

    pub(super) fn handlers(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        handlers: &[Handler],
    ) {
        let mut operations = BTreeSet::new();
        let mut installed = BTreeSet::new();
        for handler in handlers {
            let id = self.definition(handler.operation.span);
            let effect = id.and_then(|id| self.program.hir.effect_of(id));
            let span = handler.operation.span;
            if let Some(id) = id
                && effect.is_some()
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
                ledger.holds.push(value);
            }
            if let Some(effect) = effect {
                installed.insert(effect.to_owned());
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
                value.transform(&mut |origin| {
                    origin.dependencies.insert(name.span);
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
        self.expr(&mut inner, &mut locals, *body);
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
            closure
                .members
                .insert(Coordinate::Index(index.to_string()), slot.value.clone());
        }
        if !contextual && !closure.members.is_empty() {
            self.seed(ctx, Obligation::Capture);
        }
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
