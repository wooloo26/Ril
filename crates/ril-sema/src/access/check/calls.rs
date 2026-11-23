use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
};

use ril_base::{
    diag::{Code, Diagnostic},
    span::Span,
};
use ril_frontend::{
    hir::{DefinitionId, DefinitionKind},
    syntax::{Argument, Expr, ExprId, Function, Handler, Mode, StateKind, StmtKind},
};

use crate::{
    access::{
        CallbackArgument, CallbackReturn, InvocationMode, ReturnSource,
        flow::{CallbackOrigin, Handoff, Revocation},
    },
    ty::{Callable, Ty},
};

use super::{
    Access, Analyzer, CaptureConflict, ClosureModes, Context, Coordinate, Datum, Fact, Input,
    Ledger, ModeUse, Obligation, Region, Rule, SchemaRequirement, Slot, conflicts, member_axes,
    storage::CallStorage,
};
use crate::access::flow::InvocationSite;

mod imported;

type CallArgument = (usize, Mode, Datum);

struct CallEntry<'a> {
    arguments: &'a [CallArgument],
    spans: &'a [Span],
    ledger: &'a Ledger,
    span: Span,
    invocation: &'a [InvocationSite],
}

#[derive(Clone, Eq, PartialEq)]
pub(super) struct CallbackResult {
    receiver: Datum,
    arguments: Vec<(usize, Mode, Datum)>,
    spans: Vec<Span>,
    site: Vec<InvocationSite>,
    ordinal: usize,
}

impl CallbackResult {
    fn values(&self) -> impl Iterator<Item = &Datum> {
        std::iter::once(&self.receiver).chain(self.arguments.iter().map(|(_, _, value)| value))
    }

    fn values_mut(&mut self) -> impl Iterator<Item = &mut Datum> {
        std::iter::once(&mut self.receiver)
            .chain(self.arguments.iter_mut().map(|(_, _, value)| value))
    }
}

/// A call's return, stores and deferred invocations can expose the same
/// allocation. Number their identities together before publishing any of them.
pub(super) fn seal_call_allocations<'d>(
    pool: &mut Vec<CallbackResult>,
    outputs: impl Iterator<Item = &'d mut Datum>,
    body: Span,
) {
    let mut outputs: Vec<_> = outputs.collect();
    let references = |value: &Datum| {
        value
            .origins()
            .filter_map(|origin| origin.callback_result.map(|result| result.template))
            .collect::<BTreeSet<_>>()
    };
    let mut remaining: BTreeSet<_> = outputs.iter().flat_map(|value| references(value)).collect();
    let mut callbacks = BTreeMap::new();
    while let Some(index) = remaining.pop_first() {
        if callbacks.contains_key(&index) {
            continue;
        }
        let Some(callback) = pool.get(index) else {
            continue;
        };
        remaining.extend(callback.values().flat_map(references));
        callbacks.insert(index, callback.clone());
    }
    Datum::mark_call_allocations(
        outputs
            .iter_mut()
            .map(|value| &mut **value)
            .chain(callbacks.values_mut().flat_map(CallbackResult::values_mut)),
        body,
    );
    let ordinals: BTreeMap<_, _> = callbacks
        .values()
        .map(|callback| callback.site.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .enumerate()
        .map(|(ordinal, site)| (site, ordinal))
        .collect();
    let mut mapped = BTreeMap::new();
    let remap = |value: &mut Datum, mapped: &BTreeMap<usize, usize>| {
        value.transform(&mut |origin| {
            if let Some(result) = &mut origin.callback_result
                && let Some(&index) = mapped.get(&result.template)
            {
                result.template = index;
            }
        });
    };
    // A template refers only to templates already present when it was interned.
    for (old, mut callback) in callbacks {
        for value in callback.values_mut() {
            remap(value, &mapped);
        }
        if let Some(&ordinal) = ordinals.get(&callback.site) {
            callback.ordinal = ordinal;
        }
        mapped.insert(old, intern_callback(pool, callback));
    }
    for output in outputs {
        remap(output, &mapped);
    }
}

fn intern_callback(pool: &mut Vec<CallbackResult>, template: CallbackResult) -> usize {
    if let Some(index) = pool.iter().position(|known| *known == template) {
        return index;
    }
    let index = pool.len();
    pool.push(template);
    index
}

impl<'program> Analyzer<'program> {
    fn function_syntax(&self, id: DefinitionId) -> Option<&'program Function> {
        let def = self.program.hir.definition(id);
        let stmt = def.stmt?;
        match &self.ast(def.name.span.file).stmt(stmt).value.kind {
            StmtKind::Function(fun) => Some(fun),
            _ => None,
        }
    }

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
            self.effect(ctx, ledger, effect, span);
        }
        if !inline && let Ty::Callable(signature) = self.ty(node.span) {
            for effect in &signature.effects {
                self.effect(ctx, ledger, effect, span);
            }
        }
        self.snapshot_value(span)
    }

    pub(super) fn call(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        callee: ExprId,
        args: &[Argument],
        span: Span,
    ) -> Datum {
        let result = self.call_value(ctx, ledger, callee, args, span);
        ledger.remember_return_graph(&result, span);
        result
    }

    fn call_value(
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
        let target = (id.is_none() || def.is_some_and(|def| def.kind == DefinitionKind::Local))
            .then(|| self.expr(ctx, ledger, callee_id));
        let closures: BTreeMap<_, _> = target
            .iter()
            .flat_map(|target| &target.roots)
            .filter(|root| root.region.selection.is_empty())
            .filter_map(|origin| {
                let owner = origin.region.source;
                self.closure_modes
                    .get(&owner)
                    .map(|modes| (owner, modes.clone()))
            })
            .collect();
        let has_via_closures = closures
            .values()
            .any(|modes| !modes.via.is_empty() || !modes.member_axes.is_empty());
        let all_closures_known = target.as_ref().is_some_and(|target| {
            !target.roots.is_empty()
                && target.roots.iter().all(|root| {
                    root.region.selection.is_empty() && closures.contains_key(&root.region.source)
                })
        });
        let aliases: BTreeMap<_, _> = target
            .iter()
            .flat_map(|target| &target.roots)
            .filter(|root| root.region.selection.is_empty())
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
                    root.region.selection.is_empty()
                        && (aliases.contains_key(&root.region.source)
                            || closures.contains_key(&root.region.source))
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
            self.link_invocation(ctx, target);
            for source in target.root_dependencies() {
                self.seed(ctx, Obligation::Invoke(source));
            }
            for effect in &target.latent_effects {
                self.effect(ctx, ledger, effect, span);
            }
        }
        let syntax = id.and_then(|id| self.function_syntax(id));
        let indirect_template = target.as_ref().is_some_and(|target| {
            target.roots.iter().any(|root| {
                root.region.selection.is_empty()
                    && (ctx.formals.contains(&Some(root.region.source))
                        || self.definition(root.region.source).is_some_and(|id| {
                            self.program.hir.definition(id).kind == DefinitionKind::Function
                        }))
            })
        });
        let is_constructor = primitive && matches!(name, "Some" | "Ok" | "Err")
            || def.is_some_and(|def| {
                matches!(def.kind, DefinitionKind::Type | DefinitionKind::Variant(_))
            });
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
                            || id.is_some_and(|id| {
                                self.program.imported_functions.contains_key(&id)
                            })
                            || has_via_closures
                            || all_aliases_known)
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
            let value = self.prepare_argument(ctx, ledger, arg, value, node.span, mode);
            // Packing preserves inspection obligations in the payload.
            if !is_constructor {
                if parameter.is_some_and(|p| p.ty.is_result()) {
                    ledger.inspect(&value);
                } else if !value.results().is_empty()
                    && (!primitive || !matches!(name, "join" | "cancel" | "send" | "try_send"))
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
            },
        );
        for (i, ((_, mode, value), &argument_span)) in values.iter().zip(&value_spans).enumerate() {
            if let Some(mutating) = ledger.hold_conflict(value, *mode) {
                self.error(
                    if mutating { Code::E0523 } else { Code::E0524 },
                    argument_span,
                    "argument authority overlaps an active handler hold",
                );
            }
            for (_, previous_mode, previous) in values.iter().take(i) {
                if let Some(mutating) = conflicts(value, *mode, previous, *previous_mode) {
                    self.error(
                        if mutating { Code::E0523 } else { Code::E0524 },
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
            if (!modes.via.is_empty() || !modes.member_axes.is_empty())
                && let Some(signature) = sig
            {
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
            let inserted = match (module, name) {
                (Some("Array"), "push") => Some(1),
                (Some("Map"), "insert") => Some(2),
                _ => None,
            };
            if let Some(inserted) = inserted
                && let Some(((.., mode, value), &value_span)) = values
                    .iter()
                    .zip(&value_spans)
                    .find(|((index, _, _), _)| *index == inserted)
            {
                self.check_stored_views(value, *mode == Mode::Ref, value_span);
            }
            return self.primitive(ctx, ledger, name, &values, span);
        }
        if let (Some(id), Expr::Path(path)) = (id, &callee.value)
            && let Some(operation) = self.operation(id, path.span)
        {
            self.use_effect(ctx, ledger, Obligation::Operation(operation), span, None);
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
            return self.named_call(ctx, ledger, fun, sig, (&values, &value_spans), span);
        }
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
                let mut result =
                    self.named_call(ctx, &mut after, fun, actual, (&values, &value_spans), span);
                if !after.no_continuation {
                    if sig.is_some_and(|signature| signature.result_mode == Mode::Plain)
                        && fun.signature.result_mode == Mode::New
                    {
                        result = self.snapshot_value(span);
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
                };
                let mut receiver = receiver.clone();
                receiver
                    .roots
                    .retain(|root| closures.contains_key(&root.region.source));
                let mut result = self
                    .callback_return(&receiver, &entry)
                    .unwrap_or_else(|| self.snapshot_value(span));
                if sig.is_some_and(|signature| signature.result_mode == Mode::Plain)
                    && result.requires_new
                {
                    result = self.snapshot_value(span);
                }
                outputs.push(result);
                alternatives.push(
                    self.closure_storage(ctx, &closures, &entry)
                        .unwrap_or_else(|| before.clone()),
                );
            }
            ledger.merge(&before, &alternatives);
            return outputs
                .into_iter()
                .reduce(Datum::joined)
                .unwrap_or_default();
        }
        let before_updates = if all_closures_known {
            self.closure_storage(
                ctx,
                &closures,
                &CallEntry {
                    arguments: &values,
                    spans: &value_spans,
                    ledger,
                    span,
                    invocation: &[],
                },
            )
        } else {
            None
        }
        .map(|after| std::mem::replace(ledger, after));
        if has_via_closures
            && all_closures_known
            && let Some(target) = &target
        {
            let entry = CallEntry {
                arguments: &values,
                spans: &value_spans,
                ledger: before_updates.as_ref().unwrap_or(ledger),
                span,
                invocation: &[],
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
            if sig.result_mode == Mode::New {
                return Datum::source(span, Access::Mut, true);
            }
            if sig.result_mode == Mode::Infer
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
                };
                if let Some(result) = self.callback_return(&receiver, &entry) {
                    return result;
                }
                return self.defer_callback_result(
                    CallbackResult {
                        receiver,
                        arguments: values,
                        spans: value_spans,
                        site: vec![InvocationSite { span, ordinal: 0 }],
                        ordinal: 0,
                    },
                    span,
                );
            }
        }
        self.snapshot_value(span)
    }

    fn named_call(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        fun: &Function,
        sig: Option<&'program Callable>,
        (values, value_spans): (&[(usize, Mode, Datum)], &[Span]),
        span: Span,
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
                    (values, value_spans, span),
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
                if !storage.updates.is_empty() {
                    let frozen = ledger.clone();
                    modeled_stores = self.apply_storage_updates(
                        ctx,
                        storage,
                        &CallEntry {
                            arguments: values,
                            spans: value_spans,
                            ledger: &frozen,
                            span,
                            invocation: &[],
                        },
                        ledger,
                    );
                    before_updates = Some(frozen);
                }
            }
        }
        if has_body && let Some(signature) = sig {
            let formals: Vec<_> = fun
                .signature
                .params
                .iter()
                .map(|param| param.name.as_ref().map(|name| name.span))
                .collect();
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
        for (index, mode, value) in values {
            let formal = fun
                .signature
                .params
                .get(*index)
                .and_then(|param| param.name.as_ref())
                .map(|name| name.span);
            if let Some(formal) = formal.filter(|_| has_body) {
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
        ) {
            self.function(fun, ledger);
            let entry = CallEntry {
                arguments: values,
                spans: value_spans,
                ledger: before_updates.as_ref().unwrap_or(ledger),
                span,
                invocation: &[],
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

    fn applied_effect<'p>(&'p self, declaration: usize, template: &'p str, span: Span) -> &'p str {
        self.program
            .effect_applications
            .get(&span)
            .and_then(|effects| effects.get(declaration))
            .map_or(template, String::as_str)
    }

    fn charge_call_effects(
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

    pub(super) fn link_invocation(&mut self, ctx: &Context, target: &Datum) {
        self.link_invocation_if(ctx, target, None);
    }

    fn check_capture_overlap(
        &mut self,
        ctx: &Context,
        function: Option<&ril_frontend::syntax::Function>,
        target: Option<&Datum>,
        entry: &CallEntry<'_>,
    ) {
        let overlap_code = |mutating| if mutating { Code::E0523 } else { Code::E0524 };
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
            let captured = entry.ledger.snapshot(&slot.value);
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
                if let Some(code) = conflicts(argument, *mode, &captured, access).map(overlap_code)
                {
                    self.error(code, span, "argument authority overlaps a callable capture");
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
                        let reading =
                            conflicts(argument, *mode, &captured, Mode::Ref).map(overlap_code);
                        let writing =
                            conflicts(argument, *mode, &captured, writable).map(overlap_code);
                        if reading.is_some() || writing.is_some() {
                            self.capture_conflicts.push(CaptureConflict {
                                write: Fact {
                                    owner,
                                    obligation: Obligation::Write(source),
                                },
                                reading,
                                writing,
                                span,
                            });
                        }
                    }
                }
            }
        }
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

    fn link_effects(
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
        // Recursive calls may precede completion of their own return template.
        // Keep every possible formal source and avoid promising fresh ownership.
        values
            .iter()
            .filter_map(|(index, _, value)| {
                fun.signature
                    .params
                    .get(*index)
                    .filter(|formal| formal.mode == Mode::Via)
                    .map(|_| value.clone())
            })
            .reduce(Datum::joined)
            .map_or_else(
                || self.snapshot_value(span),
                |mut value| {
                    value.requires_new = false;
                    value
                },
            )
    }

    fn return_template(
        &mut self,
        fun: &ril_frontend::syntax::Function,
        entry: &CallEntry<'_>,
    ) -> Option<Datum> {
        let (formals, via, returns) = if let Some(definition) = self
            .functions
            .iter()
            .find(|definition| definition.owner == fun.name.span)
        {
            (
                definition.formals.clone(),
                definition.via.clone(),
                definition.returns.clone(),
            )
        } else {
            let provisional = self.recursive_storage.get(&fun.name.span)?.clone();
            (
                provisional.formals,
                provisional.via,
                provisional.result.into_iter().collect(),
            )
        };
        returns
            .iter()
            .map(|datum| self.instantiate_return(&formals, &via, entry, datum, &mut Vec::new()))
            .reduce(Datum::joined)
    }

    fn apply_storage_updates(
        &mut self,
        ctx: &Context,
        storage: CallStorage,
        entry: &CallEntry<'_>,
        ledger: &mut Ledger,
    ) -> bool {
        let CallStorage {
            formals,
            via,
            updates,
            ..
        } = storage;
        let mut applied = true;
        for (index, (region, update)) in updates.into_iter().enumerate() {
            let mut output_path = vec![Coordinate::Index(index.to_string())];
            let Some((member, parent)) = region.selection.split_last() else {
                let mut stored =
                    self.instantiate_return(&formals, &via, entry, &update.value, &mut output_path);
                ledger.remember_return_graph(&stored, entry.span);
                self.check_stored_views(&stored, false, entry.span);
                if ctx.caller_slots.contains(&region.source) {
                    stored.publications.insert(ctx.owner, true);
                }
                stored.transform(&mut |origin| {
                    origin.dependencies.insert(region.source.into());
                });
                applied &= ledger.replace_slot(region.source, stored, update.definite);
                continue;
            };
            let Some(formal) = formals
                .iter()
                .position(|formal| *formal == Some(region.source))
            else {
                applied = false;
                continue;
            };
            let Some(((_, _, actual), &argument_span)) = entry
                .arguments
                .iter()
                .zip(entry.spans)
                .find(|((index, _, _), _)| *index == formal)
            else {
                applied = false;
                continue;
            };

            let mut value = actual.clone();
            let mut ty = self.ty(argument_span);
            for coordinate in parent {
                let schema = self.schema_member(ty, coordinate);
                let mode = schema.map_or(Mode::Plain, |member| member.mode.mode);
                value = entry
                    .ledger
                    .project_schema(&value, coordinate.clone(), mode);
                ty = schema.map_or(&Ty::Unknown, |member| &member.ty);
            }
            let place = value.slot_projection(member.clone());
            applied &= !place.roots.is_empty();
            let mut stored =
                self.instantiate_return(&formals, &via, entry, &update.value, &mut output_path);
            ledger.remember_return_graph(&stored, entry.span);
            self.check_stored_views(&stored, false, entry.span);
            stored
                .publications
                .insert(ctx.owner, place.roots.iter().any(|origin| !origin.new));
            ledger.replace_member(&place, stored, update.definite);
        }
        applied
    }

    fn closure_storage(
        &mut self,
        ctx: &Context,
        closures: &BTreeMap<Span, ClosureModes>,
        entry: &CallEntry<'_>,
    ) -> Option<Ledger> {
        if !ctx.runtime
            || ctx.shadow
            || !ctx.reachable
            || closures.values().all(|closure| closure.updates.is_empty())
        {
            return None;
        }
        let alternatives: Vec<_> = closures
            .values()
            .map(|closure| {
                let storage = CallStorage {
                    formals: closure.formals.clone(),
                    via: closure.via.clone(),
                    updates: closure.updates.clone(),
                    ..CallStorage::default()
                };
                let mut after = entry.ledger.clone();
                self.apply_storage_updates(ctx, storage, entry, &mut after);
                after
            })
            .collect();
        let mut after = entry.ledger.clone();
        after.merge(entry.ledger, &alternatives);
        Some(after)
    }

    fn instantiate_return(
        &mut self,
        formals: &[Option<Span>],
        via_formals: &BTreeSet<Span>,
        entry: &CallEntry<'_>,
        template: &Datum,
        output_path: &mut Vec<Coordinate>,
    ) -> Datum {
        let mut output = template
            .roots
            .iter()
            .filter_map(|origin| {
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
                    let mut ty = self.ty(origin.region.source);
                    for step in &origin.region.selection {
                        let member = self.schema_member(ty, step);
                        let mode = member.map_or(Mode::Plain, |member| member.mode.mode);
                        value = callback_ledger.project_schema(&value, step.clone(), mode);
                        ty = member.map_or(&Ty::Unknown, |member| &member.ty);
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
                        let mut ty = self.ty(argument_span);
                        for coordinate in &origin.region.selection {
                            let member = self.schema_member(ty, coordinate);
                            let mode = member.map_or(Mode::Plain, |member| member.mode.mode);
                            actual = entry
                                .ledger
                                .project_schema(&actual, coordinate.clone(), mode);
                            ty = member.map_or(&Ty::Unknown, |member| &member.ty);
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
        for (coordinate, member) in &template.members {
            output_path.push(coordinate.clone());
            let specialized =
                self.instantiate_return(formals, via_formals, entry, member, output_path);
            output_path.pop();
            output.members.insert(coordinate.clone(), specialized);
        }
        output
            .latent_effects
            .extend(template.latent_effects.iter().cloned());
        output.stateful_handler |= template.stateful_handler;
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
        output
    }

    fn defer_callback_result(&mut self, callback: CallbackResult, span: Span) -> Datum {
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

    fn callback_template(&mut self, template: CallbackResult) -> usize {
        intern_callback(&mut self.callback_results, template)
    }

    pub(super) fn callback_return_contracts(
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
                .map(|(position, mode, value)| {
                    let modes = if let Some(input) = Input::from_mode(*mode) {
                        vec![InvocationMode::Input(input)]
                    } else {
                        value
                            .roots
                            .iter()
                            .filter(|root| root.inherits_mode)
                            .filter_map(|root| {
                                formal_index(root.region.source).map(InvocationMode::Formal)
                            })
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
                        allocations: Datum::return_allocations(std::slice::from_ref(value)),
                        constructs: value.requires_new,
                    }
                })
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

    fn instantiate_callback_result<'e>(
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
            .unwrap_or_else(|| ril_base::ice!("missing callback return template"));
        let receiver = self.instantiate_return(formals, via, entry, &receiver, &mut Vec::new());
        for ((_, mode, argument), span) in arguments.iter_mut().zip(&mut spans) {
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
            *argument = self.instantiate_return(formals, via, entry, argument, &mut Vec::new());
            if matches!(mode, Mode::Ref | Mode::Shared) {
                for root in &mut argument.roots {
                    root.fix_mode(root.mode.project(Access::from_mode(*mode)));
                    root.new = false;
                }
                argument.requires_new = false;
            }
        }
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

    fn callback_return(&mut self, receiver: &Datum, entry: &CallEntry<'_>) -> Option<Datum> {
        let mut outputs = Vec::new();
        for target in &receiver.roots {
            if !target.region.selection.is_empty() {
                return None;
            }
            let span = target.region.source;
            if let Some(closure) = self.closure_modes.get(&span).cloned() {
                for value in &closure.returns {
                    outputs.push(self.instantiate_return(
                        &closure.formals,
                        &closure.via,
                        entry,
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

    fn link_schema_argument(
        &mut self,
        ctx: &Context,
        owner: Span,
        axis: Region,
        argument: &Datum,
        span: Span,
    ) {
        let mut ty = self.ty(span);
        let mut mode = Mode::Plain;
        for coordinate in &axis.selection {
            let Some(member) = self.schema_member(ty, coordinate) else {
                return;
            };
            mode = member.mode.mode;
            ty = &member.ty;
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

    fn forward_handoff(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        value: &Datum,
        (owner, formal): Handoff,
    ) {
        if !ctx.reachable {
            return;
        }
        for root in &value.roots {
            if !ctx.shadow {
                for obligation in [Obligation::Handoff, Obligation::NeedsSharing] {
                    self.rules.push(Rule {
                        premises: vec![Fact {
                            owner,
                            obligation: obligation(formal),
                        }],
                        conclusion: Fact {
                            owner: ctx.owner,
                            obligation: obligation(root.region.source),
                        },
                    });
                }
            }
            for &token in &root.dependencies {
                ledger.revoke(token, Some(root), Some(Revocation::Formal((owner, formal))));
            }
        }
    }

    fn link_via_projection(
        &mut self,
        ctx: &Context,
        value: &Datum,
        owner: Span,
        formal: Span,
        span: Span,
    ) {
        self.deferred_errors.push((
            vec![Fact {
                owner,
                obligation: Obligation::Handoff(formal),
            }],
            Diagnostic::error(
                Code::E0548,
                span,
                "via application requires explicit new ownership",
            ),
        ));
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

    fn forward_via_input(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        value: &Datum,
        (owner, formal): Handoff,
        span: Span,
    ) {
        if value.roots.iter().all(|origin| origin.inherits_mode) {
            self.forward_handoff(ctx, ledger, value, (owner, formal));
        } else {
            self.link_via_projection(ctx, value, owner, formal, span);
        }
    }

    fn apply_closure_input(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        (owner, formal): Handoff,
        (mode, value, span): (Mode, &Datum, Span),
        (via, modeled_stores): (bool, bool),
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
                        mode == Mode::New,
                        Fact {
                            owner,
                            obligation: Obligation::Handoff(formal),
                        },
                        Code::E0548,
                        "via application requires new ownership",
                    ),
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

    fn forwards_via(ctx: &Context, value: &Datum) -> bool {
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

    fn prepare_argument(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        arg: &Argument,
        mut value: Datum,
        span: Span,
        mode: Mode,
    ) -> Datum {
        if mode != Mode::Via {
            for root in &mut value.roots {
                root.inherits_mode = false;
            }
        }
        match mode {
            Mode::New => self.handoff(ctx, ledger, &mut value, span),
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
                    if value.roots.iter().any(|origin| origin.call_borrow) {
                        self.error(Code::E0528, span, "a call-scoped writer cannot be retained");
                    }
                    for root in &mut value.roots {
                        root.fix_mode(Access::Shared);
                        root.new = false;
                    }
                    value.requires_new = false;
                }
            }
            Mode::Plain
                if matches!(self.ty(span), Ty::Callable(_)) || value.task_scope.is_some() => {}
            Mode::Plain => self.freeze_value(ledger, &mut value, span),
            _ => {}
        }
        value
    }

    fn mutable_argument_place(&self, ctx: &Context, id: ExprId, mode: Mode) -> bool {
        let ast = self.ast(ctx.file);
        match &ast.expr(id).value {
            Expr::Path(_) => true,
            Expr::Member { .. } | Expr::Index { .. } => ast.navigation_chain(id).is_none(),
            Expr::Call { callee, args } if mode == Mode::Mut => {
                matches!(
                    &ast.expr(*callee).value,
                    Expr::Path(path)
                        if self.definition(path.span).is_some_and(|def| {
                            let def = self.program.hir.definition(def);
                            matches!(def.kind, DefinitionKind::Primitive(_)) && def.name.value == "inner"
                        })
                ) && matches!(args.as_slice(), [arg] if arg.mode == Mode::Mut)
            }
            _ => false,
        }
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
            "println" | "print" => self.effect(ctx, ledger, "io", span),
            "panic" => self.publish_at_exit(ctx, ledger, false),
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
                    .map(|value| ledger.project(value, Coordinate::Index("0".into()), Access::Mut))
                    .unwrap_or_default();
            }
            "derive" => {
                if let Some((_, _, callback)) = args.iter().find(|(i, _, _)| *i == 1) {
                    self.link_invocation(ctx, callback);
                    for effect in &callback.latent_effects {
                        self.effect(ctx, ledger, effect, span);
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

    pub(super) fn handlers(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        handlers: &[Handler],
    ) {
        let mut operations = BTreeSet::new();
        let mut installed = std::collections::BTreeMap::new();
        for handler in handlers {
            let span = handler.operation.span;
            let operation = self
                .definition(span)
                .and_then(|id| self.operation(id, span));
            if let Some(operation) = &operation {
                if !operations.insert(operation.clone()) {
                    self.error(Code::E0622, span, "duplicate operation in handler group");
                }
            } else {
                self.error(
                    Code::E0621,
                    span,
                    "handler must target a user effect operation",
                );
            }
            let rhs = self.ast(ctx.file).expr(handler.value);
            let inline = matches!(rhs.value, Expr::Closure { .. });
            let mut value = if inline {
                let mut local = ctx.clone();
                if handler.mode == Mode::New {
                    local.expected = Mode::New;
                }
                self.closure(&local, ledger, handler.value, true)
            } else {
                self.expr(ctx, ledger, handler.value)
            };
            if let Expr::Path(path) = &rhs.value
                && let Some(id) = self.definition(path.span)
            {
                let def = self.program.hir.definition(id);
                if let Some(stmt) = def.stmt
                    && let StmtKind::Function(fun) =
                        &self.ast(def.name.span.file).stmt(stmt).value.kind
                {
                    let bindings: BTreeSet<_> = fun
                        .signature
                        .obligations
                        .state
                        .iter()
                        .filter(|clause| clause.kind == StateKind::Environment)
                        .flat_map(|clause| &clause.bindings)
                        .filter_map(|(_, path)| self.declaration(path.span))
                        .collect();
                    for (index, binding) in bindings.into_iter().enumerate() {
                        if let Some(slot) = ledger.slots.get(&binding) {
                            value
                                .members
                                .insert(Coordinate::Index(index.to_string()), slot.value.clone());
                            value
                                .invocations
                                .entry(fun.name.span)
                                .or_default()
                                .insert(binding, BTreeSet::from([binding]));
                        }
                    }
                }
            }
            let effects = value
                .latent_effects
                .iter()
                .chain(match self.ty(rhs.span) {
                    Ty::Callable(signature) if !inline => signature.effects.as_slice(),
                    _ => &[],
                })
                .cloned()
                .collect::<BTreeSet<_>>();
            for effect in effects {
                self.effect(ctx, ledger, &effect, rhs.span);
            }
            self.link_invocation(ctx, &value);
            if ctx.reachable && !ctx.shadow {
                self.check_handler_iteration(ledger, &value, rhs.span, None);
            }
            if handler.mode == Mode::New {
                self.handoff(ctx, ledger, &mut value, rhs.span);
            }
            let capture_mode = value
                .members
                .values()
                .flat_map(Datum::origins)
                .map(|origin| origin.mode)
                .max();
            let held_mode = match handler.mode {
                specified @ (Mode::Ref | Mode::Mut | Mode::Shared) => Some(specified),
                _ => match capture_mode {
                    Some(Access::Shared) => Some(Mode::Shared),
                    Some(Access::Mut) => Some(Mode::Mut),
                    Some(Access::Ref) => Some(Mode::Ref),
                    _ => None,
                },
            };
            if let Some(mode) = held_mode {
                if handler.mode == Mode::Plain
                    && !inline
                    && !value.requires_new
                    && !matches!(&rhs.value, Expr::Path(path) if self.definition(path.span).is_some_and(|id| self.program.hir.definition(id).kind == DefinitionKind::Function))
                {
                    self.error(
                        Code::E0405,
                        rhs.span,
                        "a live handler variable requires an explicit access mode",
                    );
                }
                ledger.holds.push((mode, value.clone()));
            }
            if let Some(operation) = operation {
                installed.insert(operation, value);
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
        locals.obligations.clear();
        locals.lost_results.clear();
        locals.no_continuation = false;
        let mut inner = Context::new(node.span);
        inner.in_function = true;
        inner.set_caller_storage(ledger);
        inner.expected = Mode::Infer;
        inner.runtime = ctx.runtime;
        inner.shadow = ctx.shadow;
        inner.reachable = ctx.reachable;
        inner.handlers.clone_from(&ctx.handlers);
        inner.via.clone_from(&ctx.via);
        inner.member_via = ctx.member_via;
        inner.formals = params
            .iter()
            .map(|param| param.name.as_ref().map(|name| name.span))
            .collect();
        if let Ty::Callable(signature) = self.ty(node.span) {
            let axes = member_axes(signature, &inner.formals);
            inner.member_via |= !axes.is_empty();
            self.register_member_axes(&axes);
            let via = params
                .iter()
                .filter_map(|p| {
                    p.name
                        .as_ref()
                        .filter(|_| p.mode == Mode::Via)
                        .map(|name| name.span)
                })
                .collect();
            self.closure_modes.insert(
                node.span,
                ClosureModes {
                    formals: inner.formals.clone(),
                    via,
                    member_axes: axes,
                    returns: Vec::new(),
                    updates: BTreeMap::new(),
                    models_publication: false,
                },
            );
        }
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
                self.binding_scopes.insert(name.span, inner.scope);
                if p.mode == Mode::New {
                    inner.owned_formals.insert(name.span);
                }
                let mode = Access::from_mode(p.mode);
                let mut value = Datum::source(name.span, mode, p.mode == Mode::New);
                let param_ty = self
                    .definition(name.span)
                    .and_then(|id| self.program.bindings.get(&id));
                if p.mode == Mode::Via {
                    inner.via.insert(name.span);
                    if param_ty.is_some_and(Ty::is_value) {
                        self.error(
                            Code::E0550,
                            name.span,
                            "via is redundant on a value-type parameter",
                        );
                    }
                }
                if param_ty.is_some_and(Ty::is_result) {
                    locals.record_result(&mut value, name.span);
                }
                value.transform(&mut |origin| {
                    origin.dependencies.insert(name.span.into());
                    origin.inherits_mode = p.mode == Mode::Via;
                    origin.call_borrow = p.mode == Mode::Mut;
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
        let output = locals.snapshot(&output);
        let implicit = self.ty(self.ast(ctx.file).expr(*body).span) != &Ty::Never;
        if inner.reachable && implicit {
            self.check_results(&locals, &output.results());
            self.storage_exit(&inner, &locals);
            if output.returns_borrowed_writer(Mode::Infer) {
                self.error(
                    Code::E0528,
                    node.span,
                    "a call-scoped writer cannot escape in a return",
                );
            }
        }
        let exits = self.storage_exits.remove(&node.span).unwrap_or_default();
        let body_span = self.ast(ctx.file).expr(*body).span;
        if let Some(closure) = self.closure_modes.get_mut(&node.span) {
            closure.updates = Ledger::join_updates(exits.iter().collect());
            closure.models_publication = closure
                .updates
                .keys()
                .all(|region| closure.formals.contains(&Some(region.source)));
            closure
                .updates
                .retain(|region, _| closure.formals.contains(&Some(region.source)));
            closure.returns.clone_from(&inner.return_values);
            if implicit && inner.reachable {
                closure.returns.push(output.clone());
            }
            seal_call_allocations(
                &mut self.callback_results,
                closure
                    .returns
                    .iter_mut()
                    .chain(closure.updates.values_mut().map(|update| &mut update.value)),
                body_span,
            );
        }
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
        let new = ctx.expected == Mode::New;
        let mut closure = Datum::source(
            node.span,
            if new { Access::Mut } else { Access::Immutable },
            new,
        );
        closure.result_fresh = (implicit || !inner.return_values.is_empty())
            && (!implicit || output.requires_new)
            && inner.return_values.iter().all(|value| value.requires_new);
        for (index, slot) in used
            .iter()
            .filter_map(|span| ledger.slots.get(span))
            .enumerate()
        {
            let mut value = ledger.loop_snapshot(&slot.value).into_owned();
            if value.origins().any(|origin| origin.confined.is_some()) {
                self.error(
                    Code::E0604,
                    node.span,
                    "closure cannot capture a scoped resource",
                );
            }
            if slot.variable {
                let mut origin = Datum::source(slot.decl, Access::Mut, false);
                origin.transform(&mut |origin| {
                    origin.dependencies.insert(slot.decl.into());
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
                Obligation::Operation(operation) => Some(operation.effect.clone()),
                _ => None,
            })
            .collect();
        if !closure.members.is_empty() {
            closure.environments.insert(node.span);
            let bindings = used
                .into_iter()
                .map(|decl| {
                    let sources = std::iter::once(decl)
                        .chain(
                            ledger
                                .slots
                                .get(&decl)
                                .into_iter()
                                .flat_map(|slot| slot.value.root_dependencies()),
                        )
                        .collect();
                    (decl, sources)
                })
                .collect();
            closure.invocations.insert(inner.owner, bindings);
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
