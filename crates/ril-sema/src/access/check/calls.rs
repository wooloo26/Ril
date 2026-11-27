use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
};

use ril_hir::{Definition, DefinitionId, DefinitionKind};
use ril_source::{
    diag::{Code, Diagnostic},
    span::Span,
};
use ril_syntax::syntax::{Argument, Expr, ExprId, Function, Handler, Mode, StateKind, StmtKind};

use crate::{
    access::{
        CallbackArgument, CallbackReturn, InvocationMode, ReturnSource,
        flow::{
            CallbackOrigin, DeferredStorageCall, Origin, StorageAction, StorageFlow, StorageTarget,
        },
    },
    ty::{Callable, Ty},
};

use super::{
    Access, Analyzer, ClosureModes, Context, Coordinate, Datum, Fact, Input, Ledger, ModeUse,
    Obligation, Region, Rule, SchemaRequirement, Slot, conflicts, member_axes,
    storage::CallStorage,
};
use crate::access::flow::InvocationSite;

mod draft;
mod imported;
mod snapshot_invocations;
mod storage_replay;
pub(super) use snapshot_invocations::{SnapshotInvocation, SnapshotProviders};

mod builtins;
mod closures;
mod invoke;
mod named;
mod returns;
mod storage_apply;
mod via_args;

type CallArgument = (usize, Mode, Datum);

#[derive(Clone, Copy)]
struct CallEntry<'a> {
    arguments: &'a [CallArgument],
    spans: &'a [Span],
    ledger: &'a Ledger,
    span: Span,
    invocation: &'a [InvocationSite],
    environment: Option<CallEnvironment<'a>>,
}

struct ProviderStorageCall {
    storage: CallStorage,
    arguments: Vec<CallArgument>,
    spans: Vec<Span>,
}

#[derive(Clone, Copy)]
struct CallEnvironment<'a> {
    owner: Span,
    bindings: Option<&'a CapturedBindings>,
}

#[derive(Default)]
struct CapturedBindings {
    values: BTreeMap<Span, Datum>,
    cells: BTreeMap<Span, Datum>,
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
    pub(super) fn function_syntax(&self, id: DefinitionId) -> Option<&'program Function> {
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
        self.charge_latent_effects(ctx, ledger, &callable, span);
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
        let id = match &self.ast(ctx.file).expr(callee).value {
            Expr::Path(path) => self.definition(path.span),
            _ => None,
        };
        let mut result = self.call_value(ctx, ledger, callee, args, span, id);
        if !id.is_some_and(|id| {
            let definition = self.program.hir.definition(id);
            data_constructor(definition)
                || matches!(definition.kind, DefinitionKind::Primitive(_))
                    && definition.name.value == "inner"
        }) {
            // The signature specifies the possible tags at a call boundary.
            result.forget_variants();
            if ctx.reachable && !ledger.no_continuation {
                let ty = self
                    .program
                    .propagation_inputs
                    .get(&span)
                    .unwrap_or_else(|| self.ty(span));
                result = super::results::receive_results(
                    self.program,
                    self.hir_scope(ctx),
                    ledger,
                    ty,
                    result,
                    span,
                );
            }
        }
        ledger.remember_return_graph(&result, span);
        result
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

fn data_constructor(definition: &Definition) -> bool {
    matches!(definition.kind, DefinitionKind::Variant(_))
}
