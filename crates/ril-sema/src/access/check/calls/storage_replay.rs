use std::collections::BTreeMap;

use ril_hir::DefinitionKind;
use ril_source::{
    diag::{Code, Diagnostic},
    span::Span,
};
use ril_syntax::syntax::StateKind;

use super::{
    Access, Analyzer, CallEntry, CallStorage, Context, Datum, DeferredStorageCall, InvocationSite,
    Ledger, StorageAction, StorageFlow, StorageTarget, snapshot_invocations::known_provider,
};
use crate::access::{
    Coordinate,
    check::storage::{ReadSite, ReplaySite},
    flow::StorageRead,
};

impl Analyzer<'_> {
    pub(super) fn clone_storage(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        base: &Datum,
        (span, invocation): (Span, &[InvocationSite]),
        site: ReadSite,
    ) -> Datum {
        let base = ledger.snapshot_call_graph(base);
        if base.contains_live_callable_environment() {
            self.error(Code::E0530, span, "cannot clone live callable authority");
            return Datum::source(span, Access::Mut, true);
        }
        let depends_on_caller = |origin: &super::Origin| {
            ctx.formals.contains(&Some(origin.region.source))
                || origin.callback_result.is_some()
                || origin.storage_read.is_some()
        };
        let deferred_writes = ledger
            .storage_flow
            .as_ref()
            .is_some_and(StorageFlow::has_deferred_writes);
        if ctx.in_function
            && ctx.runtime
            && ctx.reachable
            && !ctx.shadow
            && (deferred_writes
                || !base.capture_paths.is_empty()
                || base.origins().any(depends_on_caller))
        {
            let index = self.storage_read_index(site);
            ledger.defer_storage_clone(index, base);
            let mut pending = Datum::source(span, Access::Mut, true);
            for root in &mut pending.roots {
                root.storage_read = Some(StorageRead {
                    index,
                    path: Vec::new(),
                });
                root.region.set_invocation(invocation);
            }
            return pending;
        }
        base.cloned_graph(span, invocation)
    }

    pub(super) fn apply_callable_storage(
        &mut self,
        ctx: &Context,
        mut storage: CallStorage,
        entry: &CallEntry<'_>,
        ledger: &mut Ledger,
        published: bool,
    ) -> bool {
        let Some(flow) = storage.flow.take() else {
            return self.apply_storage_updates(ctx, storage, entry, ledger, published);
        };
        let mut applied = true;
        match flow {
            StorageFlow::Paths(paths) => {
                let mut alternatives = Vec::new();
                for path in paths {
                    let mut after = entry.ledger.clone();
                    for action in &path {
                        if after.no_continuation {
                            break;
                        }
                        applied &= self.replay_storage_action(
                            ctx, &storage, entry, &mut after, action, published,
                        );
                    }
                    alternatives.push(after);
                }
                ledger.merge(entry.ledger, &alternatives);
            }
            StorageFlow::Interleaved(actions) => {
                // A cyclic or widened trace represents any repetition of its
                // actions. Keep every incoming state and solve the weak join.
                let mut head = entry.ledger.clone();
                for _ in 0..64 + entry.ledger.slots.len() {
                    let mut alternatives = Vec::with_capacity(actions.len() + 1);
                    alternatives.push(head.clone());
                    for action in &actions {
                        let mut after = head.clone();
                        applied &= self.replay_storage_action(
                            ctx, &storage, entry, &mut after, action, published,
                        );
                        if let Some(flow) = &mut after.storage_flow {
                            flow.widen();
                        }
                        alternatives.push(after);
                    }
                    let mut next = head.clone();
                    next.merge(entry.ledger, &alternatives);
                    if next == head {
                        *ledger = next;
                        return applied;
                    }
                    head = next;
                }
                self.diagnostics.push(Diagnostic::unsupported_at(
                    entry.span,
                    "could not stabilize callback storage updates",
                ));
            }
        }
        applied
    }

    fn replay_storage_action(
        &mut self,
        ctx: &Context,
        storage: &CallStorage,
        entry: &CallEntry<'_>,
        after: &mut Ledger,
        action: &StorageAction,
        published: bool,
    ) -> bool {
        let observed = entry.ledger.with_storage_samples(after);
        let entry = &CallEntry {
            ledger: &observed,
            ..*entry
        };
        match action {
            StorageAction::Write(StorageTarget::Entry(target), update) => self
                .apply_storage_updates(
                    ctx,
                    CallStorage {
                        formals: storage.formals.clone(),
                        via: storage.via.clone(),
                        updates: BTreeMap::from([(target.clone(), update.clone())]),
                        ..CallStorage::default()
                    },
                    entry,
                    after,
                    published,
                ),
            StorageAction::Write(StorageTarget::Observed { parent, member }, update) => {
                let Some(parent) = entry
                    .ledger
                    .sampled_storage((entry.span, entry.invocation), parent)
                else {
                    // This read may not have run yet on a widened trace.
                    return true;
                };
                let value = self.instantiate_return(
                    &storage.formals,
                    &storage.via,
                    entry,
                    &update.value,
                    &mut Vec::new(),
                );
                let coordinate = if matches!(member, Coordinate::ArrayTail(_)) {
                    after.append_coordinate(&parent, update.definite)
                } else {
                    member.clone()
                };
                let place = parent.slot_projection(coordinate);
                self.apply_storage_member(
                    ctx,
                    after,
                    &place,
                    value,
                    (entry.span, update.definite, published),
                )
            }
            StorageAction::Invoke(call) => {
                self.replay_deferred_storage(ctx, storage, entry, after, call)
            }
            StorageAction::Derive {
                index,
                base,
                updater,
            } => {
                let key = (entry.span, ReplaySite::Derive(*index));
                if !self.replaying_storage.insert(key) {
                    self.diagnostics.push(Diagnostic::unsupported_at(
                        entry.span,
                        "could not stabilize recursive draft updates",
                    ));
                    return false;
                }
                let base = self.instantiate_return(
                    &storage.formals,
                    &storage.via,
                    entry,
                    base,
                    &mut Vec::new(),
                );
                let updater = self.instantiate_return(
                    &storage.formals,
                    &storage.via,
                    entry,
                    updater,
                    &mut Vec::new(),
                );
                let forwarded = self.storage_read_index(ReadSite::Forwarded(
                    entry.span,
                    entry.invocation.to_vec(),
                    *index,
                ));
                let mut trace = entry.invocation.to_vec();
                trace.push(InvocationSite {
                    span: entry.span,
                    ordinal: *index,
                });
                let result = self.derive_storage(
                    ctx,
                    after,
                    (&base, &updater),
                    (entry.span, &trace, forwarded),
                );
                after.sample_storage((entry.span, entry.invocation.to_vec(), *index), result);
                self.replaying_storage.remove(&key);
                true
            }
            StorageAction::Clone { index, base } => {
                let base = self.instantiate_return(
                    &storage.formals,
                    &storage.via,
                    entry,
                    base,
                    &mut Vec::new(),
                );
                let site = ReadSite::Forwarded(entry.span, entry.invocation.to_vec(), *index);
                let mut trace = entry.invocation.to_vec();
                trace.push(InvocationSite {
                    span: entry.span,
                    ordinal: *index,
                });
                let result = self.clone_storage(ctx, after, &base, (entry.span, &trace), site);
                after.sample_storage((entry.span, entry.invocation.to_vec(), *index), result);
                true
            }
            StorageAction::Read {
                index,
                base,
                coordinate,
                mode,
            } => {
                let base = self.instantiate_return(
                    &storage.formals,
                    &storage.via,
                    entry,
                    base,
                    &mut Vec::new(),
                );
                if let Some(working) = after.read_draft(&base) {
                    let selected = after.project_schema(&working, coordinate.clone(), *mode);
                    after.sample_storage((entry.span, entry.invocation.to_vec(), *index), selected);
                    return true;
                }
                after.remember_return_graph(&base, entry.span);
                let mut selected = after.project_schema(&base, coordinate.clone(), *mode);
                if after.storage_flow.is_some() && !selected.roots.is_empty() {
                    let forwarded = self.storage_read_index(ReadSite::Forwarded(
                        entry.span,
                        entry.invocation.to_vec(),
                        *index,
                    ));
                    after.record_storage_read(
                        forwarded,
                        &base,
                        coordinate.clone(),
                        *mode,
                        &mut selected,
                    );
                }
                after.sample_storage((entry.span, entry.invocation.to_vec(), *index), selected);
                true
            }
        }
    }

    fn replay_deferred_storage(
        &mut self,
        ctx: &Context,
        storage: &CallStorage,
        entry: &CallEntry<'_>,
        after: &mut Ledger,
        call: &DeferredStorageCall,
    ) -> bool {
        let key = (entry.span, ReplaySite::Callback(call.site));
        if !self.replaying_storage.insert(key) {
            self.diagnostics.push(Diagnostic::unsupported_at(
                entry.span,
                "could not stabilize recursive callback storage updates",
            ));
            return false;
        }
        let mut before = after.clone();
        let mut trace = entry.invocation.to_vec();
        trace.push(InvocationSite {
            span: call.site,
            ordinal: trace.len(),
        });
        let actual = CallEntry {
            invocation: &trace,
            ..*entry
        };
        let receiver = self.instantiate_return(
            &storage.formals,
            &storage.via,
            entry,
            &call.receiver,
            &mut Vec::new(),
        );
        let mut arguments = call.arguments.clone();
        let mut spans = call.spans.clone();
        self.specialize_callback_arguments(
            &storage.formals,
            &storage.via,
            entry,
            (&mut arguments, &mut spans),
        );
        for (_, _, argument) in &arguments {
            before.remember_return_graph(argument, entry.span);
        }
        let invocation = CallEntry {
            arguments: &arguments,
            spans: &spans,
            environment: None,
            ledger: &before,
            ..actual
        };
        let mut alternatives = Vec::new();
        let mut closures = receiver.clone();
        closures.roots.retain(|root| {
            let named = known_provider(root).and_then(|owner| {
                let id = self.definition(owner)?;
                let fun = self.function_syntax(id)?;
                (self.program.hir.definition(id).kind == DefinitionKind::Function
                    && !fun.is_meta
                    && fun
                        .signature
                        .obligations
                        .state
                        .iter()
                        .all(|state| state.kind != StateKind::Environment))
                .then_some((id, fun))
            });
            if let Some((id, fun)) = named {
                let mut branch = before.clone();
                let signature = self.program.callables.get(&id).map(|sig| sig.as_ref());
                self.named_call(
                    ctx,
                    &mut branch,
                    fun,
                    signature,
                    (&arguments, &spans),
                    (entry.span, &trace),
                );
                alternatives.push(branch);
                false
            } else {
                true
            }
        });
        if !closures.roots.is_empty() {
            let known = self.known_closures(&closures);
            self.record_snapshot_invocation(
                ctx,
                &before,
                &closures,
                (&arguments, &spans),
                entry.span,
            );
            for (&owner, closure) in &known {
                self.record_snapshot_call(
                    ctx,
                    (owner, &closure.formals),
                    (entry.span, &before),
                    (&arguments, &spans),
                );
            }
            if let Some(branch) = self.closure_storage(ctx, &known, &closures, &invocation, true) {
                alternatives.push(branch);
            }
        }
        if !alternatives.is_empty() {
            after.merge(&before, &alternatives);
        }
        self.replaying_storage.remove(&key);
        true
    }
}
