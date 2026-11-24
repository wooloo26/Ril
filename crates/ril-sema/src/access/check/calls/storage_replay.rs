use std::collections::BTreeMap;

use ril_base::diag::Diagnostic;
use ril_frontend::{hir::DefinitionKind, syntax::StateKind};

use super::{
    Analyzer, CallEntry, CallStorage, Context, DeferredStorageCall, InvocationSite, Ledger,
    StorageAction, StorageFlow, snapshot_invocations::known_provider,
};
use crate::access::check::storage::ReadSite;

impl Analyzer<'_> {
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
                self.diagnostics.push(Diagnostic {
                    primary: Some(entry.span),
                    ..Diagnostic::unsupported("could not stabilize callback storage updates")
                });
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
            StorageAction::Write(target, update) => self.apply_storage_updates(
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
            StorageAction::Invoke(call) => {
                self.replay_deferred_storage(ctx, storage, entry, after, call)
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
        let key = (entry.span, call.site);
        if !self.replaying_storage.insert(key) {
            self.diagnostics.push(Diagnostic {
                primary: Some(entry.span),
                ..Diagnostic::unsupported("could not stabilize recursive callback storage updates")
            });
            return false;
        }
        let before = after.clone();
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
                    entry.span,
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
