use ril_base::span::Span;
use ril_frontend::syntax::Mode;

use super::{
    Access, Analyzer, CallEntry, CallEnvironment, CallStorage, Context, Datum, InvocationSite,
    Ledger, Origin, snapshot_invocations::known_provider,
};
use crate::access::flow::StorageRead;

impl Analyzer<'_> {
    pub(super) fn derive_storage(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        (base, callback): (&Datum, &Datum),
        (span, invocation, index): (Span, &[InvocationSite], usize),
    ) -> Datum {
        let mut before = ledger.clone();
        let cursor = before.begin_draft((span, invocation), base);
        let arguments = [(0, Mode::Mut, cursor.clone())];
        let entry = CallEntry {
            arguments: &arguments,
            spans: &[span],
            ledger: &before,
            span,
            invocation,
            environment: None,
        };
        let mut alternatives = Vec::new();
        let mut results = Vec::new();
        for origin in &callback.roots {
            let mut after = before.clone();
            let applied = self.apply_draft_updater(ctx, (callback, origin), &entry, &mut after);
            if applied && !after.has_deferred_draft_access(&cursor) {
                results.extend(after.finish_draft(&cursor));
            } else {
                // An unresolved nested call can still use the private cursor.
                // Replay the whole update when that call is known.
                after = ledger.clone();
                let mut updater = callback.clone();
                updater.retain_compatible_origins(&origin.branches);
                updater.roots.retain(|root| root == origin);
                after.defer_storage_derive(index, base, &updater);
                let mut pending = Datum::source(span, Access::Immutable, false);
                pending.transform(&mut |root| {
                    root.detached_snapshot = true;
                    root.storage_read = Some(StorageRead {
                        index,
                        path: Vec::new(),
                    });
                });
                results.push(pending);
            }
            alternatives.push(after);
        }
        if !alternatives.is_empty() {
            let mut joined = ledger.clone();
            joined.merge(ledger, &alternatives);
            *ledger = joined;
        }
        results
            .into_iter()
            .reduce(Datum::join_draft_results)
            .unwrap_or_else(|| base.clone())
    }

    fn apply_draft_updater(
        &mut self,
        ctx: &Context,
        (receiver, origin): (&Datum, &Origin),
        entry: &CallEntry<'_>,
        after: &mut Ledger,
    ) -> bool {
        let Some(owner) = known_provider(origin) else {
            return false;
        };
        if let Some(closure) = self.closure_modes.get(&owner).cloned() {
            let captures = Self::closure_captures(entry.ledger, receiver, origin, &closure);
            let storage = CallStorage {
                formals: closure.formals,
                via: closure.via,
                updates: closure.updates,
                flow: closure.storage_flow,
                ..CallStorage::default()
            };
            let entry = CallEntry {
                environment: Some(CallEnvironment {
                    owner,
                    bindings: Some(&captures),
                }),
                ..*entry
            };
            self.apply_callable_storage(ctx, storage, &entry, after, false);
        } else if let Some(call) = self.provider_storage_call((owner, origin, receiver), entry) {
            let entry = CallEntry {
                arguments: &call.arguments,
                spans: &call.spans,
                ..*entry
            };
            self.apply_callable_storage(ctx, call.storage, &entry, after, true);
        } else {
            let named = self
                .definition(owner)
                .and_then(|id| self.function_syntax(id))
                .filter(|function| function.body.is_some());
            if let Some(function) = named {
                self.function(function, entry.ledger);
            }
            let storage = self
                .functions
                .iter()
                .find(|fun| fun.owner == owner)
                .map(CallStorage::updates_of)
                .or_else(|| {
                    if named.is_some() {
                        self.recursive_calls.insert(owner);
                        self.recursive_storage.get(&owner).cloned()
                    } else {
                        self.imported_draft_storage(owner, entry)
                    }
                });
            let Some(storage) = storage else {
                return false;
            };
            let entry = CallEntry {
                environment: Some(CallEnvironment {
                    owner,
                    bindings: None,
                }),
                ..*entry
            };
            self.apply_callable_storage(ctx, storage, &entry, after, false);
        }
        true
    }
}
