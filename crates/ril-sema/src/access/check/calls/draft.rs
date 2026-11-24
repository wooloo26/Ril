use ril_base::span::Span;
use ril_frontend::syntax::Mode;

use super::{
    Analyzer, CallEntry, CallEnvironment, CallStorage, Context, Datum, Ledger,
    snapshot_invocations::known_provider,
};

impl Analyzer<'_> {
    pub(super) fn derive_storage(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        base: &Datum,
        callback: &Datum,
        span: Span,
    ) -> Datum {
        let mut before = ledger.clone();
        let cursor = before.begin_draft(span, base);
        let arguments = [(0, Mode::Mut, cursor)];
        let entry = CallEntry {
            arguments: &arguments,
            spans: &[span],
            ledger: &before,
            span,
            invocation: &[],
            environment: None,
        };
        let mut alternatives = Vec::new();
        for origin in &callback.roots {
            let mut after = before.clone();
            if let Some(owner) = known_provider(origin) {
                if let Some(closure) = self.closure_modes.get(&owner).cloned() {
                    let captures = Self::closure_captures(&before, callback, origin, &closure);
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
                        ..entry
                    };
                    self.apply_callable_storage(ctx, storage, &entry, &mut after, false);
                } else if let Some(call) =
                    self.provider_storage_call((owner, origin, callback), &entry)
                {
                    let entry = CallEntry {
                        arguments: &call.arguments,
                        spans: &call.spans,
                        ..entry
                    };
                    self.apply_callable_storage(ctx, call.storage, &entry, &mut after, true);
                } else {
                    if let Some(function) = self
                        .definition(owner)
                        .and_then(|id| self.function_syntax(id))
                        && function.body.is_some()
                    {
                        self.function(function, &before);
                    }
                    let storage = self
                        .functions
                        .iter()
                        .find(|fun| fun.owner == owner)
                        .map(CallStorage::updates_of)
                        .or_else(|| self.imported_draft_storage(owner, &entry));
                    if let Some(storage) = storage {
                        let entry = CallEntry {
                            environment: Some(CallEnvironment {
                                owner,
                                bindings: None,
                            }),
                            ..entry
                        };
                        self.apply_callable_storage(ctx, storage, &entry, &mut after, false);
                    }
                }
            }
            alternatives.push(after);
        }
        if !alternatives.is_empty() {
            ledger.merge(&before, &alternatives);
        } else {
            *ledger = before;
        }
        ledger.finish_draft(span).unwrap_or_else(|| base.clone())
    }
}
