use std::collections::{BTreeMap, BTreeSet};

use ril_base::{diag::Code, span::Span};
use ril_frontend::syntax::{Function, Mode};

use super::{Analyzer, CallArgument, CallEntry, Context, Datum, Ledger};
use crate::{
    access::{
        Access, Input, ReturnSource, Summary,
        check::{Obligation, member_axes, storage::CallStorage},
        flow::{Region, Replacement},
    },
    iface::Export,
    ty::{Callable, Ty},
};

impl Analyzer<'_> {
    pub(super) fn imported_call(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        function: &Function,
        signature: Option<&Callable>,
        export: &Export,
        (arguments, spans, span): (&[CallArgument], &[Span], Span),
    ) -> Datum {
        let formals: Vec<_> = function
            .signature
            .params
            .iter()
            .map(|param| param.name.as_ref().map(|name| name.span))
            .collect();
        let frozen = ledger.clone();
        let entry = CallEntry {
            arguments,
            spans,
            span,
            ledger: &frozen,
        };
        let summary = if export.domain.is_empty() {
            Some(&export.summary)
        } else {
            signature.and_then(|signature| {
                self.select_imported_summary(export, signature, &formals, &entry)
            })
        };
        let Some(summary) = summary else {
            if ctx.reachable && !ctx.shadow {
                self.error(
                    Code::E0520,
                    span,
                    "arguments do not match a published via mode",
                );
            }
            return self.snapshot_value(span);
        };
        if ctx.reachable && !ctx.shadow {
            for ((position, mode, argument), &argument_span) in arguments.iter().zip(spans) {
                if summary.writes.contains(position) {
                    self.mutate(ctx, &frozen, argument, argument_span);
                    if *mode == Mode::New {
                        for origin in argument
                            .origins()
                            .filter(|origin| origin.mode.writes() && !origin.new)
                        {
                            self.seed(ctx, Obligation::WriteExisting(origin.region.source));
                        }
                    }
                }
                if summary.independent_retention.contains(position) {
                    for source in argument.root_dependencies() {
                        self.seed(ctx, Obligation::Retain(source));
                        self.seed(ctx, Obligation::Share(source));
                    }
                }
            }
            if !summary.invocations.is_empty()
                || !summary.callback_returns.is_empty()
                || summary
                    .storage_updates
                    .iter()
                    .any(|update| !update.callback_returns.is_empty())
            {
                self.error(
                    Code::E0552,
                    span,
                    "published higher-order call contract requires provider source",
                );
                return self.snapshot_value(span);
            }
            let updates: BTreeMap<_, _> = summary
                .storage_updates
                .iter()
                .filter_map(|update| {
                    let source = formals.get(update.formal).copied().flatten()?;
                    let mut ty = &signature?.parameters.get(update.formal)?.ty;
                    for coord in &update.path {
                        ty = self
                            .schema_member(ty, coord)
                            .map_or(&Ty::Unknown, |member| &member.ty);
                    }
                    let value = self.exported_value(
                        function.name.span,
                        &formals,
                        &update.sources,
                        update.constructs,
                        ty,
                    );
                    Some((
                        Region {
                            source,
                            selection: update.path.clone(),
                        },
                        Replacement {
                            value,
                            definite: update.definite,
                        },
                    ))
                })
                .collect();
            if !updates.is_empty() {
                let storage = CallStorage {
                    formals: formals.clone(),
                    updates,
                    ..CallStorage::default()
                };
                if !self.apply_storage_updates(ctx, storage, &entry, ledger) {
                    self.error(
                        Code::E0520,
                        span,
                        "published storage update has no writable call-entry target",
                    );
                }
            }
            ledger.no_continuation |= summary.nonreturning || self.ty(span) == &Ty::Never;
        }
        if summary.return_sources.is_empty() && !summary.constructs {
            return self.snapshot_value(span);
        }
        let template = self.exported_value(
            function.name.span,
            &formals,
            &summary.return_sources,
            summary.constructs,
            self.ty(span),
        );
        self.instantiate_return(
            &formals,
            &BTreeSet::new(),
            &entry,
            &template,
            &mut Vec::new(),
        )
    }

    fn select_imported_summary<'a>(
        &self,
        export: &'a Export,
        signature: &Callable,
        formals: &[Option<Span>],
        entry: &CallEntry<'_>,
    ) -> Option<&'a Summary> {
        let mut actual = Vec::new();
        for (index, formal) in signature.parameters.iter().enumerate() {
            if formal.mode == Mode::Via {
                let (_, mode, _) = entry
                    .arguments
                    .iter()
                    .find(|(position, ..)| *position == index)?;
                actual.push(Input::from_mode(*mode)?);
            }
        }
        for (index, axis) in member_axes(signature, formals) {
            let (_, &span) = entry
                .arguments
                .iter()
                .zip(entry.spans)
                .find(|((position, ..), _)| *position == index)?;
            let mut ty = self.ty(span);
            let mut mode = Mode::Plain;
            for coord in &axis.selection {
                let member = self.schema_member(ty, coord)?;
                ty = &member.ty;
                mode = member.mode.mode;
            }
            actual.push(Input::from_mode(mode)?);
        }
        export
            .domain
            .iter()
            .find(|row| row.modes == actual)
            .map(|row| &row.summary)
    }

    fn exported_value(
        &self,
        owner: Span,
        formals: &[Option<Span>],
        sources: &[ReturnSource],
        constructs: bool,
        ty: &Ty,
    ) -> Datum {
        let mut value = if constructs && sources.iter().all(|source| !source.result_path.is_empty())
        {
            Datum::source(owner, Access::Mut, true)
        } else {
            Datum {
                requires_new: constructs,
                ..Datum::default()
            }
        };
        for source in sources {
            let Some(formal) = formals.get(source.formal).copied().flatten() else {
                continue;
            };
            let mut node = &mut value;
            let mut ty = ty;
            for (depth, coord) in source.result_path.iter().enumerate() {
                let schema = self.schema_member(ty, coord);
                ty = schema.map_or(&Ty::Unknown, |member| &member.ty);
                node = node.members.entry(coord.clone()).or_insert_with(|| {
                    if constructs && depth + 1 < source.result_path.len() {
                        let mode = schema.map_or(Mode::Mut, |member| member.mode.mode);
                        Datum::source(owner, Access::from_mode(mode), true)
                    } else {
                        Datum::default()
                    }
                });
            }
            let mut origin = Datum::source(
                formal,
                source.access,
                constructs && source.result_path.is_empty(),
            );
            for root in &mut origin.roots {
                root.region.selection.clone_from(&source.source_path);
            }
            node.roots.extend(origin.roots);
        }
        value
    }
}
