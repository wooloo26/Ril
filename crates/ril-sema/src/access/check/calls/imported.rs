use std::collections::{BTreeMap, BTreeSet};

use ril_base::{diag::Code, span::Span};
use ril_frontend::syntax::{Function, Mode};

use super::{Analyzer, CallArgument, CallEntry, CallbackResult, Context, Datum, Ledger, Rule};
use crate::{
    access::{
        Access, CallbackReturn, Coordinate, Input, InvocationMode, ReturnAllocation, ReturnSource,
        Summary,
        check::{Fact, Obligation, SchemaRequirement, member_axes, storage::CallStorage},
        flow::{AllocationIdentity, CallbackOrigin, InvocationSite, Origin, Region, Replacement},
    },
    iface::Export,
    ty::{Callable, Ty},
};

struct PublishedValue<'a> {
    sources: &'a [ReturnSource],
    callbacks: &'a [CallbackReturn],
    allocations: &'a [ReturnAllocation],
    constructs: bool,
}

impl<'program> Analyzer<'program> {
    pub(in crate::access::check) fn load_interface_calls(&mut self) {
        for (&id, export) in &self.program.imported_functions {
            let Some(fun) = self.function_syntax(id).filter(|fun| fun.body.is_none()) else {
                continue;
            };
            let owner = fun.name.span;
            let formals: Vec<_> = fun
                .signature
                .params
                .iter()
                .map(|param| param.name.as_ref().map(|name| name.span))
                .collect();
            let mut via_axis = 0;
            for (index, param) in fun.signature.params.iter().enumerate() {
                if let Some(formal) = formals.get(index).copied().flatten() {
                    for (selected, obligation) in [
                        (
                            export.summary.writes.contains(&index),
                            Obligation::Write(formal),
                        ),
                        (
                            export.summary.retained.contains(&index),
                            Obligation::StoreShare(formal),
                        ),
                    ] {
                        if selected {
                            self.rules.push(Rule {
                                premises: Vec::new(),
                                conclusion: Fact { owner, obligation },
                            });
                        }
                    }
                    if param.mode == Mode::Via && !export.domain.is_empty() {
                        for (mode, obligation) in [
                            (Input::New, Obligation::Handoff(formal)),
                            (Input::Shared, Obligation::NeedsSharing(formal)),
                        ] {
                            if export
                                .domain
                                .iter()
                                .all(|row| row.modes.get(via_axis) == Some(&mode))
                            {
                                self.rules.push(Rule {
                                    premises: Vec::new(),
                                    conclusion: Fact { owner, obligation },
                                });
                            }
                        }
                    }
                }
                if param.mode == Mode::Via {
                    via_axis += 1;
                }
            }
            if !export.domain.is_empty()
                && let Some(signature) = self.program.callables.get(&id)
            {
                for (index, (_, axis)) in member_axes(signature, &formals).into_iter().enumerate() {
                    for required in [
                        SchemaRequirement::Writable,
                        SchemaRequirement::Exclusive,
                        SchemaRequirement::Shared,
                    ] {
                        if export.domain.iter().all(|row| {
                            row.modes
                                .get(via_axis + index)
                                .is_some_and(|mode| required.accepts(mode.access()))
                        }) {
                            self.rules.push(Rule {
                                premises: Vec::new(),
                                conclusion: Fact {
                                    owner,
                                    obligation: Obligation::Schema(axis.clone(), required),
                                },
                            });
                        }
                    }
                }
            }
            self.import_snapshot_contract(owner, &formals, &export.summary);
            self.higher_order
                .add_interface(owner, formals, &export.summary);
        }
    }

    pub(super) fn imported_call(
        &mut self,
        ctx: &Context,
        ledger: &mut Ledger,
        function: &Function,
        signature: Option<&'program Callable>,
        export: &Export,
        (arguments, spans, span): (&[CallArgument], &[Span], Span),
    ) -> Datum {
        let formals: Vec<_> = function
            .signature
            .params
            .iter()
            .map(|param| param.name.as_ref().map(|name| name.span))
            .collect();
        let via: BTreeSet<_> = function
            .signature
            .params
            .iter()
            .filter(|param| param.mode == Mode::Via)
            .filter_map(|param| param.name.as_ref().map(|name| name.span))
            .collect();
        let frozen = ledger.clone();
        let entry = CallEntry {
            arguments,
            spans,
            span,
            invocation: &[],
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
        self.record_snapshot_call(
            ctx,
            (function.name.span, &formals),
            (span, &frozen),
            (arguments, spans),
        );
        if let Some(signature) = signature {
            self.charge_imported_effects(
                ctx,
                &frozen,
                function.name.span,
                signature,
                summary,
                span,
            );
        }
        if ctx.reachable && !ctx.shadow {
            if let Some(signature) = signature {
                self.record_callable_arguments(
                    ctx,
                    (function.name.span, &formals),
                    signature,
                    arguments,
                    spans,
                    (span, ledger),
                );
                for (index, axis) in member_axes(signature, &formals) {
                    if let Some(((.., argument), &argument_span)) = arguments
                        .iter()
                        .zip(spans)
                        .find(|((position, ..), _)| *position == index)
                    {
                        self.link_schema_argument(
                            ctx,
                            function.name.span,
                            axis,
                            argument,
                            argument_span,
                        );
                    }
                }
            }
            for ((position, mode, argument), &argument_span) in arguments.iter().zip(spans) {
                if *mode == Mode::Via
                    && let Some(formal) = formals.get(*position).copied().flatten()
                {
                    self.forward_via_input(
                        ctx,
                        ledger,
                        argument,
                        (function.name.span, formal),
                        argument_span,
                    );
                }
                if summary.invoked.contains(position) {
                    self.link_invocation(ctx, argument);
                    for source in argument.root_dependencies() {
                        self.seed(ctx, Obligation::Invoke(source));
                    }
                    for effect in &argument.latent_effects {
                        self.effect(ctx, &frozen, effect, argument_span);
                    }
                    if let Ty::Callable(actual) = self.ty(argument_span) {
                        for effect in &actual.effects {
                            self.effect(ctx, &frozen, effect, argument_span);
                        }
                    }
                }
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
                        PublishedValue {
                            sources: &update.sources,
                            callbacks: &update.callback_returns,
                            allocations: &update.allocations,
                            constructs: update.constructs,
                        },
                        ty,
                    );
                    let mut region = Region::root(source);
                    region.selection.clone_from(&update.path);
                    Some((
                        region,
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
                    via: via.clone(),
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
        self.imported_result(
            function.name.span,
            &formals,
            &via,
            summary,
            self.ty(span),
            &entry,
        )
    }

    pub(super) fn imported_callback_result(
        &mut self,
        function: &Function,
        signature: &'program Callable,
        export: &Export,
        entry: &CallEntry<'_>,
    ) -> Option<Datum> {
        let formals: Vec<_> = function
            .signature
            .params
            .iter()
            .map(|param| param.name.as_ref().map(|name| name.span))
            .collect();
        let via: BTreeSet<_> = function
            .signature
            .params
            .iter()
            .filter(|param| param.mode == Mode::Via)
            .filter_map(|param| param.name.as_ref().map(|name| name.span))
            .collect();
        let summary = if export.domain.is_empty() {
            &export.summary
        } else {
            self.select_imported_summary(export, signature, &formals, entry)?
        };
        let owner = function.name.span;
        if !self.resolving_interface_results.insert(owner) {
            return None;
        }
        let result = self.imported_result(owner, &formals, &via, summary, &signature.result, entry);
        self.resolving_interface_results.remove(&owner);
        Some(result)
    }

    fn imported_result(
        &mut self,
        owner: Span,
        formals: &[Option<Span>],
        via: &BTreeSet<Span>,
        summary: &Summary,
        ty: &'program Ty,
        entry: &CallEntry<'_>,
    ) -> Datum {
        if summary.return_sources.is_empty()
            && summary.callback_returns.is_empty()
            && summary.return_allocations.is_empty()
            && !summary.constructs
        {
            return if ty.is_value() {
                Datum::default()
            } else {
                Datum::source(entry.span, Access::Immutable, false)
            };
        }
        let template = self.exported_value(
            owner,
            formals,
            PublishedValue {
                sources: &summary.return_sources,
                callbacks: &summary.callback_returns,
                allocations: &summary.return_allocations,
                constructs: summary.constructs,
            },
            ty,
        );
        self.instantiate_return(formals, via, entry, &template, &mut Vec::new())
    }

    pub(in crate::access::check) fn charge_imported_effects(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        owner: Span,
        signature: &Callable,
        summary: &Summary,
        span: Span,
    ) {
        let mount = self
            .program
            .hir
            .file(owner.file)
            .path
            .iter()
            .next()
            .and_then(std::ffi::OsStr::to_str)
            .unwrap_or("pkg");
        for (index, template) in signature.effects.iter().enumerate() {
            let applied = self.applied_effect(index, template, span).to_owned();
            let mut uses = summary
                .effect_uses
                .iter()
                .filter(|term| term.declaration == index)
                .peekable();
            if uses.peek().is_none() {
                self.effect(ctx, ledger, &applied, span);
            }
            for term in uses {
                if let Some(name) = &term.operation {
                    let actual = name
                        .strip_prefix("pkg/")
                        .map_or_else(|| name.clone(), |relative| format!("{mount}/{relative}"));
                    if let Some(operation) = self
                        .effect_operations(&applied)
                        .into_iter()
                        .find(|operation| self.program.hir.export_name(operation.id) == actual)
                    {
                        self.use_effect(ctx, ledger, Obligation::Operation(operation), span, None);
                        continue;
                    }
                }
                self.effect(ctx, ledger, &applied, span);
            }
        }
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
                actual.push(Input::from_mode(*mode));
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
            actual.push(Input::from_mode(mode));
        }
        let row = export.domain.iter().find(|row| {
            row.modes.len() == actual.len()
                && row
                    .modes
                    .iter()
                    .zip(&actual)
                    .all(|(mode, actual)| actual.is_none_or(|actual| actual == *mode))
        })?;
        Some(if actual.iter().any(Option::is_none) {
            &export.summary
        } else {
            &row.summary
        })
    }

    fn exported_value(
        &mut self,
        owner: Span,
        formals: &[Option<Span>],
        PublishedValue {
            sources,
            callbacks,
            allocations,
            constructs,
        }: PublishedValue<'_>,
        ty: &'program Ty,
    ) -> Datum {
        let implicit = constructs && allocations.is_empty();
        let mut value = if implicit
            && sources.iter().all(|source| !source.result_path.is_empty())
            && callbacks
                .iter()
                .all(|callback| !callback.result_path.is_empty())
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
            let mut origin = Datum::source(
                formal,
                source.access,
                constructs && source.result_path.is_empty(),
            );
            for root in &mut origin.roots {
                root.region.selection.clone_from(&source.source_path);
            }
            self.exported_path(&mut value, &source.result_path, ty, owner, implicit)
                .roots
                .extend(origin.roots);
        }
        for callback in callbacks {
            let results = self.exported_callback(owner, formals, callback);
            self.exported_path(&mut value, &callback.result_path, ty, owner, implicit)
                .roots
                .extend(results);
        }
        let mut qualification = BTreeMap::new();
        let mut array_layouts = BTreeMap::new();
        for allocation in allocations {
            let mut source = Datum::source(owner, allocation.access, allocation.new);
            for root in &mut source.roots {
                root.return_allocation = Some(AllocationIdentity {
                    index: allocation.index,
                    summarized: allocation.summarized,
                });
            }
            self.exported_path(&mut value, &allocation.path, ty, owner, false)
                .roots
                .extend(source.roots);
            if !allocation.path.is_empty() {
                *qualification.entry(&allocation.path).or_insert(true) &= allocation.qualified;
            }
            array_layouts
                .entry(&allocation.path)
                .and_modify(|len| {
                    if *len != allocation.array_len {
                        *len = None;
                    }
                })
                .or_insert(allocation.array_len);
        }
        for (path, qualified) in qualification {
            let node = self.exported_path(&mut value, path, ty, owner, false);
            node.requires_new = qualified && node.roots.iter().all(|root| root.new);
        }
        for (path, len) in array_layouts {
            if let Some(len) = len
                && !sources
                    .iter()
                    .any(|source| path.starts_with(&source.result_path))
                && !callbacks
                    .iter()
                    .any(|callback| path.starts_with(&callback.result_path))
            {
                let node = self.exported_path(&mut value, path, ty, owner, false);
                if len <= node.members.len()
                    && (0..len).all(|index| {
                        node.members
                            .contains_key(&Coordinate::Index(index.to_string()))
                    })
                {
                    node.array_len = Some(len);
                }
            }
        }
        value
    }

    fn exported_path<'value>(
        &self,
        mut node: &'value mut Datum,
        path: &[Coordinate],
        mut ty: &'program Ty,
        owner: Span,
        constructs: bool,
    ) -> &'value mut Datum {
        for (depth, coord) in path.iter().enumerate() {
            let schema = self.schema_member(ty, coord);
            ty = match (ty, coord) {
                (Ty::Map(key, _), Coordinate::MapKey) => key,
                _ => schema.map_or(&Ty::Unknown, |member| &member.ty),
            };
            node = node.members.entry(coord.clone()).or_insert_with(|| {
                if constructs && depth + 1 < path.len() {
                    let mode = schema.map_or(Mode::Mut, |member| member.mode.mode);
                    Datum::source(owner, Access::from_mode(mode), true)
                } else {
                    Datum::default()
                }
            });
        }
        node
    }

    fn exported_callback(
        &mut self,
        owner: Span,
        formals: &[Option<Span>],
        callback: &CallbackReturn,
    ) -> Vec<Origin> {
        let Some(source) = formals.get(callback.receiver).copied().flatten() else {
            return Vec::new();
        };
        let mut receiver = Datum::source(source, Access::Mut, false);
        for root in &mut receiver.roots {
            root.region.selection.clone_from(&callback.receiver_path);
        }
        let mut inputs = vec![Vec::new()];
        for argument in &callback.arguments {
            let value = self.exported_value(
                owner,
                formals,
                PublishedValue {
                    sources: &argument.sources,
                    callbacks: &argument.callback_returns,
                    allocations: &argument.allocations,
                    constructs: argument.constructs,
                },
                &Ty::Unknown,
            );
            let alternatives: Vec<_> = argument
                .modes
                .iter()
                .map(|mode| {
                    let mut value = value.clone();
                    let mode = match *mode {
                        InvocationMode::Input(input) => input.mode(),
                        InvocationMode::Formal(index) => {
                            let formal = formals.get(index).copied().flatten();
                            for root in &mut value.roots {
                                root.inherits_mode = formal == Some(root.region.source);
                            }
                            Mode::Via
                        }
                    };
                    (argument.position, mode, value)
                })
                .collect();
            inputs = inputs
                .into_iter()
                .flat_map(|args| {
                    alternatives.iter().map(move |input| {
                        let mut args = args.clone();
                        args.push(input.clone());
                        args
                    })
                })
                .collect();
        }
        let mut origins = Vec::new();
        for arguments in inputs {
            let spans = vec![owner; arguments.len()];
            let template = self.callback_template(CallbackResult {
                receiver: receiver.clone(),
                arguments,
                spans,
                site: vec![InvocationSite {
                    span: owner,
                    ordinal: callback.invocation,
                }],
                ordinal: callback.invocation,
            });
            let mut placeholder = Datum::source(owner, Access::Ref, false);
            for root in &mut placeholder.roots {
                root.region.selection.clone_from(&callback.source_path);
                root.callback_result = Some(CallbackOrigin {
                    template,
                    cap: callback.cap,
                });
            }
            origins.extend(placeholder.roots);
        }
        origins
    }
}
