use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet, VecDeque},
};

use super::{
    Analyzer, CallArgument, CallEntry, CallbackResult, Context, Coordinate, Datum, InvocationSite,
    Ledger, Mode,
};
use crate::access::check::{
    higher_order::can_supply_snapshot_callback,
    snapshots::{Arguments, Call},
};
use crate::access::{
    ModeAxis, SnapshotArgument, SnapshotCall, SnapshotFactoryStep, SnapshotGraph, SnapshotOrigin,
    SnapshotProjection, SnapshotProvider, Summary,
    flow::{AllocationIdentity, Region, widen_recursive_projection},
};
use ril_source::span::Span;

mod output;

#[derive(Clone, Eq, PartialEq)]
pub(in crate::access::check) struct SnapshotInvocation {
    owner: Span,
    site: Span,
    receiver: Datum,
    recursive_path: Option<Vec<Coordinate>>,
    arguments: Arguments,
    whole_graphs: BTreeSet<usize>,
    entry: Ledger,
}

#[derive(Clone)]
struct Provider {
    formals: Vec<Option<Span>>,
    via: BTreeSet<Span>,
}

#[derive(Default)]
pub(in crate::access::check) struct SnapshotProviders {
    signatures: BTreeMap<Span, Provider>,
    sources: Vec<Span>,
    imported: BTreeMap<Span, Vec<Span>>,
    imported_results: BTreeMap<Span, output::ImportedResult>,
    imported_storage: BTreeMap<Span, output::ImportedStorage>,
    returns: BTreeMap<Span, output::ProviderResult>,
    synthetic: usize,
}

impl SnapshotProviders {
    fn fresh_identity(&mut self, site: Span) -> Span {
        // The replayed declaration has no source location. Keep these keys
        // distinct from source spans and use the export span for diagnostics.
        let offset = usize::MAX - self.synthetic;
        self.synthetic += 1;
        Span::new(site.file, offset, offset)
    }
}

pub(super) fn known_provider(origin: &crate::access::flow::Origin) -> Option<Span> {
    if origin.callback_result.is_some() || origin.storage_read.is_some() {
        return None;
    }
    origin.snapshot_provider.or_else(|| {
        origin
            .region
            .selection
            .is_empty()
            .then_some(origin.region.source)
    })
}

#[derive(Clone, Default)]
struct InvocationTrail {
    receivers: BTreeMap<Span, Vec<Coordinate>>,
    argument_depths: BTreeMap<(Span, Span, usize), usize>,
}

impl InvocationTrail {
    fn bound_argument_graphs(&mut self, invocation: &mut SnapshotInvocation, receiver: Span) {
        for (position, mode, value) in &mut invocation.arguments.0 {
            let depth = value.snapshot_shape_depth();
            let previous = self
                .argument_depths
                .entry((invocation.owner, receiver, *position))
                .or_insert(depth);
            if depth > *previous || invocation.whole_graphs.contains(position) {
                // Recursive calls can add unbounded wrapper and projection
                // paths. Once a graph grows on a cycle, track its authority
                // boundaries without retaining each copy of the path.
                if *mode == Mode::Via && !invocation.whole_graphs.contains(position) {
                    value.detach_handed_off_paths();
                }
                value.widen_snapshot_graph();
                invocation.whole_graphs.insert(*position);
            }
        }
    }
}

fn axis(formals: &[Option<Span>], origin: &crate::access::flow::Origin) -> Option<ModeAxis> {
    Some(ModeAxis {
        parameter: formals
            .iter()
            .position(|formal| *formal == Some(origin.region.source))?,
        path: origin.region.selection.clone(),
    })
}

fn describe_graph(
    formals: &[Option<Span>],
    value: &Datum,
    ledger: &Ledger,
    providers: &BTreeMap<Span, usize>,
) -> SnapshotGraph {
    let roots: BTreeSet<_> = value
        .roots
        .iter()
        .map(|origin| SnapshotOrigin {
            source: axis(formals, origin),
            access: origin.mode,
            new: origin.new,
            call_scoped: origin.call_scoped_access,
            forwarded: origin.inherits_mode,
            detached: origin.detached_snapshot,
            provider: known_provider(origin).and_then(|owner| providers.get(&owner).copied()),
        })
        .collect();
    SnapshotGraph {
        new_root: value.requires_new,
        environment: !value.environments.is_empty(),
        replaced: ledger.snapshot_overwrites(value),
        roots: roots.into_iter().collect(),
        members: value
            .members
            .iter()
            .map(|(coordinate, member)| {
                (
                    coordinate.clone(),
                    describe_graph(formals, member, ledger, providers),
                )
            })
            .collect(),
    }
}

fn describe_invocation(
    analyzer: &Analyzer<'_>,
    formals: &[Option<Span>],
    invocation: &SnapshotInvocation,
    providers: &BTreeMap<Span, usize>,
) -> Vec<SnapshotCall> {
    let arguments = describe_arguments(
        formals,
        &invocation.arguments.0,
        &invocation.whole_graphs,
        &invocation.entry,
        providers,
    );
    invocation
        .receiver
        .roots
        .iter()
        .flat_map(|receiver| {
            describe_receiver(analyzer, formals, receiver, providers, &mut BTreeSet::new())
        })
        .map(|(receiver, factory_steps)| SnapshotCall {
            receiver,
            factory_steps,
            recursive_path: invocation.recursive_path.clone(),
            arguments: arguments.clone(),
        })
        .collect()
}

fn describe_arguments(
    formals: &[Option<Span>],
    values: &[CallArgument],
    whole_graphs: &BTreeSet<usize>,
    ledger: &Ledger,
    providers: &BTreeMap<Span, usize>,
) -> Vec<SnapshotArgument> {
    let mut arguments: Vec<_> = values
        .iter()
        .map(|(position, mode, value)| SnapshotArgument {
            position: *position,
            mode: crate::access::Input::from_mode(*mode),
            whole_graph: whole_graphs.contains(position),
            graph: describe_graph(formals, value, ledger, providers),
        })
        .collect();
    arguments.sort_unstable();
    arguments
}

fn describe_receiver(
    analyzer: &Analyzer<'_>,
    formals: &[Option<Span>],
    receiver: &crate::access::flow::Origin,
    providers: &BTreeMap<Span, usize>,
    visiting: &mut BTreeSet<usize>,
) -> Vec<(ModeAxis, Vec<SnapshotFactoryStep>)> {
    if let Some(axis) = axis(formals, receiver) {
        return vec![(axis, Vec::new())];
    }
    let Some(pending) = receiver.callback_result else {
        return Vec::new();
    };
    let Some(template) = analyzer.callback_results.get(pending.template) else {
        return Vec::new();
    };
    if !visiting.insert(pending.template) {
        return Vec::new();
    }
    let step = SnapshotFactoryStep {
        path: receiver.region.selection.clone(),
        cap: pending.cap,
        arguments: describe_arguments(
            formals,
            &template.arguments,
            &BTreeSet::new(),
            &Ledger::default(),
            providers,
        ),
    };
    let receivers = template
        .receiver
        .roots
        .iter()
        .flat_map(|root| describe_receiver(analyzer, formals, root, providers, visiting))
        .map(|(axis, mut steps)| {
            steps.push(step.clone());
            (axis, steps)
        })
        .collect();
    visiting.remove(&pending.template);
    receivers
}

fn import_graph(
    owner: Span,
    formals: &[Option<Span>],
    providers: &[Span],
    graph: &SnapshotGraph,
    (ledger, next_identity): (&mut Ledger, &mut usize),
) -> Datum {
    let roots = graph
        .roots
        .iter()
        .flat_map(|root| {
            let source = root
                .source
                .as_ref()
                .and_then(|axis| formals.get(axis.parameter).copied().flatten());
            let local = Span::new(owner.file, owner.start, owner.start);
            let mut datum = Datum::source(source.unwrap_or(local), root.access, root.new);
            for origin in &mut datum.roots {
                if let Some(axis) = &root.source {
                    origin.region.selection.clone_from(&axis.path);
                }
                origin.call_scoped_access = root.call_scoped;
                origin.inherits_mode = root.forwarded;
                origin.detached_snapshot = root.detached;
                origin.snapshot_provider = root
                    .provider
                    .and_then(|index| providers.get(index).copied());
                if source.is_none() {
                    let identity = AllocationIdentity {
                        index: *next_identity,
                        summarized: false,
                    };
                    *next_identity += 1;
                    origin.region = Region::returned(local, identity);
                    origin.return_allocation = Some(identity);
                }
            }
            datum.roots
        })
        .collect();
    let value = Datum {
        roots,
        members: graph
            .members
            .iter()
            .map(|(coordinate, member)| {
                (
                    coordinate.clone(),
                    import_graph(owner, formals, providers, member, (ledger, next_identity)),
                )
            })
            .collect(),
        requires_new: graph.new_root,
        environments: graph.environment.then_some(owner).into_iter().collect(),
        ..Datum::default()
    };
    ledger.restore_snapshot_overwrites(&value, &graph.replaced);
    value
}

impl Analyzer<'_> {
    pub(in crate::access::check) fn import_snapshot_contract(
        &mut self,
        owner: Span,
        formals: &[Option<Span>],
        summary: &Summary,
    ) {
        self.register_storage_observations(owner, summary);
        let providers: Vec<_> = summary
            .snapshot_providers
            .iter()
            .map(|_| self.snapshot_providers.fresh_identity(owner))
            .collect();
        self.snapshot_providers
            .imported
            .insert(owner, providers.clone());
        for (&provider, contract) in providers.iter().zip(&summary.snapshot_providers) {
            let formals: Vec<_> = contract
                .via_parameters
                .iter()
                .map(|_| Some(self.snapshot_providers.fresh_identity(owner)))
                .collect();
            let via = formals
                .iter()
                .zip(&contract.via_parameters)
                .filter_map(|(&formal, &is_via)| if is_via { formal } else { None })
                .collect();
            self.snapshots.import(provider, &formals, &contract.inputs);
            self.import_snapshot_invocations(
                (provider, owner),
                &formals,
                &providers,
                &contract.calls,
            );
            let signature = Provider { formals, via };
            if !contract.storage_updates.is_empty()
                || !contract.captured_slots.is_empty()
                || contract.storage_flow.is_some()
            {
                let captures = contract
                    .captured_slots
                    .iter()
                    .map(|_| Some(self.snapshot_providers.fresh_identity(owner)))
                    .collect();
                self.snapshot_providers.imported_storage.insert(
                    provider,
                    output::ImportedStorage {
                        owner,
                        signature: signature.clone(),
                        captures,
                        slots: contract.captured_slots.clone(),
                        updates: contract.storage_updates.clone(),
                        flow: contract.storage_flow.clone(),
                    },
                );
            }
            if !contract.returns.is_empty() || !contract.callback_returns.is_empty() {
                self.snapshot_providers.imported_results.insert(
                    provider,
                    output::ImportedResult {
                        owner,
                        signature: signature.clone(),
                        result: output::ProviderResult {
                            projections: contract.returns.clone(),
                            callbacks: contract.callback_returns.clone(),
                            constructs: contract.returns_new,
                        },
                    },
                );
            }
            self.snapshot_providers
                .signatures
                .insert(provider, signature);
        }
        self.snapshots
            .import(owner, formals, &summary.snapshot_inputs);
        self.import_snapshot_invocations(
            (owner, owner),
            formals,
            &providers,
            &summary.snapshot_calls,
        );
    }

    pub(in crate::access::check) fn publish_snapshot_contract(
        &self,
        function: &crate::access::check::DefinitionCheck,
        summary: &mut Summary,
    ) {
        let mut references = ProviderReferences::default();
        summary.snapshot_calls = self.publish_snapshot_calls(function.owner, &mut references);
        self.publish_snapshot_projections(function, summary, &mut references);
        summary.storage_flow = function.storage_flow.as_ref().map(|flow| {
            self.publish_storage_flow(function.owner, &function.formals, flow, &mut references)
        });
        references.rebase_callback_returns(&mut summary.callback_returns);
        for update in &mut summary.storage_updates {
            references.rebase_callback_returns(&mut update.callback_returns);
        }
        let mut providers = Vec::new();
        while let Some(source) = references.pending.pop_front() {
            let owner = *self
                .snapshot_providers
                .sources
                .get(source)
                .unwrap_or_else(|| ril_source::ice!("missing snapshot provider index {source}"));
            let signature = self
                .snapshot_providers
                .signatures
                .get(&owner)
                .unwrap_or_else(|| ril_source::ice!("missing snapshot provider signature"));
            let via_parameters = signature
                .formals
                .iter()
                .map(|formal| formal.is_some_and(|formal| signature.via.contains(&formal)))
                .collect();
            let mut result = self
                .snapshot_providers
                .returns
                .get(&owner)
                .cloned()
                .unwrap_or_default();
            references.rebase_projections(&mut result.projections);
            references.rebase_callback_returns(&mut result.callbacks);
            let (captured_slots, storage_updates) =
                self.publish_provider_storage(owner, &mut references);
            let storage_flow = self.publish_provider_flow(owner, &mut references);
            providers.push(SnapshotProvider {
                via_parameters,
                inputs: self.snapshots.inputs(owner, &signature.formals),
                calls: self.publish_snapshot_calls(owner, &mut references),
                captured_slots,
                storage_updates,
                storage_flow,
                returns: result.projections,
                callback_returns: result.callbacks,
                returns_new: result.constructs,
            });
        }
        summary.snapshot_providers = providers;
    }

    fn publish_snapshot_calls(
        &self,
        owner: Span,
        references: &mut ProviderReferences,
    ) -> Vec<SnapshotCall> {
        self.snapshot_call_summaries
            .get(&owner)
            .into_iter()
            .flatten()
            .cloned()
            .map(|mut call| {
                for argument in call
                    .factory_steps
                    .iter_mut()
                    .flat_map(|step| &mut step.arguments)
                    .chain(&mut call.arguments)
                {
                    references.rebase_graph(&mut argument.graph);
                }
                call
            })
            .collect()
    }

    fn import_snapshot_invocations(
        &mut self,
        (owner, site): (Span, Span),
        formals: &[Option<Span>],
        providers: &[Span],
        calls: &[SnapshotCall],
    ) {
        for call in calls {
            let Some(source) = formals.get(call.receiver.parameter).copied().flatten() else {
                continue;
            };
            let mut receiver = Datum::source(source, crate::access::Access::Immutable, false);
            for root in &mut receiver.roots {
                root.region.selection.clone_from(&call.receiver.path);
            }
            let mut ledger = Ledger::default();
            let mut next_identity = 0;
            for (ordinal, step) in call.factory_steps.iter().enumerate() {
                let arguments = import_arguments(
                    site,
                    formals,
                    providers,
                    &step.arguments,
                    &mut next_identity,
                    &mut Ledger::default(),
                );
                let spans = vec![site; arguments.len()];
                receiver = self.defer_callback_result(
                    CallbackResult {
                        receiver,
                        arguments,
                        spans,
                        site: vec![InvocationSite {
                            span: site,
                            ordinal,
                        }],
                        ordinal,
                    },
                    site,
                );
                for root in &mut receiver.roots {
                    root.region.selection.clone_from(&step.path);
                    if let Some(result) = &mut root.callback_result {
                        result.cap = step.cap;
                    }
                }
            }
            let arguments = import_arguments(
                site,
                formals,
                providers,
                &call.arguments,
                &mut next_identity,
                &mut ledger,
            );
            let spans = vec![site; arguments.len()];
            self.snapshot_invocations.push(SnapshotInvocation {
                owner,
                site,
                receiver,
                recursive_path: call.recursive_path.clone(),
                arguments: (arguments, spans),
                whole_graphs: call
                    .arguments
                    .iter()
                    .filter(|argument| argument.whole_graph)
                    .map(|argument| argument.position)
                    .collect(),
                entry: ledger,
            });
        }
    }
    pub(in crate::access::check) fn record_snapshot_invocation(
        &mut self,
        ctx: &Context,
        ledger: &Ledger,
        receiver: &Datum,
        (arguments, spans): (&[CallArgument], &[Span]),
        site: Span,
    ) {
        if !ctx.reachable || ctx.shadow || !ctx.runtime || receiver.roots.is_empty() {
            return;
        }
        if arguments
            .iter()
            .zip(spans)
            .any(|((_, mode, value), &span)| {
                !value.roots.is_empty()
                    && (matches!(mode, Mode::New | Mode::Via)
                        || can_supply_snapshot_callback(self.program, self.ty(span)))
            })
        {
            let mut receiver = ledger.snapshot(receiver);
            receiver.roots.retain(|root| {
                root.storage_read.is_none()
                    && (!root.region.selection.is_empty()
                        || !self.closure_modes.contains_key(&root.region.source))
            });
            if !receiver.roots.is_empty() {
                self.snapshot_invocations.push(SnapshotInvocation {
                    owner: ctx.owner,
                    site,
                    receiver,
                    recursive_path: None,
                    arguments: (arguments.to_vec(), spans.to_vec()),
                    whole_graphs: BTreeSet::new(),
                    entry: ledger.clone(),
                });
            }
        }
    }

    pub(in crate::access::check) fn link_snapshot_invocations(&mut self, calls: &mut Vec<Call>) {
        let mut providers = std::mem::take(&mut self.snapshot_providers.signatures);
        providers.extend(
            self.functions
                .iter()
                .map(|function| {
                    (
                        function.owner,
                        Provider {
                            formals: function.formals.clone(),
                            via: function.via.clone(),
                        },
                    )
                })
                .chain(self.closure_modes.iter().map(|(&owner, closure)| {
                    (
                        owner,
                        Provider {
                            formals: closure.formals.clone(),
                            via: closure.via.clone(),
                        },
                    )
                }))
                .chain(
                    self.program
                        .imported_functions
                        .keys()
                        .filter_map(|&definition| {
                            let function = self.function_syntax(definition)?;
                            let formals = function
                                .signature
                                .params
                                .iter()
                                .map(|param| param.name.as_ref().map(|name| name.span))
                                .collect();
                            let via = function
                                .signature
                                .params
                                .iter()
                                .filter(|param| param.mode == Mode::Via)
                                .filter_map(|param| param.name.as_ref().map(|name| name.span))
                                .collect();
                            Some((function.name.span, Provider { formals, via }))
                        }),
                ),
        );
        let provider_ids: BTreeMap<_, _> = providers
            .keys()
            .copied()
            .enumerate()
            .map(|(index, owner)| (owner, index))
            .collect();
        let mut by_callee = BTreeMap::<_, Vec<_>>::new();
        for (index, call) in calls.iter().enumerate() {
            by_callee.entry(call.callee).or_default().push(index);
        }
        let mut templates = BTreeMap::<Span, Vec<(SnapshotInvocation, InvocationTrail)>>::new();
        let mut pending: VecDeque<_> = std::mem::take(&mut self.snapshot_invocations)
            .into_iter()
            .map(|invocation| (invocation, InvocationTrail::default()))
            .collect();
        while let Some((invocation, trail)) = pending.pop_front() {
            for receiver in &invocation.receiver.roots {
                let source = receiver.region.source;
                let mut invocation = invocation.clone();
                let mut trail = trail.clone();
                invocation.receiver.roots.retain(|root| root == receiver);
                for (_, _, value) in &mut invocation.arguments.0 {
                    value.retain_compatible_origins(&receiver.branches);
                }
                trail.bound_argument_graphs(&mut invocation, source);
                if invocation.recursive_path.is_none()
                    && let Some(callee) = known_provider(receiver)
                    && let Some(provider) = providers.get(&callee)
                {
                    let call = Call {
                        owner: invocation.owner,
                        site: invocation.site,
                        callee,
                        formals: provider.formals.clone(),
                        entry: invocation.entry,
                        arguments: invocation.arguments,
                        whole_graphs: invocation.whole_graphs,
                    };
                    let contexts = by_callee.entry(callee).or_default();
                    if !contexts
                        .iter()
                        .any(|&index| calls.get(index) == Some(&call))
                    {
                        for (template, trail) in templates.get(&callee).into_iter().flatten() {
                            pending.extend(
                                self.specialize_snapshot_invocation(provider, &call, template)
                                    .into_iter()
                                    .map(|invocation| (invocation, trail.clone())),
                            );
                        }
                        contexts.push(calls.len());
                        calls.push(call);
                    }
                } else if let Some(provider) = providers.get(&invocation.owner)
                    && (provider.formals.contains(&Some(source))
                        || receiver.callback_result.is_some())
                {
                    let owner = invocation.owner;
                    if let Some(root) = invocation.receiver.roots.first_mut() {
                        if let Some(previous) = trail.receivers.get(&source) {
                            widen_recursive_projection(
                                &mut root.region.selection,
                                previous,
                                &mut invocation.recursive_path,
                            );
                        }
                        trail
                            .receivers
                            .insert(source, root.region.selection.clone());
                    }
                    let unresolved = templates.entry(owner).or_default();
                    if !unresolved
                        .iter()
                        .any(|(previous, _)| previous == &invocation)
                    {
                        let contracts = describe_invocation(
                            self,
                            &provider.formals,
                            &invocation,
                            &provider_ids,
                        );
                        if !contracts.is_empty() {
                            self.snapshot_call_summaries
                                .entry(owner)
                                .or_default()
                                .extend(contracts);
                        }
                        for context in by_callee
                            .get(&owner)
                            .into_iter()
                            .flatten()
                            .filter_map(|&index| calls.get(index))
                        {
                            pending.extend(
                                self.specialize_snapshot_invocation(provider, context, &invocation)
                                    .into_iter()
                                    .map(|invocation| (invocation, trail.clone())),
                            );
                        }
                        unresolved.push((invocation, trail));
                    }
                }
            }
        }
        self.snapshot_providers.sources = providers.keys().copied().collect();
        self.snapshot_providers.signatures = providers;
        self.prepare_snapshot_provider_results();
    }

    fn specialize_snapshot_invocation(
        &mut self,
        provider: &Provider,
        call: &Call,
        captured: &SnapshotInvocation,
    ) -> Vec<SnapshotInvocation> {
        let entry = CallEntry {
            arguments: &call.arguments.0,
            spans: &call.arguments.1,
            ledger: &call.entry,
            span: call.site,
            invocation: &[],
            environment: None,
        };
        let receiver = self.instantiate_return(
            &provider.formals,
            &provider.via,
            &entry,
            &captured.receiver,
            &mut Vec::new(),
        );
        let mut arguments = captured.arguments.clone();
        let mut whole_graphs = captured.whole_graphs.clone();
        let widened_formals: BTreeSet<_> = call
            .whole_graphs
            .iter()
            .filter_map(|&position| provider.formals.get(position).copied().flatten())
            .collect();
        for (position, _, value) in &mut arguments.0 {
            value.transform(&mut |origin| {
                if widened_formals.contains(&origin.region.source) {
                    origin.region.selection.clear();
                    whole_graphs.insert(*position);
                }
            });
        }
        self.specialize_callback_arguments(
            &provider.formals,
            &provider.via,
            &entry,
            (&mut arguments.0, &mut arguments.1),
        );
        let mut ledger = call.entry.clone();
        for ((_, _, original), (_, _, actual)) in captured.arguments.0.iter().zip(&arguments.0) {
            restore_projected_overwrites(original, actual, &captured.entry, &mut ledger);
        }
        let mut targets = Vec::new();
        let widened_receiver = captured.receiver.roots.iter().find_map(|root| {
            if !widened_formals.contains(&root.region.source) {
                return None;
            }
            let position = provider
                .formals
                .iter()
                .position(|formal| *formal == Some(root.region.source))?;
            call.arguments
                .0
                .iter()
                .find(|(index, ..)| *index == position)
                .map(|(.., value)| value)
        });
        if let Some(graph) = widened_receiver {
            // The argument retains its possible providers after losing exact
            // member paths. Replay any provider reachable in that graph.
            nested_snapshot_receivers(graph, &[], &mut targets);
        } else if let Some(path) = &captured.recursive_path {
            nested_snapshot_receivers(&receiver, path, &mut targets);
        } else {
            targets.push((receiver, None));
        }
        targets
            .into_iter()
            .map(|(receiver, recursive_path)| SnapshotInvocation {
                owner: call.owner,
                site: call.site,
                receiver,
                recursive_path,
                arguments: arguments.clone(),
                whole_graphs: whole_graphs.clone(),
                entry: ledger.clone(),
            })
            .collect()
    }
}

fn import_arguments(
    site: Span,
    formals: &[Option<Span>],
    providers: &[Span],
    arguments: &[SnapshotArgument],
    next_identity: &mut usize,
    ledger: &mut Ledger,
) -> Vec<CallArgument> {
    arguments
        .iter()
        .map(|argument| {
            (
                argument.position,
                argument.mode.map_or(Mode::Via, crate::access::Input::mode),
                import_graph(
                    site,
                    formals,
                    providers,
                    &argument.graph,
                    (ledger, next_identity),
                ),
            )
        })
        .collect()
}

#[derive(Default)]
struct ProviderReferences {
    indices: BTreeMap<usize, usize>,
    observations: BTreeMap<usize, usize>,
    pending: VecDeque<usize>,
}

impl ProviderReferences {
    fn rebase_callback_returns(&mut self, callbacks: &mut [crate::access::CallbackReturn]) {
        visit_callback_projections(callbacks, &mut |projections| {
            self.rebase_projections(projections);
        });
    }

    fn rebase_projections(&mut self, projections: &mut [SnapshotProjection]) {
        for projection in projections {
            self.rebase_origin(&mut projection.origin);
            if let Some(read) = &mut projection.observation {
                read.index = self.rebase_observation(read.index);
            }
        }
    }

    fn rebase_observation(&mut self, index: usize) -> usize {
        let next = self.observations.len();
        *self.observations.entry(index).or_insert(next)
    }

    fn rebase_origin(&mut self, origin: &mut SnapshotOrigin) {
        if let Some(provider) = &mut origin.provider {
            let next = self.indices.len();
            *provider = *self.indices.entry(*provider).or_insert_with(|| {
                self.pending.push_back(*provider);
                next
            });
        }
    }

    fn rebase_graph(&mut self, graph: &mut SnapshotGraph) {
        for root in &mut graph.roots {
            self.rebase_origin(root);
        }
        for (_, member) in &mut graph.members {
            self.rebase_graph(member);
        }
    }
}

fn visit_callback_projections(
    callbacks: &mut [crate::access::CallbackReturn],
    visit: &mut impl FnMut(&mut [SnapshotProjection]),
) {
    for callback in callbacks {
        for argument in &mut callback.arguments {
            visit(&mut argument.snapshot_projections);
            visit_callback_projections(&mut argument.callback_returns, visit);
        }
    }
}

fn restore_projected_overwrites(
    template: &Datum,
    actual: &Datum,
    before: &Ledger,
    after: &mut Ledger,
) {
    after.restore_snapshot_overwrites(actual, &before.snapshot_overwrites(template));
    for (coordinate, original) in &template.members {
        if let Some(result) = actual.members.get(coordinate) {
            restore_projected_overwrites(original, result, before, after);
        }
    }
}

fn nested_snapshot_receivers(
    graph: &Datum,
    path: &[Coordinate],
    out: &mut Vec<(Datum, Option<Vec<Coordinate>>)>,
) {
    if !graph.roots.is_empty() {
        out.push((graph.clone(), Some(path.to_vec())));
    }
    let selected = path.iter().try_fold(Cow::Borrowed(graph), |value, step| {
        value.known_member(step).map(Cow::Owned)
    });
    if let Some(selected) = selected.filter(|value| !value.roots.is_empty()) {
        out.push((selected.into_owned(), None));
    }
    for child in graph.members.values() {
        nested_snapshot_receivers(child, path, out);
    }
}
