use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet, VecDeque},
};

use super::{Analyzer, CallArgument, CallEntry, Context, Coordinate, Datum, Ledger, Mode};
use crate::access::check::{
    higher_order::can_supply_snapshot_callback,
    snapshots::{Arguments, Call},
};
use crate::access::{
    ModeAxis, SnapshotArgument, SnapshotCall, SnapshotGraph, SnapshotOrigin, SnapshotProvider,
    Summary,
    flow::{AllocationIdentity, Region, widen_recursive_projection},
};
use ril_base::span::Span;

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

struct Provider {
    formals: Vec<Option<Span>>,
    via: BTreeSet<Span>,
}

#[derive(Default)]
pub(in crate::access::check) struct SnapshotProviders {
    signatures: BTreeMap<Span, Provider>,
    sources: Vec<Span>,
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

fn known_provider(origin: &crate::access::flow::Origin) -> Option<Span> {
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
            borrowed: origin.call_borrow,
            forwarded: origin.inherits_mode,
            provider: known_provider(origin).and_then(|owner| providers.get(&owner).copied()),
        })
        .collect();
    SnapshotGraph {
        owned: value.requires_new,
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
    formals: &[Option<Span>],
    invocation: &SnapshotInvocation,
    providers: &BTreeMap<Span, usize>,
) -> Option<SnapshotCall> {
    let receiver = axis(formals, invocation.receiver.roots.first()?)?;
    let mut arguments: Vec<_> = invocation
        .arguments
        .0
        .iter()
        .map(|(position, mode, value)| SnapshotArgument {
            position: *position,
            mode: crate::access::Input::from_mode(*mode),
            whole_graph: invocation.whole_graphs.contains(position),
            graph: describe_graph(formals, value, &invocation.entry, providers),
        })
        .collect();
    arguments.sort_unstable();
    Some(SnapshotCall {
        receiver,
        recursive_path: invocation.recursive_path.clone(),
        arguments,
    })
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
                origin.call_borrow = root.borrowed;
                origin.inherits_mode = root.forwarded;
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
        requires_new: graph.owned,
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
        let providers: Vec<_> = summary
            .snapshot_providers
            .iter()
            .map(|_| self.snapshot_providers.fresh_identity(owner))
            .collect();
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
            self.snapshot_providers
                .signatures
                .insert(provider, Provider { formals, via });
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
        owner: Span,
    ) -> (Vec<SnapshotCall>, Vec<SnapshotProvider>) {
        let mut references = ProviderReferences::default();
        let calls = self.publish_snapshot_calls(owner, &mut references);
        let mut providers = Vec::new();
        while let Some(source) = references.pending.pop_front() {
            let owner = *self
                .snapshot_providers
                .sources
                .get(source)
                .unwrap_or_else(|| ril_base::ice!("missing snapshot provider index {source}"));
            let signature = self
                .snapshot_providers
                .signatures
                .get(&owner)
                .unwrap_or_else(|| ril_base::ice!("missing snapshot provider signature"));
            let via_parameters = signature
                .formals
                .iter()
                .map(|formal| formal.is_some_and(|formal| signature.via.contains(&formal)))
                .collect();
            providers.push(SnapshotProvider {
                via_parameters,
                inputs: self.snapshots.inputs(owner, &signature.formals),
                calls: self.publish_snapshot_calls(owner, &mut references),
            });
        }
        (calls, providers)
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
                for argument in &mut call.arguments {
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
            let arguments: Vec<_> = call
                .arguments
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
                            (&mut ledger, &mut next_identity),
                        ),
                    )
                })
                .collect();
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
                        || can_supply_snapshot_callback(self.ty(span)))
            })
        {
            let mut receiver = ledger.snapshot(receiver);
            receiver.roots.retain(|root| {
                !root.region.selection.is_empty()
                    || !self.closure_modes.contains_key(&root.region.source)
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
        if self.snapshot_invocations.is_empty() {
            return;
        }
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
                    && provider.formals.contains(&Some(source))
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
                        if let Some(contract) =
                            describe_invocation(&provider.formals, &invocation, &provider_ids)
                        {
                            self.snapshot_call_summaries
                                .entry(owner)
                                .or_default()
                                .insert(contract);
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

#[derive(Default)]
struct ProviderReferences {
    indices: BTreeMap<usize, usize>,
    pending: VecDeque<usize>,
}

impl ProviderReferences {
    fn rebase_graph(&mut self, graph: &mut SnapshotGraph) {
        for root in &mut graph.roots {
            if let Some(provider) = &mut root.provider {
                let next = self.indices.len();
                *provider = *self.indices.entry(*provider).or_insert_with(|| {
                    self.pending.push_back(*provider);
                    next
                });
            }
        }
        for (_, member) in &mut graph.members {
            self.rebase_graph(member);
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
