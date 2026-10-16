//! Cancellation can return from a prefix of a scope body. Preserve those
//! states independently of the body's normal or diverging final state.
use super::*;
use std::sync::Arc;

pub(super) struct Context {
    scope: NodeId,
    task: Option<NodeId>,
    bindings: Vec<BindingId>,
    nodes: BTreeSet<NodeId>,
    recency_nodes: BTreeSet<NodeId>,
    duties: usize,
    before: Arc<flow::FlowSnapshot>,
    checkpoints: Vec<Checkpoint>,
    overflow: bool,
}
struct Checkpoint {
    span: Span,
    owner: ScopeId,
    has_cleanup: bool,
    state: Arc<flow::FlowSnapshot>,
}
pub(super) struct Projection {
    pub(super) recency: usize,
    pub(super) concurrency: concurrent::State,
    pub(super) bindings: BTreeMap<BindingId, Value>,
    pub(super) fields: BTreeMap<(NodeId, Slot), Value>,
    pub(super) duties: Vec<ResultDuty>,
    pub(super) uncertain: BTreeSet<(NodeId, Slot)>,
    pub(super) arrays: BTreeMap<NodeId, Option<u64>>,
    pub(super) fixed_arrays: BTreeSet<NodeId>,
}

impl Checker {
    pub(super) fn begin_scope_cancellation(&mut self, scope: NodeId, _span: Span) {
        let bindings: Vec<_> = self
            .bindings
            .iter()
            .enumerate()
            .filter_map(|(id, binding)| binding.alive.then_some(id))
            .collect();
        let nodes = self.heap.reachable(bindings.iter().flat_map(|id| {
            self.bindings[*id]
                .value
                .origins
                .nodes
                .iter()
                .copied()
                .chain(self.bindings[*id].cell)
        }));
        let mut recency_nodes = nodes.clone();
        recency_nodes.extend(self.concurrency.cancellation_recency_nodes());
        // A scalar projection can still carry a latent copy obligation. Its
        // frozen source/output graphs belong to this certificate even when
        // those nodes are not reachable from the projection's runtime value.
        let mut dependencies = bindings
            .iter()
            .map(|id| &self.bindings[*id].value)
            .chain(self.concurrency.cancellation_retained_values())
            .flat_map(|value| self.pending_copy_dependencies(value))
            .collect::<BTreeSet<_>>();
        let mut seen = BTreeSet::new();
        while let Some(id) = dependencies.pop_first() {
            if !seen.insert(id) {
                continue;
            }
            if let Some(boundary) = self.copy_boundaries.get(id.0 as usize) {
                recency_nodes.extend(
                    boundary
                        .nodes
                        .iter()
                        .chain(&boundary.output_nodes)
                        .map(|node| node.origin),
                );
                for requirement in &boundary.requirements {
                    if let super::super::copy_contract::CopyRequirementKind::PriorBoundary(prior) =
                        requirement.kind
                    {
                        dependencies.insert(prior);
                    }
                }
            }
        }
        recency_nodes = self.heap.reachable(recency_nodes);
        self.cancellation_contexts.push(Context {
            scope,
            task: self.cancellation_task(),
            bindings,
            nodes,
            recency_nodes,
            duties: self.result_duties.len(),
            before: Arc::new(self.snapshot_flow()),
            checkpoints: vec![],
            overflow: false,
        });
    }

    pub(super) fn cancellation_checkpoint(&mut self, span: Span, frame: &Frame) {
        let task = self.cancellation_task();
        let targets: Vec<_> = self
            .cancellation_contexts
            .iter()
            .enumerate()
            .filter_map(|(index, context)| {
                (context.task == task && self.cancellation_has_child(context.scope))
                    .then_some(index)
            })
            .collect();
        if targets.is_empty() {
            return;
        }
        let state = Arc::new(self.snapshot_flow());
        let has_cleanup = self.bindings.iter().any(|binding| {
            binding.alive && matches!(binding.mode, BindingMode::Scoped | BindingMode::ScopedMut)
        });
        for index in targets {
            let context = &mut self.cancellation_contexts[index];
            if context.checkpoints.len() >= 512 {
                context.overflow = true;
            } else {
                context.checkpoints.push(Checkpoint {
                    span,
                    owner: frame.owner,
                    has_cleanup,
                    state: state.clone(),
                });
            }
        }
    }

    pub(super) fn finish_scope_cancellation(
        &mut self,
        scope: NodeId,
        result: &mut Value,
        span: Span,
        frame: &mut Frame,
    ) {
        let context = self
            .cancellation_contexts
            .pop()
            .expect("scope cancellation contexts nest");
        debug_assert_eq!(context.scope, scope);
        if context.checkpoints.is_empty() {
            return;
        }
        if context.overflow {
            self.unsupported(span, "scope cancellation requires a complete prefix resource and ownership transfer proof");
            return;
        }
        // A parent panic is a non-returning path, never a scope TaskFault.
        // The separate cancellation prefixes may still return Err, provided
        // their heap and caller-owned duties pass the checks below. An effect
        // abort has a live destination and needs a separate target summary.
        if self.pending_abort.is_some() || (result.abnormal && result.ty != Ty::Never) {
            self.unsupported(span, "scope cancellation mixed with a parent panic or effect abort requires separate per-exit targets");
            return;
        }
        let initial = context.before.cancellation_projection(
            &context.bindings,
            &context.nodes,
            context.duties,
        );
        let final_state = self.snapshot_flow();
        let final_projection =
            final_state.cancellation_projection(&context.bindings, &context.nodes, context.duties);
        let prefixes: Vec<_> = context
            .checkpoints
            .iter()
            .map(|checkpoint| {
                checkpoint.state.cancellation_projection(
                    &context.bindings,
                    &context.nodes,
                    context.duties,
                )
            })
            .collect();
        if std::iter::once(&final_projection)
            .chain(&prefixes)
            .any(|prefix| {
                self.recency_moves[initial.recency..prefix.recency]
                    .iter()
                    .any(|(recent, older)| {
                        context.recency_nodes.contains(recent)
                            || context.recency_nodes.contains(older)
                    })
            })
        {
            self.unsupported(span, "scope cancellation across allocation recency requires a prefix identity transport proof");
            return;
        }
        if std::iter::once(&final_projection)
            .chain(&prefixes)
            .any(|prefix| {
                !prefix
                    .concurrency
                    .cancellation_external_compatible(&initial.concurrency, scope)
            })
        {
            self.unsupported(span, "scope cancellation requires a complete prefix resource and ownership transfer proof");
            return;
        }
        if context
            .checkpoints
            .iter()
            .any(|checkpoint| checkpoint.has_cleanup)
            && initial.duties.iter().enumerate().any(|(index, initial)| {
                !initial.covered
                    && !initial.abnormal
                    && self.result_duties[index].inspected
                    && prefixes
                        .iter()
                        .any(|prefix| !prefix.duties[index].inspected)
            })
        {
            self.unsupported(span, "scope cancellation Result inspection through cleanup requires per-prefix cleanup replay");
            return;
        }
        if std::iter::once(&final_projection)
            .chain(&prefixes)
            .any(|prefix| !same_graph(&initial, prefix, &self.loan_parents))
        {
            self.unsupported(span, "scope cancellation changes an external reference, resource, or Result producer before exit; a prefix heap transfer proof is required");
            return;
        }
        // No reference or authority can change under this certificate. Scalar
        // information is deliberately widened, including cleanup/callee writes;
        // a final-state constant or refinement cannot describe an earlier exit.
        for id in &context.bindings {
            widen(&mut self.bindings[*id].value);
        }
        for ((node, _), value) in &mut self.fields {
            if context.nodes.contains(node) {
                widen(value);
            }
        }
        self.widen_repeated_refinements();
        for prefix in &prefixes {
            self.merge_cancellation_external_tasks(
                &prefix.concurrency,
                &initial.concurrency,
                scope,
            );
        }
        for (index, initial) in initial.duties.iter().enumerate() {
            let current = &mut self.result_duties[index];
            current.inspected &= prefixes.iter().all(|prefix| prefix.duties[index].inspected);
            current.covered &= prefixes.iter().all(|prefix| prefix.duties[index].covered);
            current.returned &= initial.returned;
            // The cancelled activation cannot waive a caller-owned producer.
            current.abnormal = initial.abnormal;
        }
        let parents = context
            .checkpoints
            .iter()
            .map(|checkpoint| {
                self.cause(
                    CauseKind::BranchJoin,
                    checkpoint.span,
                    format!(
                        "cancellable scope prefix in activation {} retains its complete flow state",
                        checkpoint.owner.0
                    ),
                    [],
                )
            })
            .collect::<Vec<_>>();
        let cause = self.cause(CauseKind::BranchJoin, span, "scope cancellation joins every retained prefix without restoring scalar refinements or waiving outside Result duties", parents);
        if result.ty == Ty::Never {
            let error = self.standard_value(
                Ty::Named("Concurrent::TaskFault".into()),
                span,
                frame.owner,
                0x6211,
            );
            *result = self.make_result(false, error, span, frame.owner);
            result.ty = Ty::Result(
                Box::new(Ty::Never),
                Box::new(Ty::Named("Concurrent::TaskFault".into())),
            );
        }
        result.cause = cause;
        self.refresh_heap_fields();
        self.refresh_writable_roots();
    }
}

fn same_graph(
    left: &Projection,
    right: &Projection,
    loans: &BTreeMap<LoanId, BTreeSet<Participant>>,
) -> bool {
    left.bindings.len() == right.bindings.len()
        && left.fields.len() == right.fields.len()
        && left.uncertain == right.uncertain
        && left.arrays == right.arrays
        && left.fixed_arrays == right.fixed_arrays
        && left.bindings.iter().all(|(id, value)| {
            right
                .bindings
                .get(id)
                .is_some_and(|other| same_value(value, other, loans))
        })
        && left.fields.iter().all(|(key, value)| {
            right
                .fields
                .get(key)
                .is_some_and(|other| same_value(value, other, loans))
        })
}
fn same_value(
    left: &Value,
    right: &Value,
    loans: &BTreeMap<LoanId, BTreeSet<Participant>>,
) -> bool {
    fn normalize(value: &mut Value, loans: &BTreeMap<LoanId, BTreeSet<Participant>>) {
        let scalar = value.ty.scalar()
            && value.origins.nodes.is_empty()
            && value.callables.is_empty()
            && value.results.is_empty()
            && value.pending_copies.is_empty()
            && value.scoped.is_empty();
        if scalar {
            *value = Value::scalar(value.ty.clone(), None, CauseId(0));
            return;
        }
        value.constant = None;
        value.static_coordinate = None;
        value.cause = CauseId(0);
        value.origins.choices.clear();
        value.participants =
            super::recursive_calls::normalize_participants(&value.participants, loans);
        value.temporary = false;
        for nested in [
            &mut value.option_payload,
            &mut value.result_payload,
            &mut value.result_success,
            &mut value.result_error,
            &mut value.variant_payload,
        ]
        .into_iter()
        .flatten()
        .chain(value.variant_witnesses.values_mut())
        {
            normalize(nested, loans);
        }
    }
    let mut left = left.clone();
    let mut right = right.clone();
    normalize(&mut left, loans);
    normalize(&mut right, loans);
    left == right
}
fn widen(value: &mut Value) {
    // Cancellation may select an earlier scalar assignment. A predicate from
    // the completed body does not prove that prefix performed its tag tests.
    value.condition_inspections = Default::default();
    value.origins.choices.clear();
    value.constant = None;
    value.static_coordinate = None;
    value.unsuffixed_numeric = false;
    value.literal_number = false;
    value.option_tag = None;
    value.result_tag = None;
    value.variant_tag = None;
    for nested in [
        &mut value.option_payload,
        &mut value.result_payload,
        &mut value.result_success,
        &mut value.result_error,
        &mut value.variant_payload,
    ]
    .into_iter()
    .flatten()
    .chain(value.variant_witnesses.values_mut())
    {
        widen(nested);
    }
}
