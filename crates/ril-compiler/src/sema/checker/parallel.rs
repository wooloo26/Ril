//! Parallel contracts use the actual transitive callback invocation. A mutable
//! handle is only a temporary loan; it is never a proof of region independence.
use super::*;

pub(super) fn is_builtin(name: &str) -> bool {
    matches!(
        name,
        "Parallel::map"
            | "Parallel::map_bounded"
            | "Parallel::find"
            | "Parallel::first"
            | "Parallel::any"
            | "Parallel::fold"
            | "Parallel::join"
            | "Parallel::join3"
            | "Parallel::for_each"
    )
}

#[derive(Clone)]
enum PermissionBoundary {
    Pure,
    Join,
    Element(BTreeSet<NodeId>),
}

/// Local inputs/results survive callback evaluation, which can recycle an
/// allocation site. They are snapshots at an epoch, not permanent node IDs.
struct ParallelValue {
    value: Value,
    recency: usize,
}
impl ParallelValue {
    fn new(value: Value, recency: usize) -> Self {
        Self { value, recency }
    }
    fn current(&mut self, moves: &[(NodeId, NodeId)]) -> Value {
        for &(recent, older) in &moves[self.recency..] {
            copy::remap_value_origins(&mut self.value, recent, older);
        }
        self.recency = moves.len();
        self.value.clone()
    }
}

impl Checker {
    pub(super) fn parallel_builtin(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        if !is_builtin(name) {
            return None;
        }
        let count = match name {
            "Parallel::join3" | "Parallel::map_bounded" => 3,
            "Parallel::fold" => 4,
            _ => 2,
        };
        if args.len() != count {
            self.error(
                "E0314",
                span,
                format!("{name} requires {count} arguments"),
                [],
            );
            return Some(self.unit(span));
        }
        for (index, (mode, value, argument_span)) in args.iter().enumerate() {
            let expected = if name == "Parallel::for_each" && index == 0 {
                ParameterMode::Mut
            } else {
                ParameterMode::Read
            };
            if *mode != expected {
                self.error(
                    "E0405",
                    *argument_span,
                    "parallel argument mode mismatch",
                    [value.cause],
                );
            }
        }
        let bound_panics = name == "Parallel::map_bounded"
            && matches!(args[1].1.constant,
            Some(Constant::Integer(bound)) if bound <= 0);
        let before_bound = bound_panics.then(|| (self.snapshot_flow(), frame.obligations.clone()));
        let mut proofs = Vec::new();
        let mut output = if matches!(name, "Parallel::join" | "Parallel::join3") {
            let mut callbacks: Vec<_> = args
                .iter()
                .map(|(_, value, span)| {
                    (
                        ParallelValue::new(value.clone(), self.recency_moves.len()),
                        *span,
                    )
                })
                .collect();
            let staging = self.allocate(span, 0x5042, frame.owner);
            for (index, (callback, callback_span)) in callbacks.iter_mut().enumerate() {
                let callback = callback.current(&self.recency_moves);
                let (value, proof) = self.parallel_callback(
                    &callback,
                    vec![],
                    *callback_span,
                    frame,
                    PermissionBoundary::Join,
                );
                self.store_field(staging, Slot::Tuple(index as u32), value);
                proofs.push(proof);
            }
            for (index, left) in proofs.iter().enumerate() {
                for right in &proofs[index + 1..] {
                    self.parallel_disjoint(&left.accesses, &right.accesses, span);
                }
            }
            let values = (0..args.len())
                .map(|index| self.fields[&(staging, Slot::Tuple(index as u32))].clone())
                .collect();
            self.parallel_product(values, true, span, frame.owner)
        } else {
            let source = &args[0].1;
            let Ty::Array(element) =
                self.expanded(&self.collection_type(source), &mut BTreeSet::new())
            else {
                self.error(
                    "E0301",
                    args[0].2,
                    "parallel collection input must be an array",
                    [source.cause],
                );
                return Some(self.unit(span));
            };
            let mutable = name == "Parallel::for_each";
            if mutable {
                if source.permission != Permission::Write {
                    self.error(
                        "E0619",
                        args[0].2,
                        "for_each requires writable element loans",
                        [source.cause],
                    );
                }
                self.access(source, None, Mode::Write, args[0].2, frame);
            } else {
                if !self.parallel_immutable(source) {
                    self.error(
                        "E0605",
                        args[0].2,
                        "pure parallel input must be immutable",
                        [source.cause],
                    );
                }
                self.access(source, None, Mode::Read, args[0].2, frame);
            }
            if name == "Parallel::map_bounded" {
                self.require_type(&args[1].1, &Ty::Int("int".into()), args[1].2);
            }
            if name == "Parallel::fold" {
                self.parallel_fold(source, *element, args, span, frame, &mut proofs)
            } else {
                self.parallel_traverse(name, source, args.last().unwrap(), span, frame, &mut proofs)
            }
        };
        let cause = self.cause(
            CauseKind::Call,
            span,
            "parallel boundary proves finite callbacks, local effects and confined disjoint access",
            proofs.iter().map(|proof| proof.cause),
        );
        for proof in &mut proofs {
            for access in &mut proof.accesses {
                access.transport(&self.recency_moves);
            }
        }
        use super::super::ParallelOperation as Op;
        let operation = match name {
            "Parallel::map" => Op::Map,
            "Parallel::map_bounded" => Op::MapBounded,
            "Parallel::find" => Op::Find,
            "Parallel::first" => Op::First,
            "Parallel::any" => Op::Any,
            "Parallel::fold" => Op::Fold,
            "Parallel::join" => Op::Join,
            "Parallel::join3" => Op::Join3,
            "Parallel::for_each" => Op::ForEach,
            _ => unreachable!(),
        };
        self.parallel_boundaries
            .push(super::super::ParallelBoundary {
                span,
                operation,
                callbacks: proofs,
                cause,
            });
        if let Some((before, obligations)) = before_bound {
            self.restore_preview(&before);
            frame.obligations = obligations;
            output = self.unit(span);
            output.ty = Ty::Never;
            output.abnormal = true;
        }
        Some(output)
    }

    fn parallel_immutable(&self, value: &Value) -> bool {
        if self.contains_resource(value)
            || value.mutable_environment
            || value.observer_environment
            || value.publication == Publication::Live
            || self.has_unresolved_row(value)
        {
            return false;
        }
        value.publication == Publication::Immutable
            || value.ty.scalar()
            || (value.construction && self.construction_can_publish(value))
    }

    fn parallel_callback(
        &mut self,
        callback: &Value,
        arguments: Vec<(ParameterMode, Value, Span)>,
        span: Span,
        frame: &mut Frame,
        mut permission: PermissionBoundary,
    ) -> (Value, super::super::ParallelCallbackProof) {
        let before_bindings = self.bindings.len();
        let before_handlers = self.handler_definitions.len();
        let before_cleanup = self.cleanup_events.len();
        let recency = self.recency_moves.len();
        let mut child = self.frame(frame.env.clone(), true);
        self.scopes.set_parent(child.owner, frame.owner);
        // The parent's budget cannot certify a worker. A budget installed by
        // the callback itself still creates the ordinary semantic certificate.
        let budget = std::mem::take(&mut self.budget_coverage);
        let mut handle = callback.clone();
        let loan = LoanId(self.next_loan);
        self.next_loan += 1;
        self.loan_parents.insert(loan, handle.participants.clone());
        handle.participants = [Participant::Loan(loan)].into();
        handle.temporary = true;
        let mut output = self.invoke_generated_values(&handle, arguments, span, &mut child);
        if let PermissionBoundary::Element(nodes) = &mut permission {
            loop_graph::transport_nodes(nodes, &self.recency_moves[recency..]);
        }
        self.flush_handler_obligations(&mut child);
        self.budget_coverage = budget;
        if !child.obligations.effects.is_empty() {
            self.error(
                "E0605",
                span,
                "parallel callback has residual effects",
                [callback.cause],
            );
        }
        if child.obligations.symbolic {
            self.error(
                "E0605",
                span,
                "parallel callback lacks a complete transitive dependency proof",
                [callback.cause],
            );
        }
        let ambient_handlers: BTreeSet<_> = child
            .obligations
            .selected_handlers
            .iter()
            .copied()
            .filter(|id| *id < before_handlers)
            .collect();
        for (lexical, body) in self.selected_handler_bodies(&ambient_handlers) {
            let mut names = BTreeSet::new();
            expressions::collect_names(&body, &mut names);
            for binding in names.iter().filter_map(|name| lexical.get(name)) {
                let dependency = self.capture_value(*binding);
                if !self.parallel_handler_immutable(&dependency, &mut BTreeSet::new()) {
                    self.error(
                        "E0605",
                        span,
                        "parallel invocation selects an outside mutable or live handler",
                        [dependency.cause],
                    );
                }
            }
        }
        for (&binding, &mode) in &child.obligations.named {
            if binding >= before_bindings {
                continue;
            }
            let dependency = self.capture_value(binding);
            let permitted = match &permission {
                PermissionBoundary::Join => {
                    !self.contains_resource(&dependency) && mode != Mode::Retain
                }
                PermissionBoundary::Element(_) => {
                    mode == Mode::Read && self.parallel_immutable(&dependency)
                }
                PermissionBoundary::Pure => {
                    mode == Mode::Read && self.parallel_immutable(&dependency)
                }
            };
            if !permitted {
                self.error("E0605", span,
                    "parallel callee, handler or cleanup depends on outside mutable or resource authority",
                    [dependency.cause]);
            }
        }
        let mut accesses = self.current_accesses(&child.obligations.accesses);
        for access in &mut accesses {
            let local: BTreeSet<_> = access
                .origins
                .nodes
                .iter()
                .copied()
                .filter(|node| self.access_is_local(access, *node, child.owner))
                .collect();
            access.origins.nodes.retain(|node| !local.contains(node));
            for choices in access.origins.choices.values_mut() {
                for origins in choices {
                    origins.retain(|node| !local.contains(node));
                }
            }
            access
                .origin_owners
                .retain(|node, _| access.origins.nodes.contains(node));
            if access.mode == Mode::Read {
                continue;
            }
            let permitted = match &permission {
                PermissionBoundary::Join => access.mode != Mode::Retain,
                PermissionBoundary::Element(loan) => {
                    access.mode != Mode::Retain && access.origins.nodes.is_subset(loan)
                }
                PermissionBoundary::Pure => access.origins.nodes.is_empty(),
            };
            if !permitted {
                self.error(
                    "E0605",
                    access.span,
                    "parallel writes escape the temporary invocation loan",
                    [access.cause],
                );
            }
        }
        accesses.retain(|access| !access.origins.nodes.is_empty());
        if output.ty != Ty::Never && !self.parallel_immutable(&output) {
            self.error(
                "E0605",
                span,
                "parallel callback cannot return live or resource authority",
                [output.cause],
            );
        }
        if output.ty != Ty::Never && self.parallel_immutable(&output) {
            freeze_formal_value(&mut output);
        }
        let (mut termination, handlers) =
            self.selected_handler_termination(&child.obligations.selected_handlers, span);
        include_termination(
            &mut termination,
            &self.callable_termination(callback, span, &handlers),
        );
        for event in &self.cleanup_events[before_cleanup..] {
            let value = &self.bindings[event.binding].value;
            for node in &value.origins.nodes {
                if let Some(cleanup) = self.fields.get(&(*node, Slot::Field("on_close".into()))) {
                    include_termination(
                        &mut termination,
                        &self.callable_termination(cleanup, event.span, &handlers),
                    );
                }
            }
        }
        if termination.may_diverge
            || termination.unresolved
            || !termination.callable_parameters.is_empty()
        {
            self.error(
                "E0820",
                span,
                "parallel callback has no independent finite computation proof",
                [callback.cause],
            );
        }
        self.transfer_results(&output, child.owner, frame.owner);
        let mut outward = child.obligations.clone();
        for states in [
            &mut outward.named,
            &mut outward.concrete,
            &mut outward.direct,
        ] {
            states.retain(|binding, _| {
                !self.scope_is_within(self.bindings[*binding].owner, frame.owner)
            });
        }
        let loans = [(loan, callback.participants.clone())].into();
        for access in &mut outward.accesses {
            access.participants =
                super::recursive_calls::normalize_participants(&access.participants, &loans);
        }
        frame.obligations.include(&outward, false);
        (
            output,
            super::super::ParallelCallbackProof {
                cause: callback.cause,
                accesses,
                selected_handlers: child.obligations.selected_handlers,
                termination,
            },
        )
    }

    fn parallel_handler_immutable(&self, value: &Value, seen: &mut BTreeSet<BindingId>) -> bool {
        if !self.parallel_immutable(value) {
            return false;
        }
        for callable in &value.callables {
            let key = match callable {
                Callable::Named(id) => (false, *id),
                Callable::Closure(id) => (true, *id),
                _ => continue,
            };
            if let Some(summary) = self.callable_dependencies.get(&key) {
                for (&binding, &mode) in &summary.named {
                    if seen.insert(binding)
                        && (mode != Mode::Read
                            || !self.parallel_handler_immutable(&self.capture_value(binding), seen))
                    {
                        return false;
                    }
                }
            }
        }
        true
    }

    fn parallel_disjoint(&mut self, left: &[AccessFact], right: &[AccessFact], span: Span) {
        let left = self.current_accesses(left);
        let right = self.current_accesses(right);
        for a in &left {
            for b in &right {
                if a.mode == Mode::Read && b.mode == Mode::Read {
                    continue;
                }
                let slots_disjoint = match (&a.slot, &b.slot) {
                    (Some(a), Some(b)) => {
                        a != b
                            && !matches!(a, Slot::AnyIndex | Slot::RowTail(_))
                            && !matches!(b, Slot::AnyIndex | Slot::RowTail(_))
                    }
                    _ => false,
                };
                if !slots_disjoint && !self.origins_disjoint(&a.origins, &b.origins) {
                    self.error(
                        "E0619",
                        span,
                        "parallel write/read or write/write regions may overlap",
                        [a.cause, b.cause],
                    );
                    return;
                }
            }
        }
    }

    fn parallel_product(
        &mut self,
        children: Vec<Value>,
        tuple: bool,
        span: Span,
        owner: ScopeId,
    ) -> Value {
        let ty = if tuple {
            Ty::Tuple(children.iter().map(|value| value.ty.clone()).collect())
        } else {
            Ty::Array(Box::new(
                children
                    .first()
                    .map(|value| value.ty.clone())
                    .unwrap_or(Ty::Unknown),
            ))
        };
        let node = self.allocate(span, 0x5041, owner);
        let mut result = Value::reference(ty, node, self.heap.nodes[node.0 as usize].cause);
        if !tuple {
            self.array_lengths.insert(node, Some(children.len() as u64));
        }
        for (index, child) in children.into_iter().enumerate() {
            result.results.extend(&child.results);
            result.must_results.extend(&child.must_results);
            result.scoped.extend(&child.scoped);
            result
                .callback_parameters
                .extend(&child.callback_parameters);
            self.store_field(
                node,
                if tuple {
                    Slot::Tuple(index as u32)
                } else {
                    Slot::Index(index as i64)
                },
                child,
            );
        }
        if !tuple {
            self.complete_standard_array_source(&mut result, span);
        }
        result
    }

    fn parallel_exact_length(&self, source: &Value) -> Option<u64> {
        let count = self.known_array_length(source)?;
        source
            .origins
            .nodes
            .iter()
            .all(|node| {
                let slots: BTreeSet<_> = self
                    .fields
                    .keys()
                    .filter_map(|(parent, slot)| {
                        if parent != node {
                            return None;
                        }
                        match slot {
                            Slot::Index(index) => Some(*index),
                            _ => None,
                        }
                    })
                    .collect();
                !self.fields.contains_key(&(*node, Slot::AnyIndex))
                    && slots.len() as u64 == count
                    && slots.iter().copied().eq(0..count as i64)
            })
            .then_some(count)
    }

    fn parallel_element_region(&self, value: &Value, writable: bool) -> Origins {
        let reachable = |roots: &BTreeSet<NodeId>| {
            if writable {
                let mut branch = value.clone();
                branch.origins.nodes = roots.clone();
                self.writable_nodes(&branch)
            } else {
                self.heap.reachable(roots.iter().copied())
            }
        };
        Origins {
            nodes: reachable(&value.origins.nodes),
            choices: value
                .origins
                .choices
                .iter()
                .map(|(choice, branches)| (*choice, branches.iter().map(reachable).collect()))
                .collect(),
        }
    }

    fn parallel_traverse(
        &mut self,
        name: &str,
        source: &Value,
        callback: &(ParameterMode, Value, Span),
        span: Span,
        frame: &mut Frame,
        proofs: &mut Vec<super::super::ParallelCallbackProof>,
    ) -> Value {
        let Ty::Array(element) = self.expanded(&self.collection_type(source), &mut BTreeSet::new())
        else {
            unreachable!()
        };
        let element = *element;
        let count = self.known_array_length(source);
        let mutable = name == "Parallel::for_each";
        let explicit = self.parallel_exact_length(source);
        let mut input = ParallelValue::new(source.clone(), self.recency_moves.len());
        let mut callable = ParallelValue::new(callback.1.clone(), self.recency_moves.len());
        if mutable && explicit.is_none() && self.reference_bearing(&element) {
            self.error(
                "E0619",
                span,
                "for_each element regions are not proved pairwise disjoint",
                [source.cause],
            );
        }
        let iterations = explicit.unwrap_or(1).max(1);
        let preview = self.snapshot_flow();
        let old_obligations = frame.obligations.clone();
        let staging = self.allocate(span, 0x5043, frame.owner);
        let mut regions: Vec<(Origins, Origins)> = Vec::new();
        let mut regions_recency = self.recency_moves.len();
        for index in 0..iterations {
            let source = input.current(&self.recency_moves);
            let mut item = if count == Some(0) {
                self.formal_value(element.clone(), 0, span, &mut BTreeSet::new())
            } else {
                self.project(
                    &source,
                    if explicit.is_some() {
                        Slot::Index(index as i64)
                    } else {
                        Slot::AnyIndex
                    },
                    span,
                    frame,
                    true,
                )
            };
            item.ty = element.clone();
            for (read, write) in &mut regions {
                for &(recent, older) in &self.recency_moves[regions_recency..] {
                    read.remap(recent, older);
                    write.remap(recent, older);
                }
            }
            regions_recency = self.recency_moves.len();
            if mutable && count == Some(0) {
                // A hypothetical element validates the callback signature; no
                // actual readonly graph receives write permission.
                item.permission = Permission::Write;
            }
            let permission = if mutable {
                if item.permission != Permission::Write && count != Some(0) {
                    self.error(
                        "E0619",
                        span,
                        "for_each cannot lend a read-only element",
                        [item.cause],
                    );
                }
                let reachable = self.parallel_element_region(&item, false);
                let writable = self.parallel_element_region(&item, true);
                for (previous_read, previous_write) in &regions {
                    if !self.origins_disjoint(previous_write, &reachable)
                        || !self.origins_disjoint(&writable, previous_read)
                    {
                        self.error(
                            "E0619",
                            span,
                            "for_each elements have overlapping reachable regions",
                            [item.cause],
                        );
                    }
                }
                regions.push((reachable, writable.clone()));
                PermissionBoundary::Element(writable.nodes)
            } else {
                freeze_formal_value(&mut item);
                PermissionBoundary::Pure
            };
            let handle = callable.current(&self.recency_moves);
            let (value, proof) = self.parallel_callback(
                &handle,
                vec![(
                    if mutable {
                        ParameterMode::Mut
                    } else {
                        ParameterMode::Read
                    },
                    item,
                    span,
                )],
                callback.2,
                frame,
                permission,
            );
            if matches!(name, "Parallel::find" | "Parallel::first" | "Parallel::any") {
                self.require_type(&value, &Ty::Bool, callback.2);
            } else if mutable {
                self.require_type(&value, &Ty::Unit, callback.2);
            }
            for previous in proofs.iter() {
                self.parallel_disjoint(&previous.accesses, &proof.accesses, span);
            }
            proofs.push(proof);
            self.store_field(staging, Slot::Index(index as i64), value);
        }
        let mut outputs: Vec<_> = (0..iterations)
            .map(|index| self.fields[&(staging, Slot::Index(index as i64))].clone())
            .collect();
        let result_ty = outputs[0].ty.clone();
        if count == Some(0) {
            self.restore_preview(&preview);
            frame.obligations = old_obligations;
            outputs.clear();
        }
        let source = input.current(&self.recency_moves);
        match name {
            "Parallel::for_each" => self.unit(span),
            "Parallel::any" => Value::scalar(
                Ty::Bool,
                (count == Some(0)).then_some(Constant::Bool(false)),
                source.cause,
            ),
            "Parallel::find" | "Parallel::first" => {
                let mut item = if count == Some(0) {
                    Value::scalar(element.clone(), None, source.cause)
                } else {
                    self.project(&source, Slot::AnyIndex, span, frame, true)
                };
                item.ty = element;
                self.standard_option(item, (count == Some(0)).then_some(false), span, frame.owner)
            }
            _ => {
                let mut value = if explicit.is_some() {
                    self.parallel_product(outputs, false, span, frame.owner)
                } else {
                    self.standard_array_with_children(result_ty.clone(), outputs, span, frame.owner)
                };
                value.ty = Ty::Array(Box::new(result_ty));
                for node in &value.origins.nodes {
                    self.array_lengths.insert(*node, count);
                }
                if explicit.is_none() {
                    // An unknown number of results cannot be discharged by one
                    // arbitrary indexed projection.
                    for node in &value.origins.nodes {
                        if let Some(child) = self.fields.get_mut(&(*node, Slot::AnyIndex)) {
                            child.must_results.clear();
                            child.must_outer_results.clear();
                        }
                    }
                }
                value
            }
        }
    }

    fn parallel_fold(
        &mut self,
        source: &Value,
        element: Ty,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
        proofs: &mut Vec<super::super::ParallelCallbackProof>,
    ) -> Value {
        let count = self.known_array_length(source);
        let exact = self.parallel_exact_length(source);
        let mut input = ParallelValue::new(source.clone(), self.recency_moves.len());
        let mut callbacks: Vec<_> = args
            .iter()
            .map(|(_, value, _)| ParallelValue::new(value.clone(), self.recency_moves.len()))
            .collect();
        let groups = exact.map(|count| count.div_ceil(64).max(1)).unwrap_or(2);
        let staging = self.allocate(span, 0x5044, frame.owner);
        let mut values = Vec::new();
        let mut accumulator_type = None;
        for group in 0..groups {
            let handle = callbacks[1].current(&self.recency_moves);
            let (accumulator, proof) =
                self.parallel_callback(&handle, vec![], args[1].2, frame, PermissionBoundary::Pure);
            proofs.push(proof);
            if let Some(ty) = &accumulator_type {
                self.require_type(&accumulator, ty, span);
            } else {
                accumulator_type = Some(accumulator.ty.clone());
            }
            let mut accumulator = ParallelValue::new(accumulator, self.recency_moves.len());
            let steps = exact
                .map(|count| count.saturating_sub(group * 64).min(64))
                .unwrap_or(1);
            for index in 0..steps {
                let source = input.current(&self.recency_moves);
                let mut item = self.project(
                    &source,
                    if exact.is_some() {
                        Slot::Index((group * 64 + index) as i64)
                    } else {
                        Slot::AnyIndex
                    },
                    span,
                    frame,
                    true,
                );
                item.ty = element.clone();
                freeze_formal_value(&mut item);
                let mut previous = accumulator.current(&self.recency_moves);
                if exact.is_none() {
                    widen(&mut previous);
                    widen(&mut item);
                }
                let handle = callbacks[2].current(&self.recency_moves);
                let (mut next, proof) = self.parallel_callback(
                    &handle,
                    vec![
                        (ParameterMode::Read, previous, span),
                        (ParameterMode::Read, item, span),
                    ],
                    args[2].2,
                    frame,
                    PermissionBoundary::Pure,
                );
                self.require_type(&next, accumulator_type.as_ref().unwrap(), args[2].2);
                if next.ty == Ty::Never {
                    // A fault has no dependent runtime evaluation. Continue
                    // checking the static callback contract with the selected A.
                    next = self.formal_value(
                        accumulator_type.as_ref().unwrap().clone(),
                        0,
                        span,
                        &mut BTreeSet::new(),
                    );
                    freeze_formal_value(&mut next);
                }
                proofs.push(proof);
                accumulator = ParallelValue::new(next, self.recency_moves.len());
            }
            let accumulator = accumulator.current(&self.recency_moves);
            self.store_field(staging, Slot::Index(group as i64), accumulator);
        }
        values.extend((0..groups).map(|group| {
            ParallelValue::new(
                self.fields[&(staging, Slot::Index(group as i64))].clone(),
                self.recency_moves.len(),
            )
        }));
        // Every callback is checked even when reference evaluation does not
        // execute it, without creating runtime Result duties for that path.
        if count == Some(0) || groups == 1 {
            let before = self.snapshot_flow();
            let obligations = frame.obligations.clone();
            if count == Some(0) {
                let item = self.formal_value(element, 0, span, &mut BTreeSet::new());
                let sample = values[0].current(&self.recency_moves);
                let handle = callbacks[2].current(&self.recency_moves);
                let (value, proof) = self.parallel_callback(
                    &handle,
                    vec![
                        (ParameterMode::Read, sample.clone(), span),
                        (ParameterMode::Read, item, span),
                    ],
                    args[2].2,
                    frame,
                    PermissionBoundary::Pure,
                );
                self.require_type(&value, accumulator_type.as_ref().unwrap(), args[2].2);
                proofs.push(proof);
            }
            let sample = values[0].current(&self.recency_moves);
            let handle = callbacks[3].current(&self.recency_moves);
            let (value, proof) = self.parallel_callback(
                &handle,
                vec![
                    (ParameterMode::Read, sample.clone(), span),
                    (ParameterMode::Read, sample, span),
                ],
                args[3].2,
                frame,
                PermissionBoundary::Pure,
            );
            self.require_type(&value, accumulator_type.as_ref().unwrap(), args[3].2);
            proofs.push(proof);
            self.restore_preview(&before);
            frame.obligations = obligations;
        }
        while values.len() > 1 {
            let mut next = Vec::new();
            let mut pairs = values.into_iter();
            while let Some(mut left) = pairs.next() {
                let Some(mut right) = pairs.next() else {
                    next.push(left);
                    break;
                };
                let left = left.current(&self.recency_moves);
                let right = right.current(&self.recency_moves);
                let handle = callbacks[3].current(&self.recency_moves);
                let (value, proof) = self.parallel_callback(
                    &handle,
                    vec![
                        (ParameterMode::Read, left, span),
                        (ParameterMode::Read, right, span),
                    ],
                    args[3].2,
                    frame,
                    PermissionBoundary::Pure,
                );
                self.require_type(&value, accumulator_type.as_ref().unwrap(), args[3].2);
                proofs.push(proof);
                next.push(ParallelValue::new(value, self.recency_moves.len()));
            }
            values = next;
        }
        let mut value = values.remove(0).current(&self.recency_moves);
        if exact.is_none() {
            value.constant = None;
        }
        value
    }
}

fn widen(value: &mut Value) {
    value.constant = None;
    value.result_tag = None;
    value.option_tag = None;
    value.variant_tag = None;
    for payload in [
        &mut value.result_payload,
        &mut value.result_success,
        &mut value.result_error,
        &mut value.option_payload,
        &mut value.variant_payload,
    ]
    .into_iter()
    .flatten()
    .chain(value.variant_witnesses.values_mut())
    {
        widen(payload);
    }
}

fn include_termination(
    target: &mut crate::termination::Judgment,
    source: &crate::termination::Judgment,
) {
    target.may_diverge |= source.may_diverge;
    target.unresolved |= source.unresolved;
    target
        .callable_parameters
        .extend(&source.callable_parameters);
}
#[cfg(test)]
mod tests {
    use super::*;
    fn check(source: &str) -> crate::sema::AnalyzeOutcome {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        crate::sema::analyze(&parsed.program, FileId(0))
    }
    fn accepts(source: &str) {
        let result = check(source);
        assert!(
            result.program.is_some(),
            "{source}\n{:?}\n{:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    fn rejects(source: &str, code: &str) {
        let result = check(source);
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == code),
            "expected {code}: {source}\n{:?}\n{:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn parallel_pure_empty_and_fold_contracts() {
        accepts(
            "fn example(){let xs=Parallel::map([1,2],\\x->x+1);assert(xs==[2,3]);assert(Parallel::first([1,2],\\x->x>1)==Some(2));assert(Parallel::any([1,2],\\x->x==1));let empty:[]int=[];assert(Parallel::map(empty,\\x->x+1)==[]);let value=Parallel::fold(empty,\\->10,\\acc,x->acc+x,\\a,b->a+b);assert(value==10);let _=Parallel::join3(\\->1,\\->2,\\->3)}",
        );
        accepts("halt fn example()->[]int{Parallel::map([1,2],\\x->x+1)}");
        rejects(
            "fn example(){let _=Parallel::map_bounded([1],true,\\x->x)}",
            "E0301",
        );
        rejects(
            "fn example(){let _=Parallel::fold([1],\\->0,\\a,x->true,\\a,b->a+b)}",
            "E0301",
        );
    }
    #[test]
    fn parallel_join_proves_access_regions_and_retains_writes() {
        accepts(
            "type Cell={mut count:int}\nfn example(){let mut copy=(Cell.{count:0},Cell.{count:0});let _=Parallel::join(\\->{copy.0.count+=1},\\->{copy.1.count+=1});assert(copy.0.count==1)}",
        );
        rejects(
            "type Cell={mut count:int}\nfn example(){let original=Cell.{count:0};let mut copy=^mut clone((original,original));let _=Parallel::join(\\->{copy.0.count+=1},\\->{copy.1.count+=1})}",
            "E0619",
        );
        rejects(
            "type Cell={mut count:int}\nfn example(){let mut cell=Cell.{count:0};let _=Parallel::join(\\->{cell.count+=1},\\->cell.count)}",
            "E0619",
        );
    }
    #[test]
    fn parallel_outside_state_and_transitive_helpers_are_checked() {
        rejects(
            "type Cell={mut count:int}\nfn example(){let mut cell=Cell.{count:0};let _=Parallel::map([1],\\n->{cell.count+=n;n})}",
            "E0605",
        );
        rejects(
            "type Cell={mut count:int}\nlet mut cell=Cell.{count:0}\nfn hidden()->int &{cell}{cell.count}\nfn example() &{cell}{cell.count+=1;let _=Parallel::map([1],\\n->n+hidden())}",
            "E0605",
        );
        rejects(
            "fn spin()->int{loop{}}\nfn example(){let _=Parallel::map([1],\\n->spin())}",
            "E0820",
        );
        rejects(
            "fn example(){let empty:[]int=[];let _=Parallel::map(empty,\\n->{loop{}})}",
            "E0820",
        );
        rejects(
            "fn example() @Div {let _=Parallel::map([1],\\n->Div::exhausted())}",
            "E0605",
        );
    }
    #[test]
    fn parallel_for_each_requires_each_real_writable_element() {
        accepts(
            "type Cell={mut count:int}\nfn example(){let mut cells=[Cell.{count:1},Cell.{count:2}];cells !> Parallel::for_each(\\mut cell->{cell.count*=2});assert(cells[0].count==2)}",
        );
        rejects(
            "type Cell={mut count:int}\nfn example(){let original=Cell.{count:1};let mut cells=^mut clone([original,original]);cells !> Parallel::for_each(\\mut cell->{cell.count*=2})}",
            "E0619",
        );
        rejects(
            "type Cell={mut count:int}\nfn example(mut cells:[]Cell) &mut {cells !> Parallel::for_each(\\mut cell->{cell.count*=2})}",
            "E0619",
        );
        rejects(
            "type Cell={mut count:int}\nfn example(){let base=Cell.{count:1};let mut cells=[base];cells !> Parallel::for_each(\\mut cell->{cell.count*=2})}",
            "E0619",
        );
    }
    #[test]
    fn parallel_result_obligations_reach_the_actual_output() {
        accepts(
            "fn example(){let (a,b)=Parallel::join(\\->Ok(1),\\->Err(2));assert(a is Ok(1));assert(b is Err(2))}",
        );
        rejects(
            "fn example(){let _=Parallel::join(\\->Ok(1),\\->Err(2))}",
            "E0720",
        );
        rejects(
            "fn example(){let _=Parallel::map([1,2],\\n->Ok(n))}",
            "E0720",
        );
        accepts(
            "fn example(){let values=Parallel::map([1,2],\\n->Ok(n));assert(values[0] is Ok(1));assert(values[1] is Ok(2))}",
        );
        let helpers = "fn init()->Result<int,str>{Ok(0)}\nfn add(acc:Result<int,str>,x:int)->Result<int,str>{let value=acc?;Ok(value+x)}\nfn merge(a:Result<int,str>,b:Result<int,str>)->Result<int,str>{let left=a?;let right=b?;Ok(left+right)}\n";
        accepts(&format!(
            "{helpers}fn example(){{let result=Parallel::fold([1,2],init,add,merge);assert(result is Ok(3))}}"
        ));
        accepts(&format!(
            "{helpers}fn example(items:Immut<[]int>)->Result<int,str>{{Parallel::fold(items,init,add,merge)}}"
        ));
        rejects(
            &format!("{helpers}fn example(){{let _=Parallel::fold([1,2],init,add,merge)}}"),
            "E0720",
        );
        let items = vec!["0"; 65].join(",");
        accepts(&format!(
            "{helpers}fn example(){{let result=Parallel::fold([{items}],init,add,merge);assert(result is Ok(0))}}"
        ));
    }
    #[test]
    fn parallel_handlers_cleanup_budgets_and_actual_callback_aliases() {
        accepts(
            "eff Read{get()->int}\nfn example(){let callback={with Read::get()->resume 40;\\n:int->Read::get()+n};let values=Parallel::map([1,2],callback);assert(values==[41,42])}",
        );
        rejects(
            "type Guard={on_close:fn()->()}\nfn example(){let _=Parallel::map([1],\\n->{let scoped guard=Guard.{on_close: \\->{loop{}}};n})}",
            "E0820",
        );
        accepts(
            "eff Read{get()->int}\nfn example(){let values=Parallel::map([1,2],\\n->{with Read::get()->resume n;Read::get()+1});assert(values==[2,3])}",
        );
        accepts(
            "fn spin()->int{loop{}}\nfn example(){let values=Parallel::map([1,2],\\n->{with Div::exhausted()->n+10;Div::budget(3,spin)});assert(values==[11,12])}",
        );
        accepts(
            "type Guard={on_close:fn()->()}\nfn example(){assert(Parallel::any([0,1],\\n->{if n==0{true}else{let scoped guard=Guard.{on_close: \\->panic(\"cleanup\")};panic(\"right\")}}))}",
        );
        accepts(
            "fn apply(callback:fn(int)->int,x:int)->int{callback(x)}\nfn example(){let step=\\n:int->n+1;let callback=\\n->apply(step,n);let _=Parallel::map([1,2],callback)}",
        );
        rejects(
            "type Cell={mut count:int}\neff Read{get()->int}\nfn example(){let mut cell=Cell.{count:1};with Read::get()->{cell.count+=1;resume cell.count};let _=Parallel::map([1],\\n->Read::get()+n)}",
            "E0605",
        );
        rejects(
            "type Cell={mut count:int}\neff Read{get()->int}\nfn example(){let mut cell=Cell.{count:1};with Read::get()->{cell.count+=1;resume cell.count};let _=Parallel::join(\\->Read::get(),\\->0)}",
            "E0605",
        );
        rejects(
            "type Cell={mut count:int}\ntype Guard={on_close:fn()->()}\nfn example(){let mut cell=Cell.{count:1};let _=Parallel::map([1],\\n->{let scoped guard=Guard.{on_close: \\->{cell.count+=1}};n})}",
            "E0605",
        );
    }

    #[test]
    fn parallel_disjointness_agrees_with_finite_alias_graphs() {
        // Exhaust the concrete two-node graphs and both read/write modes. This
        // checks the proof algebra independently from source expression paths.
        for same in [false, true] {
            for left_write in [false, true] {
                for right_write in [false, true] {
                    let mut checker = Checker::new(FileId(0));
                    let span = Span {
                        file: FileId(0),
                        start: 0,
                        end: 1,
                    };
                    let a = checker.allocate(span, 1, ScopeId(0));
                    let b = if same {
                        a
                    } else {
                        checker.allocate(span, 2, ScopeId(0))
                    };
                    let access = |node, writes| AccessFact {
                        observed_recency: 0,
                        recency: 0,
                        origin_owners: [(node, AccessOwners::Known([ScopeId(0)].into()))].into(),
                        origins: Origins::one(node),
                        slot: None,
                        mode: if writes { Mode::Write } else { Mode::Read },
                        participants: BTreeSet::new(),
                        cause: CauseId(0),
                        span,
                    };
                    checker.parallel_disjoint(
                        &[access(a, left_write)],
                        &[access(b, right_write)],
                        span,
                    );
                    assert_eq!(
                        !checker.diagnostics.is_empty(),
                        same && (left_write || right_write)
                    );
                }
            }
        }
        let mut checker = Checker::new(FileId(0));
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 1,
        };
        let a = checker.allocate(span, 1, ScopeId(0));
        let b = checker.allocate(span, 2, ScopeId(0));
        let origins = |reverse| Origins {
            nodes: [a, b].into(),
            choices: [(
                0,
                if reverse {
                    vec![[b].into(), [a].into()]
                } else {
                    vec![[a].into(), [b].into()]
                },
            )]
            .into(),
        };
        let access = |origins| AccessFact {
            observed_recency: 0,
            recency: 0,
            origin_owners: BTreeMap::new(),
            origins,
            slot: None,
            mode: Mode::Write,
            participants: BTreeSet::new(),
            cause: CauseId(0),
            span,
        };
        checker.parallel_disjoint(&[access(origins(false))], &[access(origins(true))], span);
        assert!(
            checker.diagnostics.is_empty(),
            "correlated permutation retains disjointness"
        );
        checker.parallel_disjoint(&[access(origins(false))], &[access(origins(false))], span);
        assert!(
            checker
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0619")
        );
    }
}
