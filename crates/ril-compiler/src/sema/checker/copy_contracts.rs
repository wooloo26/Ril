use super::super::copy_contract::*;
use super::super::copy_eligibility::{AbstractMember, Constituent, Rejection};
use super::*;

#[derive(Default)]
struct MissingCopyScan {
    active: BTreeSet<String>,
    budget: resources::TypeScanBudget,
}

impl Checker {
    pub(super) fn invalidate_opaque_collection_members(&mut self, node: NodeId) {
        let slot = Slot::Field("$members".into());
        if let Some(witness) = self.fields.get_mut(&(node, slot.clone())) {
            witness.constant = None;
            self.uncertain_slots.insert((node, slot));
        }
    }

    fn opaque_collection_qualification(&self, value: &Value, ty: &Ty) -> Option<Constituent> {
        let Ty::Applied {
            constructor,
            arguments,
        } = ty
        else {
            return None;
        };
        if !matches!(constructor.as_str(), "Deque::Deque" | "Heap::Heap") {
            return None;
        }
        if !matches!(
            arguments.as_slice(),
            [TypeArgument::Type(_) | TypeArgument::CanonicalType { .. }]
        ) || value.origins.nodes.is_empty()
        {
            return Some(Constituent::Incomplete);
        }
        let complete = value.origins.nodes.iter().all(|node| {
            self.fields
                .get(&(*node, Slot::Field("$members".into())))
                .is_some_and(|witness| {
                    witness.ty == Ty::Unit && witness.constant == Some(Constant::Unit)
                })
                && !self
                    .uncertain_slots
                    .iter()
                    .any(|(origin, _)| origin == node)
                && (constructor != "Heap::Heap"
                    || self
                        .fields
                        .contains_key(&(*node, Slot::Field("$compare".into()))))
        });
        // The shell is ordinary, but all element and comparator values are
        // still assessed independently in this boundary's frozen graph.
        Some(if complete {
            Constituent::Ordinary
        } else {
            Constituent::Incomplete
        })
    }
    /// Includes inlined sums, graph fields and captured values. A new shell or
    /// a lost optional witness is never evidence that an obligation vanished.
    pub(super) fn pending_copy_dependencies(&self, value: &Value) -> BTreeSet<CopyBoundaryId> {
        let mut result = BTreeSet::new();
        let mut nodes = BTreeSet::new();
        let mut bindings = BTreeSet::new();
        let mut pending = vec![value];
        while let Some(value) = pending.pop() {
            result.extend(&value.pending_copies);
            pending.extend(
                [
                    &value.option_payload,
                    &value.result_payload,
                    &value.result_success,
                    &value.result_error,
                    &value.variant_payload,
                ]
                .into_iter()
                .flatten()
                .map(Box::as_ref),
            );
            pending.extend(value.variant_witnesses.values().map(Box::as_ref));
            for origin in &value.origins.nodes {
                if nodes.insert(*origin) {
                    pending.extend(
                        self.fields
                            .iter()
                            .filter_map(|((parent, _), value)| (parent == origin).then_some(value)),
                    );
                }
            }
            for callable in &value.callables {
                let captures = match callable {
                    Callable::Named(id, _) => Some(&self.functions[*id].captures),
                    Callable::Closure(id) => Some(&self.closures[*id].captures),
                    _ => None,
                };
                if let Some(captures) = captures {
                    for capture in captures {
                        if bindings.insert(*capture) {
                            pending.push(&self.bindings[*capture].value);
                        }
                    }
                }
            }
        }
        result
    }

    pub(super) fn require_copy_dependencies(
        &mut self,
        value: &Value,
        span: Span,
        usage: &str,
    ) -> bool {
        if self.pending_copy_dependencies(value).is_empty() {
            return true;
        }
        self.unsupported(
            span,
            format!(
                "{usage} requires the pending copy qualification and transfer to be instantiated"
            ),
        );
        false
    }

    pub(super) fn forwards_conditional_copy(&self, value: &Value, frame: &Frame) -> bool {
        let Some(current) = self.copy_invocation_stack.last() else {
            return false;
        };
        let target = self.copy_invocations[current.0 as usize].target;
        let pending = self.pending_copy_dependencies(value);
        !pending.is_empty()
            && frame.definition == Some(target)
            && frame.callable_owner == Some(CallableOwner::Function(target))
            && pending.iter().all(|id| {
                self.copy_boundaries
                    .get(id.0 as usize)
                    .is_some_and(|boundary| {
                        boundary.template
                            && boundary
                                .template_root
                                .is_some_and(|root| self.copy_invocation_stack.contains(&root))
                    })
            })
    }

    pub(super) fn clone_value(
        &mut self,
        source: &Value,
        span: Span,
        frame: &mut Frame,
        immutable: bool,
    ) -> Value {
        // Capture before allocation can recycle recent nodes or rewrite fields.
        let mut proof = self.copy_boundary(source, span, frame, immutable);
        if let Some(root) = self.copy_template_root(&proof, frame) {
            proof.template = true;
            proof.template_root = Some(root);
            proof.requirements.push(CopyRequirement {
                constituent: 0,
                kind: CopyRequirementKind::DeferredTransfer,
            });
            // Conditional output has the original graph as a conservative
            // placeholder. It creates no allocation, permission or isolation.
            let mut output = source.clone();
            output.ty = match (&source.ty, immutable) {
                (Ty::Immutable(inner), false) => *inner.clone(),
                (Ty::Immutable(_), true) => source.ty.clone(),
                (_, true) => Ty::Immutable(Box::new(source.ty.clone())),
                _ => source.ty.clone(),
            };
            output.permission = Permission::Read;
            output.construction = false;
            output.marker = false;
            output.cause = proof.cause;
            let mut pending = self.pending_copy_dependencies(source);
            pending.insert(proof.id);
            output.inherit_copy_dependencies(&pending);
            frame.obligations.copy_boundaries.extend(pending);
            self.copy_boundaries.push(proof);
            return output;
        }
        let diagnostics = self.diagnostics.len();
        let unsupported = self.unsupported.len();
        self.require_copy_dependencies(source, span, "copying a conditional copy output");
        let eligibility = proof.requirements.is_empty();
        let mut result =
            self.clone_value_unrecorded(source, span, frame.owner, immutable, eligibility);
        if proof.constituents.iter().any(|item| {
            matches!(
                item.qualification,
                Constituent::Deferred(AbstractMember::CallableEnvironment)
            )
        }) && self.unsupported.len() == unsupported
        {
            self.unsupported(
                span,
                "copy eligibility of an abstract callable payload environment is not established",
            );
        }
        if proof
            .constituents
            .iter()
            .any(|item| matches!(item.qualification, Constituent::Deferred(_)))
            && self.unsupported.len() == unsupported
        {
            self.unsupported(
                span,
                "copy eligibility retains unresolved source-indexed generic or row requirements",
            );
        }
        if proof.constituents.iter().any(|item| {
            matches!(
                item.qualification,
                Constituent::Rejected(Rejection::RetainedEnvironment)
            )
        }) && self.diagnostics.len() == diagnostics
        {
            self.error(
                "E0530",
                span,
                "retained callable environments cannot be copied",
                [source.cause],
            );
        }
        if proof
            .constituents
            .iter()
            .any(|item| matches!(item.qualification, Constituent::Incomplete))
            && self.unsupported.len() == unsupported
        {
            self.unsupported(
                span,
                "copy eligibility requires complete constituent graph witnesses",
            );
        }
        if diagnostics != self.diagnostics.len() || unsupported != self.unsupported.len() {
            proof.requirements.push(CopyRequirement {
                constituent: 0,
                kind: CopyRequirementKind::Transfer,
            });
        }
        if proof.requirements.is_empty() {
            (proof.output_nodes, proof.output_relations) = self.copy_graph_snapshot(&result);
            proof.output = Some(result.clone());
            proof.output_allocation_epoch = Some(self.recency_moves.len());
        } else {
            let mut dependencies = self.pending_copy_dependencies(source);
            dependencies.insert(proof.id);
            result.inherit_copy_dependencies(&dependencies);
        }
        frame
            .obligations
            .copy_boundaries
            .extend(self.pending_copy_dependencies(source));
        frame.obligations.copy_boundaries.insert(proof.id);
        self.copy_boundaries.push(proof);
        result
    }

    fn copy_template_root(
        &mut self,
        proof: &CopyBoundary,
        frame: &Frame,
    ) -> Option<super::super::copy_templates::InstanceId> {
        let current = self.copy_invocation_stack.last().copied()?;
        let target = self.copy_invocations[current.0 as usize].target;
        if frame.definition != Some(target)
            || frame.callable_owner != Some(CallableOwner::Function(target))
            || proof.requirements.is_empty()
            || proof.constituents.iter().any(|part| {
                matches!(
                    part.qualification,
                    Constituent::Rejected(_) | Constituent::Incomplete
                )
            })
            || proof.requirements.iter().any(|requirement| {
                !matches!(
                    requirement.kind,
                    CopyRequirementKind::Eligibility | CopyRequirementKind::PriorBoundary(_)
                )
            })
        {
            return None;
        }
        for &root in self.copy_invocation_stack.iter().rev() {
            let probe = &self.copy_invocations[root.0 as usize];
            if !probe.declaration_probe {
                continue;
            }
            let origins = self
                .application_effect
                .with_work(|work| {
                    let mut budget = crate::sema::source_types::WorkLimit::new(*work);
                    let result = (|| {
                        budget.charge(probe.entry.arguments.len())?;
                        let mut origins = BTreeSet::new();
                        for argument in probe.entry.arguments.iter() {
                            let view = argument.snapshot_view(&mut budget)?;
                            budget.charge(view.nodes.len().saturating_mul(
                                1 + origins.len().checked_ilog2().unwrap_or(0) as usize,
                            ))?;
                            origins.extend(view.nodes.iter().map(|node| node.origin));
                        }
                        Ok::<_, crate::sema::source_types::SourceTypesError>(origins)
                    })();
                    *work = budget.remaining();
                    result
                })
                .ok()?;
            let anchored =
                |nodes: &BTreeSet<NodeId>| !nodes.is_empty() && nodes.is_subset(&origins);
            if proof
                .constituents
                .iter()
                .filter(|part| matches!(part.qualification, Constituent::Deferred(_)))
                .all(|part| {
                    if let Some(source) = &part.source {
                        anchored(&source.origins.nodes)
                    } else if let Some(parent) = part.parent {
                        origins.contains(&parent)
                    } else {
                        anchored(&proof.source.origins.nodes)
                    }
                })
                && proof
                    .requirements
                    .iter()
                    .all(|requirement| match requirement.kind {
                        CopyRequirementKind::PriorBoundary(id) => self
                            .copy_boundaries
                            .get(id.0 as usize)
                            .is_some_and(|boundary| boundary.template_root == Some(root)),
                        _ => true,
                    })
            {
                return Some(root);
            }
        }
        None
    }

    fn copy_boundary(
        &mut self,
        source: &Value,
        span: Span,
        frame: &Frame,
        immutable: bool,
    ) -> CopyBoundary {
        let (nodes, relations) = self.copy_graph_snapshot(source);
        let mut constituents = Vec::new();
        self.copy_constituents(source, None, vec![], &mut constituents);
        for node in &nodes {
            for (slot, value) in &node.fields {
                self.copy_constituents(
                    value,
                    Some(node.origin),
                    vec![CopyProjection::Storage(slot.clone())],
                    &mut constituents,
                );
            }
        }
        let mut requirements: Vec<_> = constituents
            .iter()
            .enumerate()
            .filter_map(|(index, value)| {
                (!matches!(
                    value.qualification,
                    Constituent::Ordinary | Constituent::EnvironmentFreeCallable
                ))
                .then_some(CopyRequirement {
                    constituent: index as u32,
                    kind: CopyRequirementKind::Eligibility,
                })
            })
            .collect();
        requirements.extend(
            self.pending_copy_dependencies(source)
                .into_iter()
                .map(|id| CopyRequirement {
                    constituent: 0,
                    kind: CopyRequirementKind::PriorBoundary(id),
                }),
        );
        if self.has_window(source) {
            requirements.push(CopyRequirement {
                constituent: 0,
                kind: CopyRequirementKind::WindowGraph,
            });
        }
        if nodes
            .iter()
            .flat_map(|node| &node.fields)
            .any(|(_, value)| !value.results.is_subset(&source.results))
        {
            requirements.push(CopyRequirement {
                constituent: 0,
                kind: CopyRequirementKind::ResultMembership,
            });
        }
        let cause = self.cause(
            CauseKind::Restriction,
            span,
            "copy eligibility requires each reachable constituent and its graph transfer",
            [source.cause],
        );
        CopyBoundary {
            id: CopyBoundaryId(self.copy_boundaries.len() as u32),
            input_allocation_epoch: self.recency_moves.len(),
            output_allocation_epoch: None,
            owner: frame.definition,
            activation: frame.owner,
            span,
            mode: if immutable {
                CopyMode::Immutable
            } else {
                CopyMode::Mutable
            },
            cause,
            source: source.clone(),
            nodes,
            relations,
            constituents,
            requirements,
            output: None,
            output_nodes: vec![],
            output_relations: vec![],
            invocation: self.copy_invocation_stack.last().copied(),
            source_event: self.application_effect.current_call_event(),
            template: false,
            template_root: None,
        }
    }

    pub(super) fn copy_graph_snapshot(
        &self,
        source: &Value,
    ) -> (Vec<CopyNode>, Vec<(NodeId, NodeId, Relation)>) {
        let reachable = self.heap.reachable(source.origins.nodes.iter().copied());
        let mut nodes = Vec::new();
        for &origin in &reachable {
            let fact = self.heap.nodes[origin.0 as usize].clone();
            let fields: Vec<_> = self
                .fields
                .iter()
                .filter(|((node, _), _)| *node == origin)
                .map(|((_, slot), value)| (slot.clone(), value.clone()))
                .collect();
            nodes.push(CopyNode {
                origin,
                fact,
                fields,
                length: self.array_lengths.get(&origin).copied(),
                fixed: self.fixed_arrays.contains(&origin),
            });
        }
        let mut relations = Vec::new();
        for (index, a) in nodes.iter().enumerate() {
            for b in &nodes[index..] {
                relations.push((a.origin, b.origin, self.heap.relation(a.origin, b.origin)));
            }
        }
        (nodes, relations)
    }

    fn copy_constituents(
        &self,
        value: &Value,
        parent: Option<NodeId>,
        path: Vec<CopyProjection>,
        result: &mut Vec<CopyConstituent>,
    ) {
        let mut ty = self
            .capability_shallow_type(&value.ty)
            .unwrap_or(Ty::Unknown);
        while let Ty::Immutable(inner) = ty {
            ty = *inner;
        }
        let qualification = if value.mutable_environment || value.observer_environment {
            Constituent::Rejected(Rejection::RetainedEnvironment)
        } else {
            self.copy_shallow_qualification(value, &ty)
        };
        result.push(CopyConstituent {
            parent,
            path: path.clone(),
            source: Some(value.clone()),
            ty: value.ty.clone(),
            cause: value.cause,
            qualification,
        });
        self.copy_missing_storage(value, &ty, parent, &path, result);
        let mut visit = |payload: Option<&Value>, expected: &Ty, projection: CopyProjection| {
            let mut path = path.clone();
            path.push(projection);
            if let Some(payload) = payload {
                self.copy_constituents(payload, parent, path, result);
            } else {
                // A declared primitive shape is complete, but a function type
                // does not witness its environment and a binder does not prove
                // any particular instantiation's copy eligibility.
                self.copy_missing_constituents(
                    expected,
                    value.cause,
                    parent,
                    path,
                    result,
                    &mut MissingCopyScan::default(),
                );
            }
        };
        match &ty {
            Ty::Optional(inner) if value.option_tag != Some(false) => {
                visit(
                    value.option_payload.as_deref(),
                    inner,
                    CopyProjection::OptionPayload,
                );
            }
            Ty::Result(ok, error) => {
                if value.result_tag != Some(false) {
                    visit(
                        value.result_success.as_deref().or_else(|| {
                            (value.result_tag == Some(true))
                                .then_some(value.result_payload.as_deref())
                                .flatten()
                        }),
                        ok,
                        CopyProjection::ResultSuccess,
                    );
                }
                if value.result_tag != Some(true) {
                    visit(
                        value.result_error.as_deref().or_else(|| {
                            (value.result_tag == Some(false))
                                .then_some(value.result_payload.as_deref())
                                .flatten()
                        }),
                        error,
                        CopyProjection::ResultError,
                    );
                }
            }
            _ => {
                let constructors: Vec<_> = self
                    .constructors
                    .values()
                    .filter(|constructor| constructor.owner == ty)
                    .collect();
                if !constructors.is_empty() {
                    for constructor in constructors {
                        if value
                            .variant_tag
                            .as_ref()
                            .is_some_and(|tag| *tag != constructor.tag)
                        {
                            continue;
                        }
                        if constructor.has_payload {
                            visit(
                                value.variant_witness(&constructor.tag),
                                &constructor.payload,
                                CopyProjection::Variant(constructor.tag.clone()),
                            );
                        }
                    }
                    return;
                }
                for (tag, payload) in &value.variant_witnesses {
                    visit(
                        Some(payload),
                        &payload.ty,
                        CopyProjection::Variant(tag.clone()),
                    );
                }
                if value.variant_witnesses.is_empty()
                    && let Some(payload) = &value.variant_payload
                {
                    visit(
                        Some(payload),
                        &payload.ty,
                        CopyProjection::Variant(value.variant_tag.clone().unwrap_or_default()),
                    );
                }
            }
        }
    }

    /// Missing lazy projections cannot be assumed to describe a complete
    /// object. Preserve each potential member's independent latent condition.
    fn copy_missing_storage(
        &self,
        value: &Value,
        ty: &Ty,
        parent: Option<NodeId>,
        path: &[CopyProjection],
        result: &mut Vec<CopyConstituent>,
    ) {
        let members: Vec<_> = match ty {
            Ty::Record(fields) | Ty::OpenRecord { fields, .. } => fields
                .iter()
                .map(|(name, (_, ty))| (Slot::Field(name.clone()), ty))
                .collect(),
            Ty::Tuple(items) => items
                .iter()
                .enumerate()
                .map(|(index, ty)| (Slot::Tuple(index as u32), ty))
                .collect(),
            Ty::Array(inner) | Ty::Set(inner) => vec![(Slot::AnyIndex, inner.as_ref())],
            Ty::Map(key, inner) => vec![
                (Slot::Field("key".into()), key.as_ref()),
                (Slot::AnyIndex, inner.as_ref()),
            ],
            _ => return,
        };
        for (slot, expected) in members {
            for origin in value
                .origins
                .nodes
                .iter()
                .copied()
                .map(Some)
                .chain(value.origins.nodes.is_empty().then_some(None))
            {
                if let Some(origin) = origin {
                    if matches!(ty, Ty::Array(_) | Ty::Map(..) | Ty::Set(_))
                        && self.array_lengths.get(&origin) == Some(&Some(0))
                    {
                        continue;
                    }
                    if self.fields.contains_key(&(origin, slot.clone())) {
                        continue;
                    }
                    if slot == Slot::AnyIndex
                        && self
                            .array_lengths
                            .get(&origin)
                            .copied()
                            .flatten()
                            .is_some_and(|length| {
                                (0..length).all(|index| {
                                    self.fields
                                        .contains_key(&(origin, Slot::Index(index as i64)))
                                })
                            })
                    {
                        continue;
                    }
                }
                let mut missing = path.to_vec();
                missing.push(CopyProjection::Storage(slot.clone()));
                if !expected.scalar() && !self.ordinary_data_type(expected) {
                    result.push(CopyConstituent {
                        parent: origin.or(parent),
                        path: missing.clone(),
                        source: None,
                        ty: expected.clone(),
                        cause: value.cause,
                        qualification: Constituent::Incomplete,
                    });
                }
                self.copy_missing_constituents(
                    expected,
                    value.cause,
                    origin.or(parent),
                    missing,
                    result,
                    &mut MissingCopyScan::default(),
                );
            }
        }
    }

    fn copy_missing_constituents(
        &self,
        ty: &Ty,
        cause: CauseId,
        parent: Option<NodeId>,
        path: Vec<CopyProjection>,
        result: &mut Vec<CopyConstituent>,
        scan: &mut MissingCopyScan,
    ) {
        // Closed recursive ordinary-data shapes can prove absence of excluded
        // constituents coinductively. This proves only eligibility: it adds no
        // graph node, alias relation, singleton fact or writable permission.
        if self.ordinary_data_type(ty) {
            result.push(CopyConstituent {
                parent,
                path,
                source: None,
                ty: ty.clone(),
                cause,
                qualification: Constituent::Ordinary,
            });
            return;
        }
        let key = self.capability_type_key(ty, &mut scan.budget);
        let admitted = scan.budget.node()
            && key.as_ref().is_some_and(|key| {
                !matches!(ty, Ty::Named(_) | Ty::Applied { .. }) || scan.budget.instance(key)
            });
        let expanded = admitted
            .then(|| self.capability_shallow_type_with_budget(ty, &mut scan.budget))
            .flatten()
            .unwrap_or(Ty::Unknown);
        let fresh = admitted
            && key
                .as_ref()
                .is_some_and(|key| scan.active.insert(key.clone()));
        let mut members = Vec::new();
        if fresh {
            match &expanded {
                Ty::Immutable(inner) => {
                    self.copy_missing_constituents(inner, cause, parent, path, result, scan);
                    if let Some(key) = key {
                        scan.active.remove(&key);
                    }
                    return;
                }
                Ty::Record(fields) | Ty::OpenRecord { fields, .. } => {
                    members.extend(fields.iter().map(|(name, (_, ty))| {
                        (CopyProjection::Storage(Slot::Field(name.clone())), ty)
                    }))
                }
                Ty::Tuple(items) => {
                    members.extend(items.iter().enumerate().map(|(index, ty)| {
                        (CopyProjection::Storage(Slot::Tuple(index as u32)), ty)
                    }))
                }
                Ty::Optional(inner) => {
                    members.push((CopyProjection::OptionPayload, inner.as_ref()))
                }
                Ty::Result(ok, error) => {
                    members.push((CopyProjection::ResultSuccess, ok.as_ref()));
                    members.push((CopyProjection::ResultError, error.as_ref()));
                }
                Ty::Array(inner) | Ty::Set(inner) => {
                    members.push((CopyProjection::Storage(Slot::AnyIndex), inner.as_ref()))
                }
                Ty::Map(key, inner) => {
                    members.push((
                        CopyProjection::Storage(Slot::Field("key".into())),
                        key.as_ref(),
                    ));
                    members.push((CopyProjection::Storage(Slot::AnyIndex), inner.as_ref()));
                }
                _ => {}
            }
        }
        if members.is_empty() || matches!(expanded, Ty::OpenRecord { .. }) {
            let qualification = if fresh {
                self.copy_type_qualification(&expanded, &mut BTreeSet::new())
            } else {
                Constituent::Incomplete
            };
            result.push(CopyConstituent {
                parent,
                path: path.clone(),
                source: None,
                ty: ty.clone(),
                cause,
                qualification,
            });
        }
        for (projection, ty) in members {
            let mut path = path.clone();
            path.push(projection);
            self.copy_missing_constituents(ty, cause, parent, path, result, scan);
        }
        if fresh && let Some(key) = key {
            scan.active.remove(&key);
        }
    }

    fn copy_shallow_qualification(&self, value: &Value, ty: &Ty) -> Constituent {
        if let Some(qualification) = self.opaque_collection_qualification(value, ty) {
            return qualification;
        }
        if self
            .constructors
            .values()
            .any(|constructor| constructor.owner == *ty)
        {
            return Constituent::Ordinary;
        }
        match ty {
            Ty::Immutable(inner) => self.copy_shallow_qualification(value, inner),
            Ty::Optional(_) | Ty::Result(_, _) => Constituent::Ordinary,
            Ty::Record(_) | Ty::Tuple(_) | Ty::Array(_) | Ty::Map(_, _) | Ty::Set(_) => {
                Constituent::Ordinary
            }
            Ty::OpenRecord { row, .. } => {
                if self.has_unresolved_row(value) {
                    Constituent::Deferred(AbstractMember::RowBinder(row.identity.clone()))
                } else {
                    Constituent::Ordinary
                }
            }
            Ty::Callable(..) => {
                if value.callables.is_empty() {
                    return Constituent::Deferred(AbstractMember::CallableEnvironment);
                }
                if value
                    .callables
                    .iter()
                    .any(|callable| matches!(callable, Callable::Builtin(_)))
                    && self
                        .heap
                        .reachable(value.origins.nodes.iter().copied())
                        .iter()
                        .any(|node| {
                            self.heap.nodes[node.0 as usize]
                                .fields
                                .keys()
                                .any(|slot| matches!(slot, Slot::Capture(_)))
                        })
                {
                    // A builtin adapter may retain a receiver even when it
                    // retains no user handlers. Its actual Capture graph,
                    // not the builtin enum/name, determines that environment.
                    return Constituent::Rejected(Rejection::RetainedEnvironment);
                }
                let mut deferred = false;
                for callable in &value.callables {
                    match callable {
                        Callable::Symbolic(..) => deferred = true,
                        Callable::Closure(id)
                            if !self.closures[*id].captures.is_empty()
                                || self.has_retained_handlers(callable) =>
                        {
                            return Constituent::Rejected(Rejection::RetainedEnvironment);
                        }
                        Callable::Named(id, _)
                            if !self.functions[*id].captures.is_empty()
                                || self.has_retained_handlers(callable) =>
                        {
                            return Constituent::Rejected(Rejection::RetainedEnvironment);
                        }
                        _ => {}
                    }
                }
                if deferred {
                    Constituent::Deferred(AbstractMember::CallableEnvironment)
                } else {
                    Constituent::EnvironmentFreeCallable
                }
            }
            _ => self.copy_type_qualification(ty, &mut BTreeSet::new()),
        }
    }

    fn copy_type_qualification(&self, ty: &Ty, _seen: &mut BTreeSet<String>) -> Constituent {
        fn visit(
            checker: &Checker,
            ty: &Ty,
            budget: &mut resources::TypeScanBudget,
            active: &mut BTreeSet<String>,
            complete: &mut BTreeMap<String, Constituent>,
        ) -> Constituent {
            if !budget.node() {
                return Constituent::Incomplete;
            }
            if checker.resource_scan_type(ty) == resources::ResourceScan::Present {
                return Constituent::Rejected(Rejection::Resource);
            }
            if checker.ordinary_data_type(ty) {
                return Constituent::Ordinary;
            }
            let Some(key) = checker.capability_type_key(ty, budget) else {
                return Constituent::Incomplete;
            };
            if active.contains(&key) {
                return Constituent::Incomplete;
            }
            if let Some(qualification) = complete.get(&key) {
                return qualification.clone();
            }
            if matches!(ty, Ty::Named(_) | Ty::Applied { .. }) && !budget.instance(&key) {
                return Constituent::Incomplete;
            }
            active.insert(key.clone());
            let Some(shape) = checker.capability_shallow_type_with_budget(ty, budget) else {
                return Constituent::Incomplete;
            };
            let qualification = if shape != *ty {
                visit(checker, &shape, budget, active, complete)
            } else {
                match ty {
                    // STD's opaque Rng is ordinary mutable sequence state and has an
                    // explicit isolated-clone contract; builtin scalar names carry no
                    // reachable resource or callable environment.
                    Ty::Named(name) if ty.scalar() || name == "Random::Rng" => {
                        Constituent::Ordinary
                    }
                    Ty::Unit
                    | Ty::Bool
                    | Ty::Int(_)
                    | Ty::Float(_)
                    | Ty::Str
                    | Ty::Bytes
                    | Ty::StaticKey(_)
                    | Ty::Never => Constituent::Ordinary,
                    Ty::Generic(binder) => {
                        Constituent::Deferred(AbstractMember::DataBinder(binder.clone()))
                    }
                    Ty::OpenRecord { row, .. } => {
                        Constituent::Deferred(AbstractMember::RowBinder(row.identity.clone()))
                    }
                    Ty::Callable(..) => Constituent::Deferred(AbstractMember::CallableEnvironment),
                    Ty::Immutable(inner)
                    | Ty::Optional(inner)
                    | Ty::Array(inner)
                    | Ty::Set(inner)
                    | Ty::Range(inner) => visit(checker, inner, budget, active, complete),
                    Ty::Result(a, b) | Ty::Map(a, b) => {
                        let a = visit(checker, a, budget, active, complete);
                        let b = visit(checker, b, budget, active, complete);
                        if a == Constituent::Ordinary && b == Constituent::Ordinary {
                            Constituent::Ordinary
                        } else if matches!(a, Constituent::Rejected(_)) {
                            a
                        } else if matches!(b, Constituent::Rejected(_)) {
                            b
                        } else if a != Constituent::Ordinary {
                            a
                        } else {
                            b
                        }
                    }
                    Ty::Tuple(items) => items
                        .iter()
                        .map(|item| visit(checker, item, budget, active, complete))
                        .find(|item| *item != Constituent::Ordinary)
                        .unwrap_or(Constituent::Ordinary),
                    Ty::Record(fields) => fields
                        .values()
                        .map(|(_, item)| visit(checker, item, budget, active, complete))
                        .find(|item| *item != Constituent::Ordinary)
                        .unwrap_or(Constituent::Ordinary),
                    _ => Constituent::Incomplete,
                }
            };
            active.remove(&key);
            complete.insert(key, qualification.clone());
            qualification
        }
        visit(
            self,
            ty,
            &mut resources::TypeScanBudget::default(),
            &mut BTreeSet::new(),
            &mut BTreeMap::new(),
        )
    }
}

#[cfg(test)]
#[path = "copy_contract_tests.rs"]
mod tests;
