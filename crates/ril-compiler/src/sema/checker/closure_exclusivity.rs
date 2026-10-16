use super::super::closure_exclusivity::{self as domain, *};
use super::*;
impl Checker {
    pub(super) fn record_closure_discard(
        &mut self,
        value: &Value,
        created_start: usize,
        named_start: usize,
        frame: &Frame,
        span: Span,
    ) {
        let [Callable::Closure(id)] = value.callables.as_slice() else {
            return;
        };
        if *id < created_start
            || !value.callback_parameters.is_empty()
            || self
                .graph_callables(value)
                .iter()
                .any(|callable| matches!(callable, Callable::Symbolic(..)))
            || self.closure_invocation_stack.last().is_some_and(|id| {
                self.closure_invocations[id.0 as usize].probe
                    || self.closure_invocations[id.0 as usize].budget_validation
            })
        {
            return;
        }
        self.closure_discards.push(ClosureDiscard {
            id: ClosureDiscardId(self.closure_discards.len() as u32),
            closure: ClosureObjectId(*id as u32),
            created_start: ClosureObjectId(created_start as u32),
            created_end: ClosureObjectId(self.closures.len() as u32),
            named_start: super::super::copy_templates::InstanceId(named_start as u32),
            named_end: super::super::copy_templates::InstanceId(self.copy_invocations.len() as u32),
            owner: frame.callable_owner,
            named: self.copy_invocation_stack.last().copied(),
            invocation: self.closure_invocation_stack.last().copied(),
            span,
            allocation_epoch: self.recency_moves.len(),
            value: self.copy_value_snapshot(value),
        });
    }
    pub(super) fn record_closure_exposure(
        &mut self,
        value: &Value,
        frame: &Frame,
        kind: ExposureKind,
        span: Span,
    ) {
        for callable in self.graph_callables(value) {
            if let Callable::Closure(id) = callable {
                self.closure_exposures.push(ClosureExposure {
                    closure: ClosureObjectId(id as u32),
                    kind,
                    owner: frame.callable_owner,
                    named: self.copy_invocation_stack.last().copied(),
                    invocation: self.closure_invocation_stack.last().copied(),
                    span,
                });
            }
        }
    }
    pub(super) fn record_closure_exclusivity(
        &mut self,
        closure: usize,
        frame: &Frame,
        span: Span,
        probe: bool,
    ) {
        let Some(invocation) = self.closure_invocation_stack.last().copied() else {
            self.unsupported(
                span,
                "closure exclusivity check has no actual invocation identity",
            );
            return;
        };
        let accesses = self.current_accesses(&frame.obligations.accesses);
        let mut queried = BTreeSet::new();
        let requirements = domain::requirements(&accesses, |a, b| {
            for left in &a.nodes {
                for right in &b.nodes {
                    queried.insert((*left.min(right), *left.max(right)));
                }
            }
            self.origins_disjoint(a, b)
        });
        let roots: BTreeSet<_> = accesses
            .iter()
            .flat_map(|access| access.origins.nodes.iter().copied())
            .collect();
        let nodes: Vec<_> = roots
            .iter()
            .map(|node| (*node, self.heap.nodes[node.0 as usize].clone()))
            .collect();
        let relations = queried
            .into_iter()
            .map(|(a, b)| (a, b, self.heap.relation(a, b)))
            .collect();
        let resolution = if requirements.is_empty() {
            Resolution::Proved
        } else if probe {
            Resolution::Pending
        } else {
            Resolution::Rejected
        };
        let info = &self.closures[closure];
        self.closure_exclusivity_checks
            .push(ClosureExclusivityCheck {
                id: ClosureCheckId(self.closure_exclusivity_checks.len() as u32),
                closure: ClosureObjectId(closure as u32),
                site: info.site,
                invocation,
                creation_named: info.creation_invocation,
                creation_closure: info.creation_closure,
                creation_default: info.creation_default,
                probe,
                body_complete: !frame.obligations.symbolic,
                span,
                allocation_epoch: self.recency_moves.len(),
                accesses,
                nodes,
                relations,
                requirements,
                resolution,
            });
        if !probe {
            self.check_exclusivity(&frame.obligations.accesses, span);
        }
    }
    pub(super) fn finish_closure_exclusivity(&mut self) {
        let pending: BTreeSet<_> = self
            .closure_exclusivity_checks
            .iter()
            .filter(|check| check.resolution == Resolution::Pending)
            .map(|check| check.closure)
            .collect();
        if pending.is_empty() {
            return;
        }
        let result = domain::close(&CoverageInput {
            final_epoch: self.recency_moves.len(),
            closures: &self.closures,
            sites: &self.closure_sites,
            functions: &self.functions,
            named: &self.copy_invocations,
            calls: &self.closure_invocations,
            checks: &self.closure_exclusivity_checks,
            exposures: &self.closure_exposures,
            discards: &self.closure_discards,
            references: &self.copy_references,
            events: &self.copy_call_events,
        });
        let certificate = match result {
            Ok(certificate) => certificate,
            Err(reason) => {
                let object = *pending.first().unwrap();
                self.unsupported(self.closures[object.0 as usize].body.span, format!("conditional closure exclusivity requires complete actual-object invocation coverage: {reason:?}"));
                return;
            }
        };
        for check in &mut self.closure_exclusivity_checks {
            if check.resolution != Resolution::Pending {
                continue;
            }
            let calls = certificate
                .objects
                .get(&check.closure)
                .cloned()
                .or_else(|| {
                    certificate.templates.get(&check.closure).map(|objects| {
                        objects
                            .iter()
                            .flat_map(|object| certificate.objects[object].iter().copied())
                            .collect()
                    })
                });
            if let Some(calls) = calls {
                let objects = certificate
                    .templates
                    .get(&check.closure)
                    .cloned()
                    .unwrap_or_else(|| [check.closure].into());
                let discards = objects
                    .iter()
                    .filter_map(|object| certificate.discarded.get(object).copied())
                    .collect();
                check.resolution = Resolution::Discharged { calls, discards };
            }
        }
        self.closure_exclusivity_certificate = Some(certificate);
    }
}
