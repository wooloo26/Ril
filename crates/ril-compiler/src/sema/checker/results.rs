use super::*;
#[path = "result_paths.rs"]
mod paths;
impl Checker {
    pub(super) fn result_family_closure(
        &self,
        roots: impl IntoIterator<Item = u32>,
    ) -> BTreeSet<u32> {
        let mut pending: Vec<_> = roots.into_iter().collect();
        let mut closure = BTreeSet::new();
        while let Some(id) = pending.pop() {
            if closure.insert(id)
                && let Some(members) = self.result_families.get(&id)
            {
                pending.extend(members.iter().copied());
            }
        }
        closure
    }
    fn result_duty(
        &mut self,
        owner: ScopeId,
        span: Span,
        discriminator: u32,
        cause: CauseId,
    ) -> u32 {
        let key = (owner.0, span.file.0, span.start, discriminator);
        if let Some(&id) = self.result_sites.get(&key)
            && !self.loop_result_site_can_repeat(id)
        {
            self.unsupported(
                span,
                "repeated Result production requires a multiplicity and inspection-coverage proof",
            );
            let version = self.result_inspection_versions.entry(id).or_default();
            if let Some(next) = version.checked_add(1) {
                *version = next;
            } else {
                self.unsupported(span, "Result inspection generation budget exhausted");
            }
            return id;
        }
        let id = self.result_duties.len() as u32;
        self.result_sites.insert(key, id);
        self.result_duties.push(ResultDuty {
            id,
            owner,
            creation_owner: owner,
            span,
            cause,
            inspected: false,
            returned: false,
            abnormal: false,
            covered: false,
        });
        id
    }
    pub(super) fn make_result(
        &mut self,
        success: bool,
        payload: Value,
        span: Span,
        owner: ScopeId,
    ) -> Value {
        let cause = self.cause(
            CauseKind::Source,
            span,
            if success {
                "produced Ok Result"
            } else {
                "produced Err Result"
            },
            [payload.cause],
        );
        let id = self.result_duty(owner, span, 0, cause);
        Self::result_value(success, payload, cause, id)
    }
    fn result_value(success: bool, payload: Value, cause: CauseId, id: u32) -> Value {
        let ty = if success {
            Ty::Result(Box::new(payload.ty.clone()), Box::new(Ty::Unknown))
        } else {
            Ty::Result(Box::new(Ty::Unknown), Box::new(payload.ty.clone()))
        };
        let mut value = Self::result_carrier(payload.clone(), ty, cause, id);
        value.result_success = success.then(|| Box::new(payload.clone()));
        value.result_error = (!success).then(|| Box::new(payload.clone()));
        value.result_payload = Some(Box::new(payload));
        value.result_tag = Some(success);
        value
    }

    /// Both a known tag and an incoming union use the same carrier operation.
    /// Payload-specific interfaces do not become interfaces of the Result.
    pub(super) fn result_carrier(mut value: Value, ty: Ty, cause: CauseId, id: u32) -> Value {
        value.source_type_witness = None;
        value.condition_inspections = Default::default();
        value.ty = ty;
        value.result_success = None;
        value.result_error = None;
        value.unsuffixed_numeric = false;
        value.literal_number = false;
        value.callables.clear();
        value.signature = None;
        value.callable_bounds.clear();
        value.callable_returns.clear();
        value.static_coordinate = None;
        value.option_payload = None;
        value.option_tag = None;
        value.option_identity = None;
        value.variant_payload = None;
        value.variant_witnesses.clear();
        value.variant_tag = None;
        value.result_payload = None;
        value.constant = None;
        value.result_tag = None;
        value.outer_results = [id].into();
        value.must_outer_results = [id].into();
        value.results.insert(id);
        value.must_results.insert(id);
        value.cause = cause;
        value
    }
    pub(super) fn checked_static_result(
        &mut self,
        success: bool,
        payload: Value,
        receipt: &crate::static_eval::results::Receipt,
    ) -> Value {
        let mut cause = self.cause(
            CauseKind::Source,
            receipt.production,
            format!(
                "static Result producer {} received from the verified constant pool",
                receipt.producer.0
            ),
            [payload.cause],
        );
        for &span in &receipt.inspections {
            cause = self.cause(
                CauseKind::Source,
                span,
                "reached static Result tag inspection of this producer",
                [cause],
            );
        }
        assert!(
            !receipt.inspections.is_empty(),
            "static Result receipt must contain an actual inspection"
        );
        let id = self.result_duties.len() as u32;
        self.result_duties.push(ResultDuty {
            id,
            owner: ScopeId(0),
            creation_owner: ScopeId(0),
            span: receipt.production,
            cause,
            inspected: true,
            returned: false,
            abnormal: false,
            covered: true,
        });
        Self::result_value(success, payload, cause, id)
    }
    pub(super) fn inspect_result(&mut self, value: &Value) {
        if let Some(span) = self.pending_copy_dependencies(value).iter().find_map(|id| {
            self.copy_boundaries
                .get(id.0 as usize)
                .map(|boundary| boundary.span)
        }) {
            self.require_copy_dependencies(
                value,
                span,
                "Result inspection of conditional copy output",
            );
            return;
        }
        if self.loop_depth > 0
            && !value.outer_results.is_empty()
            && !self.loop_result_inspection_allowed(value)
        {
            self.unsupported(
                self.result_duties[*value.outer_results.first().unwrap() as usize].span,
                "Result inspection inside a loop requires full traversal coverage",
            );
        }
        for id in self.result_family_closure(value.must_outer_results.iter().copied()) {
            self.result_duties[id as usize].inspected = true;
            self.result_duties[id as usize].covered = true;
        }
        self.channel_inspect_results(value);
    }
    pub(super) fn result_payload(
        &mut self,
        value: &Value,
        success: bool,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let expected = match self.expanded(&value.ty, &mut BTreeSet::new()) {
            Ty::Result(ok, error) => {
                if success {
                    *ok
                } else {
                    *error
                }
            }
            _ => {
                self.error(
                    "E0301",
                    span,
                    "Result constructor pattern requires a Result",
                    [value.cause],
                );
                return Value::scalar(Ty::Unknown, None, value.cause);
            }
        };
        let witness = if success {
            &value.result_success
        } else {
            &value.result_error
        };
        let mut payload = if let Some(payload) = witness {
            *payload.clone()
        } else if value.result_tag == Some(success) {
            value
                .result_payload
                .as_ref()
                .map(|payload| *payload.clone())
                .unwrap_or_else(|| {
                    self.formal_value(expected.clone(), span.start, span, &mut BTreeSet::new())
                })
        } else {
            let mut payload =
                self.formal_value(expected.clone(), span.start, span, &mut BTreeSet::new());
            if value.result_tag.is_none() {
                payload.origins = value.origins.clone();
                payload.results = value
                    .results
                    .difference(&value.outer_results)
                    .copied()
                    .collect();
                payload.must_results = value
                    .must_results
                    .difference(&value.outer_results)
                    .copied()
                    .collect();
            }
            // A known opposite tag has no actual payload. Type-check its
            // excluded path with the declared symbolic value, without lending
            // the present tag's storage or inspection duties to that path.
            payload
        };
        if expected != Ty::Unknown {
            payload.ty = expected;
        }
        self.project_result_source_type(value, success, &mut payload);
        payload.permission = payload.permission.meet(value.permission);
        payload.construction &= value.construction;
        payload.publication = if payload.publication == Publication::Immutable
            || value.publication == Publication::Immutable
        {
            Publication::Immutable
        } else if value.publication == Publication::Live {
            Publication::Live
        } else {
            payload.publication
        };
        payload.sources = value.sources.clone();
        payload.participants = value.participants.clone();
        payload.marker = value.marker || (value.construction && payload.marker);
        payload.retention_result =
            value.retention_result || (value.construction && payload.retention_result);
        payload.through_return |= value.through_return;
        if payload.ty.scalar() {
            if !value.sources.is_empty() || value.through_return {
                payload.unsuffixed_numeric = false;
                payload.literal_number = false;
            }
            payload.origins = Origins::default();
            payload.participants.clear();
            payload.temporary = false;
            payload.scoped.clear();
        }
        payload
            .callback_parameters
            .extend(&value.callback_parameters);
        let _ = frame;
        payload
    }
    pub(super) fn return_results(&mut self, value: &Value) {
        for id in self.result_family_closure(value.must_results.iter().copied()) {
            if self.channel_known_producer(id) {
                continue;
            }
            self.result_duties[id as usize].returned = true;
            self.result_duties[id as usize].covered = true;
        }
    }
    /// Evidence belongs to this invocation and this evaluated value. A later
    /// branch inspection cannot repair a return that was already uncovered.
    pub(super) fn record_result_return(&mut self, owner: ScopeId, value: &Value) -> bool {
        self.channel_return_at(owner, value);
        self.channel_return_exit(owner, value);
        let returned = self
            .result_family_closure(value.must_results.iter().copied())
            .into_iter()
            .filter(|id| !self.channel_known_producer(*id))
            .collect::<BTreeSet<_>>();
        let covered = self.result_duties.iter().all(|duty| {
            if self.channel_known_producer(duty.id) {
                self.channel_can_finish(duty.id, owner)
            } else {
                duty.owner != owner || duty.covered || duty.abnormal || returned.contains(&duty.id)
            }
        });
        self.result_return_checks
            .entry((owner.0, value.cause.0))
            .and_modify(|old| *old &= covered)
            .or_insert(covered);
        covered
    }
    pub(super) fn result_return_covered(&self, owner: ScopeId, value: &Value) -> bool {
        self.result_return_checks.get(&(owner.0, value.cause.0)) == Some(&true)
    }
    pub(super) fn record_result_control_exit(
        &mut self,
        owner: ScopeId,
        value: &Value,
        span: Span,
        returns: bool,
    ) {
        let covered = if returns {
            self.record_result_return(owner, value)
        } else {
            let start = self
                .result_loop_starts
                .last()
                .copied()
                .unwrap_or(self.result_duties.len());
            self.result_duties[start..]
                .iter()
                .all(|duty| duty.owner != owner || duty.inspected || duty.abnormal)
        };
        self.result_exit_checks
            .entry((owner.0, span.file.0, span.start, span.end))
            .and_modify(|old| *old &= covered)
            .or_insert(covered);
    }
    pub(super) fn finish_results(&mut self, owner: ScopeId, implicit: &Value) {
        self.channel_finish_callable(owner, implicit);
        self.return_results(implicit);
        if implicit.abnormal {
            for duty in &mut self.result_duties {
                if duty.owner == owner {
                    duty.abnormal = true;
                }
            }
        }
        let unhandled: Vec<_> = self
            .result_duties
            .iter()
            .filter(|duty| {
                if self.channel_known_producer(duty.id) {
                    self.channel_obligations_complete() && !self.channel_can_finish(duty.id, owner)
                } else {
                    duty.owner == owner && !duty.covered && !duty.abnormal
                }
            })
            .cloned()
            .collect();
        for duty in unhandled {
            self.error(
                "E0720",
                duty.span,
                "produced Result was neither inspected nor returned with its obligation",
                [duty.cause],
            );
        }
    }
    /// A returned outer Result is one dynamic event even when mutually
    /// exclusive return sites have distinct producer IDs. Collapse only a
    /// confined family born in this invocation; caller-owned aliases retain
    /// their original duties and are never absorbed by this summary.
    pub(super) fn export_conditional_result_family(
        &mut self,
        value: &mut Value,
        from: ScopeId,
        span: Span,
    ) {
        if !matches!(
            self.expanded(&value.ty, &mut BTreeSet::new()),
            Ty::Result(..)
        ) || value.outer_results.is_empty()
            || value.outer_results == value.must_outer_results
        {
            return;
        }
        let family = value.outer_results.clone();
        let pending: BTreeSet<_> = family
            .iter()
            .copied()
            .filter(|id| !self.result_duties[*id as usize].inspected)
            .collect();
        if pending
            .iter()
            .any(|id| self.result_duties[*id as usize].owner != from)
        {
            self.unsupported(
                span,
                "conditional returned Result aliases require path-indexed caller ownership",
            );
            return;
        }
        let outside: Vec<_> = self
            .bindings
            .iter()
            .filter(|binding| binding.alive && binding.owner != from)
            .collect();
        let reachable = self.heap.reachable(outside.iter().flat_map(|binding| {
            binding
                .value
                .origins
                .nodes
                .iter()
                .copied()
                .chain(binding.cell)
        }));
        if outside
            .iter()
            .any(|binding| !binding.value.results.is_disjoint(&pending))
            || self.fields.iter().any(|((node, _), field)| {
                reachable.contains(node) && !field.results.is_disjoint(&pending)
            })
        {
            self.unsupported(
                span,
                "a conditional returned Result family has a surviving independent alias",
            );
            return;
        }
        let inspected = family
            .iter()
            .all(|id| self.result_duties[*id as usize].inspected);
        let id = self.result_duty(from, span, u32::MAX, value.cause);
        let duty = &mut self.result_duties[id as usize];
        duty.inspected = inspected;
        duty.covered = inspected;
        self.result_families.insert(id, family.clone());
        self.channel_record_aliases([(id, family.clone())].into(), from, value.cause, span);
        value.results.retain(|old| !family.contains(old));
        value.must_results.retain(|old| !family.contains(old));
        value.results.insert(id);
        value.must_results.insert(id);
        value.outer_results = [id].into();
        value.must_outer_results = [id].into();
    }
    pub(super) fn transfer_results(&mut self, value: &Value, from: ScopeId, to: ScopeId) {
        self.channel_record_result_transfer(value, from, to);
        self.channel_transfer_results(value, from, to);
        for id in self.result_family_closure(value.results.iter().copied()) {
            let duty = &mut self.result_duties[id as usize];
            if duty.owner == from {
                duty.owner = to;
            }
            duty.returned = false;
            duty.covered = duty.inspected;
        }
    }
    pub(super) fn copy_result_duties(
        &mut self,
        value: &mut Value,
        span: Span,
        owner: ScopeId,
    ) -> BTreeMap<u32, u32> {
        let mut map = BTreeMap::new();
        let closure = self.result_family_closure(value.results.iter().copied());
        for old in &closure {
            let cause = self.result_duties[*old as usize].cause;
            let id = self.result_duty(owner, span, old.saturating_add(1), cause);
            map.insert(*old, id);
        }
        for old in &closure {
            if let Some(members) = self.result_families.get(old).cloned() {
                self.result_families
                    .insert(map[old], members.iter().map(|member| map[member]).collect());
            }
        }
        self.channel_copy_results(value, &map, owner, span);
        remap_results(value, &map);
        map
    }
    pub(super) fn formal_result(&mut self, ty: Ty, span: Span) -> Value {
        let cause = self.cause(
            CauseKind::Source,
            span,
            "symbolic Result from an outside producer",
            [],
        );
        let id = self.result_duties.len() as u32;
        self.result_duties.push(ResultDuty {
            id,
            owner: ScopeId(u32::MAX),
            creation_owner: ScopeId(u32::MAX),
            span,
            cause,
            inspected: false,
            returned: false,
            abnormal: false,
            covered: false,
        });
        let mut value = Value::scalar(ty, None, cause);
        value.results.insert(id);
        value.outer_results.insert(id);
        value.must_outer_results.insert(id);
        value.must_results.insert(id);
        value
    }
    pub(super) fn produced_symbolic_results(
        &mut self,
        value: &mut Value,
        span: Span,
        owner: ScopeId,
    ) {
        if self.has_unresolved_row(value) {
            self.unsupported(span, "an unknown producer's open row requires complete resource and Result production coverage");
        }
        if !value.results.is_empty() {
            self.copy_result_duties(value, span, owner);
        }
    }
    pub(super) fn merge_result_paths(
        &mut self,
        before: &[ResultDuty],
        left_state: &[ResultDuty],
        left: &Value,
        right: &Value,
        mut joined: Value,
    ) -> Value {
        let right_state = self.result_duties.clone();
        for (index, initial) in before.iter().enumerate() {
            let a = &left_state[index];
            let b = &right_state[index];
            let (inspected, returned, abnormal) = if left.abnormal {
                (b.inspected, b.returned, b.abnormal)
            } else if right.abnormal {
                (a.inspected, a.returned, a.abnormal)
            } else {
                (
                    a.inspected && b.inspected,
                    a.returned && b.returned,
                    a.abnormal && b.abnormal,
                )
            };
            let _ = initial;
            self.result_duties[index].inspected = inspected;
            self.result_duties[index].returned = returned;
            self.result_duties[index].abnormal = abnormal;
            self.result_duties[index].covered =
                (a.covered || left.abnormal) && (b.covered || right.abnormal);
        }
        for duty in &mut self.result_duties[before.len()..left_state.len()] {
            let old = &left_state[duty.id as usize];
            duty.inspected = old.inspected;
            duty.returned = old.returned;
            duty.covered = old.covered;
            duty.abnormal = old.abnormal || left.abnormal;
        }
        if right.abnormal {
            for duty in &mut self.result_duties[left_state.len()..] {
                duty.abnormal = true;
            }
        }
        joined.must_results = joined
            .results
            .iter()
            .copied()
            .filter(|id| {
                let index = *id as usize;
                if index >= before.len() {
                    return left.must_results.contains(id) || right.must_results.contains(id);
                }
                let a = &left_state[index];
                let b = &right_state[index];
                (left.must_results.contains(id) || a.covered || left.abnormal)
                    && (right.must_results.contains(id) || b.covered || right.abnormal)
            })
            .collect();
        joined.must_outer_results = joined
            .outer_results
            .iter()
            .copied()
            .filter(|id| {
                if *id as usize >= before.len() {
                    left.must_outer_results.contains(id) || right.must_outer_results.contains(id)
                } else {
                    left.must_outer_results.contains(id) && right.must_outer_results.contains(id)
                }
            })
            .collect();
        joined
    }
    pub(super) fn discharge_absent_results(&mut self, value: &Value, span: Span) {
        for id in &value.must_results {
            if self.channel_known_producer(*id) {
                continue;
            }
            self.result_duties[*id as usize].covered = true;
        }
        self.cause(CauseKind::BranchJoin,span,"narrowed constructor contains no Result payload; remaining carried obligations are absent or already discharged",[value.cause]);
    }
}
pub(super) fn remap_results(value: &mut Value, map: &BTreeMap<u32, u32>) {
    value.results = value
        .results
        .iter()
        .map(|id| *map.get(id).unwrap_or(id))
        .collect();
    value.outer_results = value
        .outer_results
        .iter()
        .map(|id| *map.get(id).unwrap_or(id))
        .collect();
    value.must_outer_results = value
        .must_outer_results
        .iter()
        .map(|id| *map.get(id).unwrap_or(id))
        .collect();
    value.must_results = value
        .must_results
        .iter()
        .map(|id| *map.get(id).unwrap_or(id))
        .collect();
    for payload in [
        &mut value.result_payload,
        &mut value.result_success,
        &mut value.result_error,
    ]
    .into_iter()
    .flatten()
    {
        remap_results(payload, map);
    }
    if let Some(payload) = &mut value.option_payload {
        remap_results(payload, map);
    }
    if let Some(payload) = &mut value.variant_payload {
        remap_results(payload, map);
    }
    for payload in value.variant_witnesses.values_mut() {
        remap_results(payload, map);
    }
}
