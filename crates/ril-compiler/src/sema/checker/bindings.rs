use super::*;
use crate::sema::storage_sources::{StorageDestination, StorageObservation};

/// Original binder identity is installed at birth, before capture publication.
/// A diagnostic location alone never identifies a source binder.
pub(super) struct BindingSite {
    span: Span,
    declaration: Option<ril_compiler_core::ids::StmtId>,
    pattern: Option<ril_compiler_core::ids::PatternId>,
    birth: Option<crate::sema::application_effect::OccurrenceIdentity>,
}

impl BindingSite {
    pub(super) fn declaration(
        span: Span,
        declaration: Option<ril_compiler_core::ids::StmtId>,
    ) -> Self {
        Self {
            span,
            declaration,
            pattern: None,
            birth: None,
        }
    }
    pub(super) fn original(span: Span, pattern: ril_compiler_core::ids::PatternId) -> Self {
        Self {
            span,
            declaration: None,
            pattern: Some(pattern),
            birth: None,
        }
    }
    pub(super) fn at(
        mut self,
        birth: Option<crate::sema::application_effect::OccurrenceIdentity>,
    ) -> Self {
        self.birth = birth;
        self
    }
}

impl From<Span> for BindingSite {
    fn from(span: Span) -> Self {
        Self {
            span,
            declaration: None,
            pattern: None,
            birth: None,
        }
    }
}

impl From<&Pattern> for BindingSite {
    fn from(pattern: &Pattern) -> Self {
        Self {
            span: pattern.span,
            declaration: None,
            pattern: pattern.hir_id,
            birth: None,
        }
    }
}

impl Checker {
    pub(super) fn bind_parameter_packet(
        &mut self,
        pattern: &Pattern,
        mode: BindingMode,
        mut packet: EvaluatedValue,
        frame: &mut Frame,
    ) -> Result<(), crate::sema::source_types::SourceTypesError> {
        self.prepare_evaluation_packet(&mut packet, pattern.span)?;
        let birth = packet.identity;
        self.bind_pattern_from(pattern, mode, packet.value, frame, true, birth);
        Ok(())
    }
    /// Every local receiver, including a resumed answer, installs the same
    /// declaration view and records the original initializer occurrence.
    pub(super) fn receive_binding(
        &mut self,
        binding: &Binding,
        mut value: Value,
        initializer: Option<StorageObservation>,
        source_target: Option<&crate::sema::source_reception::Target>,
        source_valid: bool,
        frame: &mut Frame,
    ) -> Value {
        let span = binding.pattern.span;
        let birth = initializer.and_then(|observed| {
            self.application_effect
                .evaluations
                .get(observed.expression)
                .and_then(|record| record.identity)
        });
        let guarded = binding.fallback.is_some()
            || matches!(
                binding.pattern.kind,
                PatternKind::Constructor { .. }
                    | PatternKind::Literal(_)
                    | PatternKind::Alternative(_)
                    | PatternKind::Value(_)
            );
        let prepared_storage = initializer.map(|initializer| {
            self.prepare_storage_binding_source(binding, source_target, initializer, frame)
        });
        if let Some(syntax) = &binding.ty {
            let Some(target) = source_target else {
                self.unsupported(
                    span,
                    "annotated binding lost its frozen receiving environment",
                );
                return self.unit(span);
            };
            self.with_typing_environment(&target.environment, |checker| {
                let recency = checker.recency_moves.len();
                if source_valid {
                    checker.ascribe_signature(&mut value, syntax);
                    checker.transport_value_since(&mut value, recency);
                    let shape_recency = checker.recency_moves.len();
                    checker.check_storage_shape(&value, syntax, frame);
                    checker.transport_value_since(&mut value, shape_recency);
                }
                let ty = checker.ty(syntax);
                if source_valid {
                    checker.constrain_collection_type(&value, &ty, binding.value.span);
                }
                checker.require_type(&value, &ty, binding.value.span);
                if source_valid {
                    value.ty = ty;
                    value.requires_inference = false;
                }
            });
        }
        if value.requires_inference
            || !self.pending_result_binders(&value).is_empty()
            || self.unresolved_empty_map_keys(&value)
        {
            self.error(
                "E0344",
                binding.value.span,
                "generic result type is not determined by arguments or a required context",
                [value.cause],
            );
        }
        if guarded {
            let binding_start = self.bindings.len();
            let result = self.check_guarded_binding(binding, value, span, frame, birth);
            if source_valid
                && let (Some(initializer), Some(prepared)) =
                    (initializer, prepared_storage.as_ref())
            {
                self.record_storage_binding_sources(
                    binding,
                    prepared,
                    initializer,
                    binding_start,
                    frame,
                );
            }
            return result;
        }
        let binding_start = self.bindings.len();
        self.bind_pattern_from(&binding.pattern, binding.mode, value, frame, false, birth);
        if source_valid
            && let (Some(initializer), Some(prepared)) = (initializer, prepared_storage.as_ref())
        {
            self.record_storage_binding_sources(
                binding,
                prepared,
                initializer,
                binding_start,
                frame,
            );
        }
        self.unit(span)
    }
    pub(super) fn bind_pattern(
        &mut self,
        pattern: &Pattern,
        mode: BindingMode,
        value: Value,
        frame: &mut Frame,
        parameter: bool,
    ) {
        self.bind_pattern_from(pattern, mode, value, frame, parameter, None);
    }
    fn bind_pattern_from(
        &mut self,
        pattern: &Pattern,
        mode: BindingMode,
        value: Value,
        frame: &mut Frame,
        parameter: bool,
        birth: Option<crate::sema::application_effect::OccurrenceIdentity>,
    ) {
        if !self.check_pattern_binder_uniqueness(pattern) {
            return;
        }
        match &pattern.kind {
            PatternKind::Name(name) => {
                self.bind_name(
                    name,
                    mode,
                    value,
                    BindingSite::from(pattern).at(birth),
                    frame,
                    parameter,
                );
            }
            PatternKind::Wildcard => {}
            PatternKind::Mode { mode, pattern } => {
                self.bind_pattern_from(pattern, *mode, value, frame, parameter, birth)
            }
            PatternKind::Tuple(items) => {
                for (i, pattern) in items.iter().enumerate() {
                    let child =
                        self.project(&value, Slot::Tuple(i as u32), pattern.span, frame, false);
                    self.bind_pattern_from(pattern, mode, child, frame, parameter, birth);
                }
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                for field in fields {
                    let mut child = self.project(
                        &value,
                        Slot::Field(field.name.clone()),
                        field.span,
                        frame,
                        false,
                    );
                    let child_mutable = mode.is_mutable()
                        || matches!(field.pattern.kind,PatternKind::Mode{mode,..}if mode.is_mutable());
                    if child_mutable && child.permission == Permission::Read {
                        self.error(
                            "E0521",
                            field.span,
                            "destructuring cannot acquire write authority",
                            [child.cause],
                        );
                    }
                    child.marker |= value.marker;
                    self.bind_pattern_from(&field.pattern, mode, child, frame, parameter, birth);
                }
                if let Some(name) = rest_binding
                    && let Some(rest) = self.record_rest_value(&value, fields, pattern.span, frame)
                {
                    self.bind_name(
                        name,
                        mode,
                        rest,
                        BindingSite::from(pattern).at(birth),
                        frame,
                        parameter,
                    );
                }
            }
            _ => self.unsupported(pattern.span, "refutable or computed pattern verification"),
        }
    }
    fn record_rest_value(
        &mut self,
        source: &Value,
        extracted: &[PatternField],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        if self.foreign_opaque_type(&source.ty)
            || matches!(&source.ty, Ty::Named(name) if self.types.get(name).is_some_and(|declaration| declaration.opaque))
        {
            self.error(
                "E0907",
                span,
                "opaque storage cannot be structurally inspected",
                [source.cause],
            );
            return None;
        }
        let Some(row) = self.value_row(&source.ty) else {
            self.unsupported(span, "record-rest binding requires an exact record shape");
            return None;
        };
        let labels = extracted.iter().map(|field| field.name.clone()).collect();
        let Some(remainder) = self
            .row_solver()
            .remove(&row, &labels)
            .ok()
            .and_then(|plan| plan.exact())
        else {
            self.unsupported(
                span,
                "record-rest removal requires exact membership in the known fields",
            );
            return None;
        };
        let fields = remainder.fields.clone();
        let tail = if let crate::sema::model::rows::RowTail::Open(row) = &remainder.tail {
            Some((
                row.identity.clone(),
                self.carried_row_tail(source, row, span)?,
            ))
        } else {
            None
        };
        let node = self.allocate_owned(span, 0, frame.owner);
        let mut rest = Value::reference(
            Self::row_type(remainder),
            node,
            self.heap.nodes[node.0 as usize].cause,
        );
        rest.marker = source.marker;
        for name in fields.keys() {
            let mut child = self.project(source, Slot::Field(name.clone()), span, frame, true);
            child.marker |= source.marker;
            rest.results.extend(&child.results);
            rest.must_results.extend(&child.must_results);
            rest.callback_parameters.extend(&child.callback_parameters);
            rest.scoped.extend(&child.scoped);
            rest.mutable_environment |= child.mutable_environment;
            rest.observer_environment |= child.observer_environment;
            rest.internal_aliases |= child.permission == Permission::Write
                && !child.construction
                && self.has_writer(&child)
                && !child.marker;
            self.store_field(node, Slot::Field(name.clone()), child);
        }
        if let Some((identity, child)) = tail {
            rest.results.extend(&child.results);
            rest.must_results.extend(&child.must_results);
            rest.callback_parameters.extend(&child.callback_parameters);
            rest.scoped.extend(&child.scoped);
            rest.mutable_environment |= child.mutable_environment;
            rest.observer_environment |= child.observer_environment;
            rest.internal_aliases |= child.permission == Permission::Write
                && !child.construction
                && self.has_writer(&child)
                && !child.marker;
            self.store_field(node, Slot::RowTail(identity), child);
        }
        Some(rest)
    }
    pub(super) fn bind_name(
        &mut self,
        name: &str,
        mode: BindingMode,
        mut value: Value,
        site: impl Into<BindingSite>,
        frame: &mut Frame,
        parameter: bool,
    ) -> BindingId {
        let BindingSite {
            span,
            declaration,
            pattern,
            birth,
        } = site.into();
        if name == "_" {
            return usize::MAX;
        }
        if frame.env.get(name).is_some_and(|id| {
            self.bindings[*id].owner == frame.owner
                && self.bindings[*id].lexical_scope
                    == self.block_boundaries.last().copied().unwrap_or(u32::MAX)
                && self.bindings[*id].alive
        }) {
            self.error("E0203", span, format!("duplicate binding {name}"), []);
        }
        self.constrain_collection_type(&value, &value.ty, span);
        let conditional_read =
            !parameter && mode == BindingMode::Let && self.forwards_conditional_copy(&value, frame);
        if !parameter
            && !conditional_read
            && (mode.is_mutable() || matches!(mode, BindingMode::Let | BindingMode::Scoped))
        {
            self.require_copy_dependencies(
                &value,
                span,
                "receiving copy output with writable or immutable authority",
            );
        }
        if conditional_read {
            // A lexical name may forward the still-conditional value. It does
            // not publish the placeholder as immutable or grant fresh writes;
            // every concrete invocation rechecks the actual reception.
            value.permission = Permission::Read;
            value.construction = false;
            value.stable = false;
        } else if mode.is_mutable() {
            if value.ty.scalar()
                || self.representation_graph_type(&value.ty).scalar()
                || self.constructor_scalar_type(&value.ty) == Some(true)
            {
                self.error(
                    if parameter { "E0401" } else { "E0402" },
                    span,
                    "scalar mutation requires plain var",
                    [value.cause],
                );
            }
            if value.permission != Permission::Write && !parameter {
                self.error(
                    if value.through_return {
                        "E0528"
                    } else {
                        "E0520"
                    },
                    span,
                    "read-only path cannot acquire write authority",
                    [value.cause],
                );
            }
            if !parameter
                && !value.marker
                && !value.retention_result
                && ((!value.construction && self.has_writer(&value)) || value.internal_aliases)
            {
                self.error(
                    "E0510",
                    span,
                    "new local writable sharing requires ^mut",
                    [value.cause],
                );
            }
            value.publication = Publication::Live;
            value.construction = false;
            value.stable = !mode.is_reassignable();
        } else if matches!(mode, BindingMode::Let | BindingMode::Scoped) && !parameter {
            self.check_deep_uncertainty(&value, span);
            if !self.concurrent_let_resource(&value)
                && (self.has_writer(&value)
                    || value.mutable_environment
                    || value.observer_environment
                    || (value.construction && !self.construction_can_publish(&value))
                    || (value.publication == Publication::Live
                        && !value.construction
                        && !value.origins.nodes.is_empty()))
            {
                self.error(
                    "E0535",
                    span,
                    "immutable binding contains live storage or a surviving writer",
                    [value.cause],
                );
            }
            value.permission = Permission::Read;
            value.publication = Publication::Immutable;
            value.construction = false;
        } else {
            if mode == BindingMode::View
                && (!value.stable || value.publication == Publication::Immutable)
            {
                self.error(
                    "E0531",
                    span,
                    "live view requires a stable pinned live origin",
                    [value.cause],
                );
            }
            value.permission = Permission::Read;
            value.construction = false;
            if mode.is_reassignable() {
                value.stable = false;
            }
        }
        let id = self.bindings.len();
        if matches!(mode, BindingMode::Scoped | BindingMode::ScopedMut) {
            value.scoped.insert(id);
        }
        let root = RootId(id as u32);
        value.marker = false;
        value.retention_result = false;
        value.unsuffixed_numeric = false;
        value.static_coordinate = None;
        let cell = if mode.is_reassignable() {
            let node = self.allocate_owned(span, 0x8000_0000, frame.owner);
            self.store_field(node, Slot::Field("value".into()), value.clone());
            self.heap.nodes[node.0 as usize].writable_roots.insert(root);
            Some(node)
        } else {
            None
        };
        if mode.is_mutable() {
            for node in self.writable_nodes(&value) {
                self.heap.nodes[node.0 as usize].writable_roots.insert(root);
            }
        }
        value.sources = [id].into();
        if parameter
            && (!value.callables.is_empty()
                || self
                    .heap
                    .reachable(value.origins.nodes.iter().copied())
                    .iter()
                    .any(|node| {
                        self.fields.iter().any(|((parent, _), child)| {
                            parent == node && !child.callables.is_empty()
                        })
                    }))
        {
            value.callback_parameters.insert(id);
        }
        if value.participants.is_empty() {
            value.participants.insert(Participant::Root(root));
        }
        let typing_environment = if parameter {
            frame
                .input_environment
                .clone()
                .unwrap_or_else(|| self.capture_typing_environment_with_bindings(&frame.env))
        } else {
            self.capture_typing_environment_with_bindings(&frame.env)
        };
        self.bindings.push(BindingInfo {
            declaration,
            pattern,
            birth,
            context: self.invocation_context(frame.callable_owner),
            typing_environment,
            name: name.into(),
            value,
            mode,
            owner: frame.owner,
            lexical_scope: self.block_boundaries.last().copied().unwrap_or(u32::MAX),
            span,
            root,
            cell,
            alive: true,
            slot_used: false,
            write_used: false,
            used: false,
            forwarded: BTreeSet::new(),
            parameter,
        });
        if parameter {
            self.record_parameter_source(id, name, span);
        }
        self.update_named_lexical_binding(id);
        self.update_type_contract_environments(id);
        if !parameter {
            let mut lease = self.application_effect.lease_work(4_000_000);
            let declaration = self.original_named_declaration(id, lease.work());
            let returned = self.application_effect.return_work(lease);
            let declaration = declaration.and_then(|declaration| returned.map(|()| declaration));
            match declaration {
                Ok(None) => {
                    let value = self.bindings[id].value.clone();
                    self.publish_named_environments(&value);
                }
                Ok(Some(_)) => {}
                Err(error) => self.unsupported(
                    span,
                    format!("named declaration publication identity: {error}"),
                ),
            }
        }
        frame.env.insert(name.into(), id);
        frame.locals.push(id);
        if matches!(mode, BindingMode::Scoped | BindingMode::ScopedMut) {
            self.validate_cleanup(id, frame);
        }
        id
    }
    pub(super) fn writable_nodes(&self, value: &Value) -> BTreeSet<NodeId> {
        if value.permission != Permission::Write {
            return BTreeSet::new();
        }
        let mut result = value.origins.nodes.clone();
        let mut work: Vec<_> = result.iter().copied().collect();
        while let Some(node) = work.pop() {
            for ((parent, _), child) in &self.fields {
                if *parent == node && child.permission == Permission::Write {
                    for origin in &child.origins.nodes {
                        if result.insert(*origin) {
                            work.push(*origin);
                        }
                    }
                }
            }
        }
        result
    }
    pub(super) fn has_writer(&self, value: &Value) -> bool {
        self.heap
            .reachable(value.origins.nodes.iter().copied())
            .iter()
            .any(|node| {
                self.heap.nodes[node.0 as usize]
                    .writable_roots
                    .iter()
                    .any(|root| {
                        self.bindings
                            .get(root.0 as usize)
                            .is_some_and(|binding| binding.alive)
                    })
            })
    }
    pub(super) fn check_authority_use(&mut self, id: BindingId) {
        let binding = &self.bindings[id];
        let invalid = (binding.mode.is_mutable() && !binding.write_used)
            || (binding.mode.is_reassignable() && !binding.slot_used);
        if invalid {
            self.error(
                "E0527",
                binding.span,
                format!(
                    "binding {} does not exercise its declared authority",
                    binding.name
                ),
                [binding.value.cause],
            );
        }
    }
    pub(super) fn use_binding(&mut self, id: BindingId, mode: Mode, frame: &mut Frame) {
        self.record_binding_use(id, mode, true, frame);
    }
    fn record_binding_use(&mut self, id: BindingId, mode: Mode, interior: bool, frame: &mut Frame) {
        self.bindings[id].used = true;
        if mode != Mode::Read && interior {
            self.mark_write(id);
        }
        let binding = &self.bindings[id];
        if binding.owner != frame.owner
            && !(mode == Mode::Read && self.static_value_bindings.contains(&id))
            && binding
                .value
                .callables
                .iter()
                .all(|c| !matches!(c, Callable::Named(_)))
        {
            frame
                .obligations
                .named
                .entry(id)
                .and_modify(|m| *m = (*m).max(mode))
                .or_insert(mode);
            frame
                .obligations
                .concrete
                .entry(id)
                .and_modify(|m| *m = (*m).max(mode))
                .or_insert(mode);
            frame
                .obligations
                .direct
                .entry(id)
                .and_modify(|m| *m = (*m).max(mode))
                .or_insert(mode);
        }
        if binding.parameter && binding.owner == frame.owner && mode != Mode::Read {
            frame.obligations.parameter_write = true;
        }
    }
    pub(super) fn mark_write(&mut self, id: BindingId) {
        let mut work = vec![id];
        let mut seen = BTreeSet::new();
        while let Some(id) = work.pop() {
            if seen.insert(id) {
                self.bindings[id].write_used = true;
                work.extend(&self.bindings[id].forwarded);
            }
        }
    }
    fn compound_assignment_value(
        &mut self,
        old: &Value,
        mut value: Value,
        operator: &str,
        span: Span,
    ) -> Value {
        if operator == "=" {
            return value;
        }
        let op = operator.strip_suffix('=').unwrap_or(operator);
        let ty = self.expanded(&old.ty, &mut BTreeSet::new());
        let integer = matches!(ty, Ty::Int(_));
        let numeric = integer || matches!(ty, Ty::Float(_));
        let bitwise = matches!(op, "&" | "|" | "^" | "<<" | ">>");
        let wrapping = matches!(op, "+%" | "-%" | "*%");
        if self.equality_has_generic(&ty) {
            self.unsupported(span,"compound arithmetic requires a numeric operation contract for every generic instance");
        } else if !numeric
            || (bitwise && !integer)
            || (wrapping && (!integer || matches!(&ty,Ty::Int(name)if name=="bigint")))
            || !matches!(
                op,
                "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^" | "<<" | ">>" | "+%" | "-%" | "*%"
            )
        {
            self.error(
                "E0327",
                span,
                "compound operator is unavailable for this target type",
                [old.cause, value.cause],
            );
        }
        if matches!(op, "<<" | ">>") {
            if !matches!(self.expanded(&value.ty, &mut BTreeSet::new()), Ty::Int(_)) {
                self.error(
                    "E0327",
                    span,
                    "shift count must have an integer type",
                    [value.cause],
                );
            }
        } else {
            self.require_type(&value, &old.ty, span);
        }
        value.ty = old.ty.clone();
        value.constant = None;
        value.unsuffixed_numeric = false;
        value.literal_number = false;
        value
    }
    pub(super) fn assign(
        &mut self,
        target: &Expr,
        operator: &str,
        rhs_syntax: &Expr,
        mut value: Value,
        rhs: Option<StorageObservation>,
        frame: &mut Frame,
    ) -> Option<Value> {
        let Some(rhs) = rhs else {
            self.unsupported(
                target.span,
                "storage write has no actual right-hand-side observation",
            );
            return None;
        };
        let value_recency = rhs.allocation_epoch;
        if let ExprKind::Name(name) = &target.kind {
            let Some(&id) = frame.env.get(name) else {
                self.error("E0204", target.span, format!("unknown binding {name}"), []);
                return None;
            };
            let binding = self.bindings[id].clone();
            self.refinements.retain(|place, _| place.root != id);
            if binding.owner != frame.owner
                && !self
                    .heap
                    .reachable(value.origins.nodes.iter().copied())
                    .is_disjoint(&self.active_drafts)
            {
                self.error(
                    "E0607",
                    target.span,
                    "derive draft reference escapes into outside storage",
                    [value.cause],
                );
            }
            if !binding.mode.is_reassignable() {
                self.error(
                    if binding.mode.is_mutable() {
                        "E0502"
                    } else {
                        "E0501"
                    },
                    target.span,
                    "binding cannot be reassigned",
                    [binding.value.cause],
                );
            }
            if !self.check_storage_write_source(
                super::storage_sources::StoreReception {
                    target,
                    operator,
                    rhs_syntax,
                    rhs,
                    destination: StorageDestination::Binding(id),
                    receiver: None,
                },
                &mut value,
                frame,
            ) {
                return None;
            }
            value = self.compound_assignment_value(&binding.value, value, operator, target.span);
            self.require_type(&value, &binding.value.ty, target.span);
            if binding.mode == BindingMode::VarMut {
                if value.permission != Permission::Write {
                    self.error(
                        "E0520",
                        target.span,
                        "replacement cannot grant write authority",
                        [value.cause],
                    );
                }
                if !value.construction
                    && self.has_writer(&value)
                    && !value.marker
                    && !value.retention_result
                {
                    self.error(
                        "E0510",
                        target.span,
                        "writable replacement sharing requires ^mut",
                        [value.cause],
                    );
                }
            } else {
                value.permission = Permission::Read;
                value.construction = false;
            }
            if binding.owner != frame.owner {
                self.check_stored_authority(
                    &binding.value,
                    &value,
                    Some(&binding.value),
                    target.span,
                    frame,
                );
            }
            self.bindings[id].slot_used = true;
            self.record_binding_use(id, Mode::Write, false, frame);
            value.sources = [id].into();
            value.stable = false;
            // A returned sharing acknowledgement authorizes this reception.
            // A subsequent read of the variable is a new path, not another
            // use of the same one-shot receipt or construction capability.
            value.marker = false;
            value.retention_result = false;
            value.unsuffixed_numeric = false;
            value.static_coordinate = None;
            value.construction = false;
            if binding.mode == BindingMode::VarMut {
                value.publication = Publication::Live;
            }
            if binding.mode == BindingMode::VarMut {
                for node in self.writable_nodes(&binding.value) {
                    self.heap.nodes[node.0 as usize]
                        .writable_roots
                        .remove(&binding.root);
                }
                for node in self.writable_nodes(&value) {
                    self.heap.nodes[node.0 as usize]
                        .writable_roots
                        .insert(binding.root);
                }
            }
            if let Some(cell) = binding.cell {
                let mut slot_value = value.clone();
                slot_value.origins = Origins::one(cell);
                slot_value.participants = binding.value.participants.clone();
                self.note_refinement_write(&slot_value, &Some(Slot::Field("value".into())), false);
                frame.obligations.accesses.push(AccessFact {
                    observed_recency: self.recency_moves.len(),
                    recency: self.recency_moves.len(),
                    origin_owners: self.access_owners(&slot_value.origins),
                    origins: slot_value.origins,
                    slot: Some(Slot::Field("value".into())),
                    mode: Mode::Write,
                    participants: slot_value.participants,
                    cause: slot_value.cause,
                    span: target.span,
                });
                self.store_field(cell, Slot::Field("value".into()), value.clone());
                self.uncertain_slots
                    .remove(&(cell, Slot::Field("value".into())));
            }
            self.bindings[id].value = value;
            let _ = operator;
            return None;
        }
        let (base, slot, receiver, selector, index_value) = match &target.kind {
            ExprKind::Field { base, field, .. } => {
                let (base, observed) = self.expression_observed(base, frame);
                let Some(expression) = observed else {
                    self.unsupported(target.span, "storage receiver has no actual observation");
                    return None;
                };
                let receiver = StorageObservation {
                    expression,
                    allocation_epoch: self.recency_moves.len(),
                };
                let slot = if let Ok(i) = field.parse() {
                    Slot::Tuple(i)
                } else {
                    Slot::Field(field.clone())
                };
                if base.ty == Ty::Never {
                    self.record_aborted_storage_write(
                        target,
                        operator,
                        rhs,
                        StorageDestination::Projection {
                            receiver,
                            selector: None,
                            slot,
                        },
                        frame,
                    );
                    return Some(base);
                }
                (base, slot, receiver, None, None)
            }
            ExprKind::Index { base, index, .. } => {
                let (mut base, observed) = self.expression_observed(base, frame);
                let base_recency = self.recency_moves.len();
                let Some(expression) = observed else {
                    self.unsupported(target.span, "storage receiver has no actual observation");
                    return None;
                };
                let receiver = StorageObservation {
                    expression,
                    allocation_epoch: base_recency,
                };
                if base.ty == Ty::Never {
                    self.record_aborted_storage_write(
                        target,
                        operator,
                        rhs,
                        StorageDestination::Projection {
                            receiver,
                            selector: None,
                            slot: Slot::AnyIndex,
                        },
                        frame,
                    );
                    return Some(base);
                }
                let (index, observed) = self.expression_observed(index, frame);
                let Some(expression) = observed else {
                    self.unsupported(target.span, "storage selector has no actual observation");
                    return None;
                };
                let selector = StorageObservation {
                    expression,
                    allocation_epoch: self.recency_moves.len(),
                };
                if index.ty == Ty::Never {
                    self.record_aborted_storage_write(
                        target,
                        operator,
                        rhs,
                        StorageDestination::Projection {
                            receiver,
                            selector: Some(selector),
                            slot: Slot::AnyIndex,
                        },
                        frame,
                    );
                    return Some(index);
                }
                self.transport_value_since(&mut base, base_recency);
                self.transport_value_since(&mut value, value_recency);
                let base_ty = self.collection_type(&base);
                if matches!(base_ty, Ty::Map(..)) && operator != "=" {
                    self.error(
                        "E0301",
                        target.span,
                        "map compound assignment cannot implicitly unwrap an optional lookup",
                        [base.cause],
                    );
                }
                match &base_ty {
                    Ty::Map(key, _) => self.require_type(&index, key, target.span),
                    Ty::Array(_) => self.require_type(&index, &Ty::Int("int".into()), target.span),
                    _ => self.error(
                        "E0352",
                        target.span,
                        "receiver does not provide assignable element lookup",
                        [base.cause],
                    ),
                }
                let slot = if matches!(base_ty, Ty::Map(..)) {
                    Slot::AnyIndex
                } else if let Some(Constant::Integer(i)) = index.constant {
                    Slot::Index(i as i64)
                } else {
                    Slot::AnyIndex
                };
                (base, slot, receiver, Some(selector), Some(index))
            }
            _ => {
                self.error(
                    "E0503",
                    target.span,
                    "assignment requires an assignable target",
                    [],
                );
                return None;
            }
        };
        // The right-hand side was evaluated before the assignment target.
        // Field/index target evaluation can recycle a site referenced by it.
        if !matches!(target.kind, ExprKind::Index { .. }) {
            self.transport_value_since(&mut value, value_recency);
        }
        // Known path/member restrictions are independent of Source completeness.
        // A missing source proof may prevent a store, but cannot hide an
        // already proven readonly-path or immutable-member error.
        if base.permission != Permission::Write {
            let container = matches!(target.kind, ExprKind::Index { .. })
                || base.sources.iter().any(|id| {
                    matches!(
                        self.expanded(&self.bindings[*id].value.ty, &mut BTreeSet::new()),
                        Ty::Array(_) | Ty::Map(..)
                    )
                });
            self.error(
                if container {
                    "E0522"
                } else if base.readonly_spread {
                    "E0525"
                } else {
                    "E0520"
                },
                target.span,
                "write through read-only access path",
                [base.cause],
            );
        }
        if let (Ty::Record(fields) | Ty::OpenRecord { fields, .. }, Slot::Field(name)) = (
            self.record_bound_receiver_view(&base.ty)
                .unwrap_or_else(|| self.expanded(&base.ty, &mut BTreeSet::new())),
            &slot,
        ) && fields.get(name).is_some_and(|(mutable, _)| !mutable)
            && !(!base.origins.nodes.is_empty()
                && base.origins.nodes.is_subset(&self.active_drafts))
        {
            self.error(
                "E0520",
                target.span,
                "record slot is not mutable",
                [base.cause],
            );
        }
        if !self.check_storage_write_source(
            super::storage_sources::StoreReception {
                target,
                operator,
                rhs_syntax,
                rhs,
                destination: StorageDestination::Projection {
                    receiver,
                    selector,
                    slot: slot.clone(),
                },
                receiver: Some(&base),
            },
            &mut value,
            frame,
        ) {
            return None;
        }
        if let Some(index) = &index_value {
            self.constrain_collection_insert(&base, &value, Some(index), target.span);
        }
        if matches!(slot, Slot::Index(_) | Slot::AnyIndex) {
            self.constrain_collection_insert(&base, &value, None, target.span);
        }
        let projection_start = self.generic_bound_projections.len();
        let old = self.project(&base, slot.clone(), target.span, frame, false);
        let bound_projections: Vec<_> =
            (projection_start..self.generic_bound_projections.len()).collect();
        value = self.compound_assignment_value(&old, value, operator, target.span);
        self.require_type(&value, &old.ty, target.span);
        if (!old.results.is_empty() || !value.results.is_empty())
            && !self.result_field_update_is_closed(&base, &slot, &value, frame)
        {
            self.unsupported(
                target.span,
                "replacing Result-bearing storage requires exact per-producer membership transfer",
            );
        }
        self.check_stored_authority(&base, &value, Some(&old), target.span, frame);
        let access = if bound_projections.is_empty() {
            self.access(&base, Some(slot.clone()), Mode::Write, target.span, frame);
            None
        } else {
            Some(self.bound_write_access(&base, slot.clone(), target.span, frame))
        };
        if operator != "=" {
            value.constant = None;
        }
        self.write_aliased_field(&base, &slot, &value, frame, target.span);
        if let Some(access) = access {
            for projection_index in bound_projections {
                self.record_bound_field_write(super::bound_writes::ObservedStore {
                    projection_index,
                    rhs_expression: Some(rhs.expression),
                    receiver_expression: Some(receiver.expression),
                    access,
                    operator,
                    replacement: &value,
                    receiver: &base,
                    span: target.span,
                });
            }
        }
        if matches!(&slot,Slot::Field(name)if name=="on_close") {
            for id in &base.scoped {
                self.validate_cleanup(*id, frame);
            }
        }
        None
    }
}
