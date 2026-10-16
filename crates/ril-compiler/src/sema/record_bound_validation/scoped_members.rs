//! Staged symbolic member type identity, separate from value authority.
//! A generic U key describes a type coordinate. It says nothing about hidden
//! Results, resources, capture, copy eligibility, retained sharing or escape.
use super::*;
use crate::sema::{
    copy_contract::CopyInvocation, effect_identity::InvocationContext,
    scoped_source_identity::ScopedSourceIdentity,
};

/// Stages are constructed only by replay below. Their fields are private: a
/// caller cannot substitute a raw header or a caller-built receiver Expr.
pub(super) struct DeclaredBoundProbe<'a> {
    bound: &'a GenericRecordBound,
    projection: &'a GenericBoundProjection,
    scope: BoundScope,
    call: &'a CopyInvocation,
    /// Every real material T position was checked before issuing this stage.
    whole_entries: Vec<&'a CopyValueSnapshot>,
}

struct ScopedHeaderOccurrence<'a> {
    original: &'a CopyValueSnapshot,
    original_receiver: &'a Value,
    actual: &'a CopyValueSnapshot,
    actual_receiver: &'a Value,
    header: &'a TypeExpr,
    scope: BoundScope,
}

/// This stage validates complete source headers, all T paths and the original
/// formal receptions. It deliberately does not claim stored-schema completion:
/// each existing member is checked only after this stage has been established.
pub(super) struct ScopedOriginalFormal<'a> {
    identity: &'a ScopedSourceIdentity,
    context: InvocationContext,
    entry_epoch: usize,
    occurrences: Vec<ScopedHeaderOccurrence<'a>>,
}

#[derive(Clone, Copy)]
pub(super) enum ReceptionSide {
    Original,
    Actual,
}

fn same_material_path(left: &[BoundTypeSelectionStep], right: &[BoundTypeSelectionStep]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| match (left, right) {
                (BoundTypeSelectionStep::Tuple(a), BoundTypeSelectionStep::Tuple(b)) => a == b,
                (BoundTypeSelectionStep::Field(a), BoundTypeSelectionStep::Field(b)) => a == b,
                _ => false,
            })
}

pub(super) fn symbolic_member_key(key: &ArgumentKey, scope: &BoundScope) -> bool {
    if !matches!(
        key,
        ArgumentKey::Array { .. } | ArgumentKey::Callable { .. }
    ) {
        return false;
    }
    let mut pending = vec![(key, 0usize)];
    let mut work = 4096usize;
    let mut symbolic = false;
    while let Some((key, depth)) = pending.pop() {
        if work == 0 || depth >= 64 {
            return false;
        }
        work -= 1;
        match key {
            ArgumentKey::Closed(_) => return false,
            ArgumentKey::Binder {
                identity,
                sort: StaticBinderSort::Type,
            } => {
                if !scope.types.values().any(|known| known == identity) {
                    return false;
                }
                symbolic = true;
            }
            ArgumentKey::Record { row: Some(_), .. } => return false,
            ArgumentKey::Name { arguments, .. } | ArgumentKey::Tuple(arguments) => {
                pending.extend(arguments.iter().map(|key| (key, depth + 1)))
            }
            ArgumentKey::Array { element, .. } => pending.push((element, depth + 1)),
            ArgumentKey::Map { key, value } => {
                pending.push((key, depth + 1));
                pending.push((value, depth + 1));
            }
            ArgumentKey::Record { fields, row: None } => {
                pending.extend(fields.iter().map(|(_, _, key)| (key, depth + 1)))
            }
            ArgumentKey::Callable {
                parameters, result, ..
            } => {
                pending.extend(parameters.iter().map(|(_, key)| (key, depth + 1)));
                pending.push((result, depth + 1));
            }
        }
    }
    symbolic
}

/// Construct only after the genuine declaration or full original-formal
/// reception was independently replayed. This token is private and grants no
/// access; it never becomes a closed SourceTypeWitness.
pub(super) struct MemberIdentity<'a> {
    label: &'a str,
    mutable: bool,
    header: &'a TypeExpr,
    key: ArgumentKey,
    scope: BoundScope,
    snapshot: &'a CopyValueSnapshot,
    member: &'a Value,
    entry_epoch: usize,
}

impl Replay<'_> {
    pub(super) fn replay_scoped_member_schemas(
        &self,
        reception: &ScopedOriginalFormal<'_>,
    ) -> Check {
        for (ordinal, occurrence) in reception.occurrences.iter().enumerate() {
            let ArgumentKey::Record {
                fields: known,
                row: Some(row),
            } = self.normalized_key(occurrence.header, &occurrence.scope)?
            else {
                return Err("staged source lost its complete open record header".into());
            };
            let ArgumentKey::Binder {
                identity: row_id, ..
            } = *row
            else {
                return Err("staged source lost its original row identity".into());
            };
            let TypeKind::Record {
                fields: syntax_fields,
                ..
            } = &occurrence.header.kind
            else {
                return Err("staged source lost its actual record syntax".into());
            };
            let Ty::OpenRecord { fields: types, .. } = &occurrence.original_receiver.ty else {
                return Err("staged source lost its original semantic field view".into());
            };
            let fields = known
                .iter()
                .map(|(label, mutable, key)| {
                    let syntax = syntax_fields
                        .iter()
                        .find(|field| &field.name == label)
                        .ok_or_else(|| "staged source invented an original field".to_owned())?;
                    let (_, ty) = types.get(label).ok_or_else(|| {
                        "staged source invented an original semantic field".to_owned()
                    })?;
                    Ok(RecordBoundField {
                        label: label.clone(),
                        mutable: *mutable,
                        ty: ty.clone(),
                        syntax: syntax.ty.clone(),
                        key: key.clone(),
                    })
                })
                .collect::<Check<Vec<_>>>()?;
            let anchor = &reception.identity.occurrences[ordinal].formal;
            let tail = RowTail::Open(OpenTail {
                identity: RowIdentity::Binder(row_id.clone()),
                lacks: self.signature_lacks(anchor.definition, &occurrence.scope, &row_id)?,
            });
            for side in [ReceptionSide::Original, ReceptionSide::Actual] {
                let (snapshot, receiver) = match side {
                    ReceptionSide::Original => (occurrence.original, occurrence.original_receiver),
                    ReceptionSide::Actual => (occurrence.actual, occurrence.actual_receiver),
                };
                let tokens = self.scoped_member_tokens(reception, ordinal, side)?;
                self.stored_schema_with_members(
                    snapshot,
                    receiver,
                    &fields,
                    &occurrence.scope,
                    &tail,
                    &tokens,
                )?;
            }
        }
        Ok(())
    }

    pub(super) fn scoped_member_tokens<'a>(
        &'a self,
        reception: &ScopedOriginalFormal<'a>,
        ordinal: usize,
        side: ReceptionSide,
    ) -> Check<Vec<MemberIdentity<'a>>> {
        let occurrence = reception
            .occurrences
            .get(ordinal)
            .ok_or_else(|| "symbolic member has no covered occurrence".to_owned())?;
        let TypeKind::Record { fields, .. } = &occurrence.header.kind else {
            return Err("symbolic source lost its original record header".into());
        };
        let mut result = Vec::new();
        for field in fields {
            let key = self.normalized_key(&field.ty, &occurrence.scope)?;
            if symbolic_member_key(&key, &occurrence.scope) {
                result.push(self.scoped_formal_member(reception, ordinal, side, &field.name)?);
            }
        }
        Ok(result)
    }

    pub(super) fn scoped_reception_for_check<'a>(
        &'a self,
        check: &GenericBoundCheck,
    ) -> Check<Option<ScopedOriginalFormal<'a>>> {
        if !matches!(
            check.actual_schema.source,
            StructuralSchemaSource::RigidParameter { .. }
        ) {
            return Ok(None);
        }
        let scope = self.schema_scope(check)?;
        if !check
            .actual_schema
            .fields
            .iter()
            .any(|field| symbolic_member_key(&field.key, &scope))
        {
            return Ok(None);
        }
        let matching: Vec<_> = self
            .facts
            .scoped_source_identities
            .iter()
            .filter(|identity| {
                identity.required == check.required && identity.context == check.context
            })
            .collect();
        require(
            matching.len() == 1,
            "symbolic schema has no unique complete scoped source",
        )?;
        self.scoped_original_formal(matching[0]).map(Some)
    }

    pub(super) fn verify_symbolic_field(
        &self,
        tokens: &[MemberIdentity<'_>],
        snapshot: &CopyValueSnapshot,
        stored: &Value,
        field: &RecordBoundField,
        scope: &BoundScope,
    ) -> Check {
        let matching: Vec<_> = tokens
            .iter()
            .filter(|identity| identity.label == field.label)
            .collect();
        require(
            matching.len() == 1,
            "stored symbolic field lacks one complete staged member identity",
        )?;
        self.require_member_identity(matching[0], snapshot, stored, field, scope)
    }

    fn symbolic_member_sources(&self, snapshot: &CopyValueSnapshot, member: &Value) -> Check {
        let mut pending = vec![(member, 0usize)];
        let mut visited = BTreeSet::new();
        let mut work = LIMIT;
        while let Some((value, depth)) = pending.pop() {
            require(
                work > 0 && depth < 64,
                "symbolic member source walk exceeds replay budget",
            )?;
            work -= 1;
            if matches!(value.ty, Ty::Generic(_)) {
                require(
                    !value.origins.nodes.is_empty(),
                    "an unresolved U value cannot erase its possible reference sources and pretend to be a scalar copy",
                )?;
            }
            for payload in [
                &value.option_payload,
                &value.result_payload,
                &value.result_success,
                &value.result_error,
                &value.variant_payload,
            ]
            .into_iter()
            .flatten()
            {
                pending.push((payload, depth + 1));
            }
            pending.extend(
                value
                    .variant_witnesses
                    .values()
                    .map(|payload| (payload.as_ref(), depth + 1)),
            );
            for origin in &value.origins.nodes {
                if !visited.insert(*origin) {
                    continue;
                }
                let node = snapshot
                    .nodes
                    .iter()
                    .find(|node| node.origin == *origin)
                    .ok_or_else(|| {
                        "symbolic member lost an existing source graph node".to_owned()
                    })?;
                pending.extend(node.fields.iter().map(|(_, value)| (value, depth + 1)));
            }
        }
        Ok(())
    }

    fn member_coordinates(&self, key: &ArgumentKey, scope: &BoundScope) -> Check {
        let mut pending = vec![(key, false, 0usize)];
        let mut work = 4096;
        while let Some((key, row_position, depth)) = pending.pop() {
            require(
                work > 0 && depth < 64,
                "symbolic member identity exceeds its finite type budget",
            )?;
            work -= 1;
            match key {
                ArgumentKey::Closed(_) => {
                    return Err("symbolic member has an unresolved type computation".into());
                }
                ArgumentKey::Binder {
                    identity,
                    sort: StaticBinderSort::Type,
                } => {
                    if scope.types.values().any(|actual| actual == identity) {
                        self.type_binder(identity)?;
                    } else {
                        require(
                            row_position
                                && scope.rows.values().any(|id| {
                                    self.facts.bound_rows.get(id.0 as usize).is_some_and(|row| {
                                        row.id == *id
                                            && row.identity == RowIdentity::Binder(identity.clone())
                                    })
                                }),
                            "a member type coordinate is not its real nearest U binder",
                        )?;
                    }
                }
                ArgumentKey::Name { arguments, .. } | ArgumentKey::Tuple(arguments) => {
                    pending.extend(arguments.iter().map(|key| (key, false, depth + 1)))
                }
                ArgumentKey::Array { length, element } => {
                    if let Some(length) = length {
                        let length = length
                            .strip_prefix("const(int:")
                            .and_then(|length| length.strip_suffix(')'))
                            .and_then(|length| length.parse::<u64>().ok())
                            .ok_or_else(|| {
                                "symbolic member array lacks a normalized dimension".to_owned()
                            })?;
                        let layout = self.facts.target_layout.ok_or_else(|| {
                            "symbolic member array lacks its abstract target layout".to_owned()
                        })?;
                        require(
                            matches!(layout.pointer_bits, 32 | 64)
                                && length < (1u64 << (layout.pointer_bits - 1)),
                            "symbolic member dimension exceeds its target int",
                        )?;
                    }
                    pending.push((element, false, depth + 1));
                }
                ArgumentKey::Map { key, value } => {
                    pending.push((key, false, depth + 1));
                    pending.push((value, false, depth + 1));
                }
                ArgumentKey::Record { fields, row } => {
                    pending.extend(fields.iter().map(|(_, _, key)| (key, false, depth + 1)));
                    if let Some(row) = row {
                        pending.push((row, true, depth + 1));
                    }
                }
                ArgumentKey::Callable {
                    parameters,
                    result,
                    annotations,
                } => {
                    require(
                        annotations.iter().all(|annotation| {
                            matches!(
                                annotation.as_str(),
                                "&mut" | "&^mut" | "&capture" | "&closure" | "@{}" | "&{}"
                            )
                        }),
                        "named callable state/effect bounds need their own scoped proof",
                    )?;
                    pending.extend(parameters.iter().map(|(_, key)| (key, false, depth + 1)));
                    pending.push((result, false, depth + 1));
                }
            }
        }
        Ok(())
    }

    /// Hook: projections(), after its actual ProjectionSite match and cause
    /// replay. `site.base` is borrowed directly from that bounded source walk.
    /// Do not expose an Expr-taking variant or rewalk/reset the source budget.
    pub(super) fn declared_bound_probe<'a>(
        &'a self,
        projection: &'a GenericBoundProjection,
        site: &ProjectionSite<'_>,
    ) -> Check<DeclaredBoundProbe<'a>> {
        let bound = self
            .facts
            .record_bounds
            .get(projection.required.0 as usize)
            .filter(|bound| bound.id == projection.required)
            .ok_or_else(|| "symbolic member has no registered structural declaration".to_owned())?;
        let binder = self.binder(bound.definition, bound.generic_index)?;
        require(
            bound.binder == binder.identity
                && projection.source.value.ty == Ty::Generic(binder.identity.clone()),
            "symbolic bound member borrowed another actual T",
        )?;
        let call = projection
            .context
            .invocation
            .and_then(|id| {
                self.facts
                    .copy_invocations
                    .get(id.0 as usize)
                    .filter(|call| call.id == id && call.status == CopyInvocationStatus::Completed)
            })
            .ok_or_else(|| "symbolic member has no actual whole argument entry".to_owned())?;
        require(
            call.arguments.len() == self.function(call.target)?.syntax.parameters.len(),
            "symbolic member argument table has missing entries or wrong arity",
        )?;
        require(
            call.declaration_probe
                && call.target == bound.definition
                && projection.context.owner == Some(CallableOwner::Function(bound.definition))
                && projection.allocation_epoch == call.entry_allocation_epoch
                && projection.access == BoundAccess::Read
                && site.supported
                && site.assignment.is_none()
                && Some(site.owner) == projection.context.owner
                && site.expression.span == projection.span
                && projection.slot == Slot::Field(site.field.to_string()),
            "symbolic declaration member has no actual readonly source projection in its owner",
        )?;
        let summaries: Vec<_> = self
            .facts
            .invocations
            .iter()
            .filter(|summary| summary.context == Some(projection.context))
            .collect();
        require(
            summaries.len() == 1 && summaries[0].activation == Some(projection.activation),
            "symbolic declaration probe borrowed another actual activation",
        )?;
        self.every_scoped_occurrence_is_material(call.target, &bound.binder)?;
        let paths = self.declared_type_paths(call.target, &bound.binder)?;
        require(
            !paths.is_empty(),
            "symbolic declaration probe has no real material T occurrence",
        )?;
        let mut whole_entries = Vec::new();
        for (argument, path) in &paths {
            let (mode, entry) = call.arguments.get(*argument).ok_or_else(|| {
                "symbolic declaration T path has no whole actual entry".to_owned()
            })?;
            require(
                *mode == super::super::model::Mode::Read,
                "symbolic declaration type identity cannot replace a mutable reception",
            )?;
            self.snapshot(entry)?;
            let selected = self.selected_value(entry, path)?;
            require(
                selected.ty == Ty::Generic(bound.binder.clone()),
                "symbolic declaration T path changed its real nearest binder",
            )?;
            whole_entries.push(entry);
        }
        let scope = self.scope(bound.definition)?;
        self.snapshot(&projection.source)?;
        self.literal_coordinate_observation(site, projection.context)?;
        let observed = self.observed_product_value(projection.context, site.base)?;
        require(
            observed == &projection.source.value,
            "symbolic declaration receiver is not its real source observation",
        )?;
        self.read_parameter_reception(
            &projection.source.value,
            site.base,
            projection.context,
            projection.activation,
            projection.allocation_epoch,
        )?;
        Ok(DeclaredBoundProbe {
            bound,
            projection,
            scope,
            call,
            whole_entries,
        })
    }

    pub(super) fn declared_probe_member<'a>(
        &'a self,
        reception: &DeclaredBoundProbe<'a>,
        label: &str,
    ) -> Check<MemberIdentity<'a>> {
        require(
            !reception.whole_entries.is_empty()
                && reception.projection.allocation_epoch == reception.call.entry_allocation_epoch,
            "symbolic declaration member has no fully covered frozen entry",
        )?;
        let syntax = self
            .function(reception.bound.definition)?
            .syntax
            .generics
            .get(reception.bound.generic_index as usize)
            .and_then(|parameter| parameter.bound.as_ref())
            .ok_or_else(|| "symbolic declaration has no original bound clause".to_owned())?;
        let TypeKind::Record { fields, .. } = &syntax.kind else {
            return Err("symbolic declaration owner is not a structural bound".into());
        };
        let field = fields
            .iter()
            .find(|field| field.name == label)
            .ok_or_else(|| "symbolic member was not promised by its original clause".to_owned())?;
        let key = self.normalized_key(&field.ty, &reception.scope)?;
        self.member_coordinates(&key, &reception.scope)?;
        let snapshot = &reception.projection.source;
        let member = self.existing_member(snapshot, &snapshot.value, label)?;
        let identity = MemberIdentity {
            label: &field.name,
            mutable: field.mutable,
            header: &field.ty,
            key,
            scope: reception.scope.clone(),
            snapshot,
            member,
            entry_epoch: reception.call.entry_allocation_epoch,
        };
        self.stored_symbolic_member(snapshot, member, &identity)?;
        Ok(identity)
    }

    /// Hook: prefix of replay_scoped_source_identity(), before stored_schema.
    /// original_formal_view and every_scoped_occurrence_is_material need only
    /// pub(super) visibility at registration. They remain the existing actual
    /// source/root/ancestor checks, not alternate raw-header ingress points.
    pub(super) fn scoped_original_formal<'a>(
        &'a self,
        identity: &'a ScopedSourceIdentity,
    ) -> Check<ScopedOriginalFormal<'a>> {
        require(
            self.facts
                .scoped_source_identities
                .get(identity.id.0 as usize)
                .is_some_and(|registered| std::ptr::eq(registered, identity)),
            "symbolic source stage has no actual arena occurrence",
        )?;
        let bound = self
            .facts
            .record_bounds
            .get(identity.required.0 as usize)
            .filter(|bound| bound.id == identity.required && bound.binder == identity.binder)
            .ok_or_else(|| "symbolic source stage has no genuine structural binder".to_owned())?;
        let call = identity
            .context
            .invocation
            .and_then(|id| {
                self.facts
                    .copy_invocations
                    .get(id.0 as usize)
                    .filter(|call| {
                        call.id == id
                            && call.target == bound.definition
                            && call.status == CopyInvocationStatus::Completed
                    })
            })
            .ok_or_else(|| "symbolic source stage has no completed actual invocation".to_owned())?;
        require(
            call.arguments.len() == self.function(call.target)?.syntax.parameters.len(),
            "symbolic source stage whole argument table is missing or has wrong arity",
        )?;
        require(
            identity.context.owner == Some(CallableOwner::Function(call.target))
                && identity.span == call.span
                && call.entry_allocation_epoch <= self.facts.allocation_history.len()
                && self
                    .facts
                    .explanations
                    .causes
                    .get(identity.cause.0 as usize)
                    .is_some_and(|cause| cause.id == identity.cause),
            "symbolic source stage lacks its actual owner, call, cause or frozen epoch",
        )?;
        let summaries: Vec<_> = self
            .facts
            .invocations
            .iter()
            .filter(|summary| summary.context == Some(identity.context))
            .collect();
        require(
            summaries.len() == 1
                && summaries[0]
                    .activation
                    .is_some_and(|activation| self.facts.allocated_scopes.contains(&activation)),
            "symbolic source stage has no unique registered invocation activation",
        )?;
        self.every_scoped_occurrence_is_material(call.target, &identity.binder)?;
        let paths = self.declared_type_paths(call.target, &identity.binder)?;
        require(
            !paths.is_empty() && paths.len() == identity.occurrences.len(),
            "symbolic source stage has incomplete real T path coverage",
        )?;
        require(
            self.normalized_key(&identity.syntax, &identity.scope)? == identity.key,
            "symbolic source descriptor differs from its complete key",
        )?;
        self.member_coordinates(&identity.key, &identity.scope)?;
        let mut occurrences = Vec::new();
        for (ordinal, ((argument, path), occurrence)) in
            paths.iter().zip(&identity.occurrences).enumerate()
        {
            require(
                *argument == occurrence.argument_index as usize
                    && same_material_path(path, &occurrence.selection_path),
                "symbolic source stage borrowed another actual T path",
            )?;
            let (mode, actual) = call
                .arguments
                .get(*argument)
                .ok_or_else(|| "symbolic source T path lacks a whole actual entry".to_owned())?;
            require(
                *mode == super::super::model::Mode::Read,
                "symbolic source type identity cannot replace mutable reception",
            )?;
            self.snapshot(actual)?;
            let actual_receiver = self.selected_value(actual, path)?;
            if ordinal == 0 {
                require(
                    actual_receiver.cause == identity.cause,
                    "symbolic source stage borrowed another selected value cause",
                )?;
            }
            let (original, original_receiver, header, scope) =
                self.original_formal_view(call, &occurrence.formal)?;
            let key = self.normalized_key(header, &scope)?;
            require(
                original_receiver.origins == actual_receiver.origins && key == identity.key,
                "symbolic source stage changed the object or complete original identity",
            )?;
            self.member_coordinates(&key, &scope)?;
            if ordinal == 0 {
                require(
                    scope == identity.scope && header.span == identity.syntax.span,
                    "symbolic source stage borrowed another primary header namespace",
                )?;
            }
            let ArgumentKey::Record {
                fields,
                row: Some(row),
            } = &key
            else {
                return Err("symbolic source stage is not a genuine original open record".into());
            };
            let ArgumentKey::Binder {
                identity: row_id,
                sort: StaticBinderSort::Type,
            } = row.as_ref()
            else {
                return Err("symbolic source stage has no genuine original row binder".into());
            };
            self.type_binder(row_id)?;
            for receiver in [original_receiver, actual_receiver] {
                let Ty::OpenRecord {
                    fields: actual_fields,
                    row: actual_row,
                } = &receiver.ty
                else {
                    return Err("symbolic source header belongs to another received type".into());
                };
                require(
                    actual_fields.len() == fields.len()
                        && actual_row.identity == RowIdentity::Binder(row_id.clone()),
                    "symbolic source stage changed the actual field family or row",
                )?;
                for (label, mutable, key) in fields {
                    let (actual_mutable, actual_ty) =
                        actual_fields.get(label).ok_or_else(|| {
                            "symbolic source header invented a received member".to_owned()
                        })?;
                    require(
                        actual_mutable == mutable,
                        "symbolic source changed member mutability",
                    )?;
                    self.ty_matches(actual_ty, key, &scope, 0)?;
                }
            }
            occurrences.push(ScopedHeaderOccurrence {
                original,
                original_receiver,
                actual,
                actual_receiver,
                header,
                scope,
            });
        }
        Ok(ScopedOriginalFormal {
            identity,
            context: identity.context,
            entry_epoch: call.entry_allocation_epoch,
            occurrences,
        })
    }

    /// Only a complete staged reception can issue this token. Neither header
    /// syntax nor a caller supplied frozen snapshot is accepted as an input.
    pub(super) fn scoped_formal_member<'a>(
        &self,
        reception: &ScopedOriginalFormal<'a>,
        occurrence: usize,
        side: ReceptionSide,
        label: &str,
    ) -> Check<MemberIdentity<'a>> {
        require(
            !reception.occurrences.is_empty()
                && reception.context.invocation.is_some()
                && reception.entry_epoch <= self.facts.allocation_history.len(),
            "symbolic member has no complete original formal reception",
        )?;
        let occurrence = reception.occurrences.get(occurrence).ok_or_else(|| {
            "symbolic member selected a nonexistent covered T occurrence".to_owned()
        })?;
        let TypeKind::Record { fields, .. } = &occurrence.header.kind else {
            return Err("symbolic member source is not its original record header".into());
        };
        let field = fields
            .iter()
            .find(|field| field.name == label)
            .ok_or_else(|| "symbolic member does not occur in its original header".to_owned())?;
        let (snapshot, receiver) = match side {
            ReceptionSide::Original => (occurrence.original, occurrence.original_receiver),
            ReceptionSide::Actual => (occurrence.actual, occurrence.actual_receiver),
        };
        let key = self.normalized_key(&field.ty, &occurrence.scope)?;
        self.member_coordinates(&key, &occurrence.scope)?;
        let member = self.existing_member(snapshot, receiver, label)?;
        let identity = MemberIdentity {
            label: &field.name,
            mutable: field.mutable,
            header: &field.ty,
            key,
            scope: occurrence.scope.clone(),
            snapshot,
            member,
            entry_epoch: reception.entry_epoch,
        };
        self.stored_symbolic_member(snapshot, member, &identity)?;
        Ok(identity)
    }

    /// schema(check) freezes a distinct copy of the canonical whole argument.
    /// It cannot borrow a canonical member token by matching NodeId or span.
    /// Replay every value, node, edge, relation and fixed/cardinality fact before
    /// issuing a new token bound to this exact registered check snapshot.
    pub(super) fn scoped_check_member<'a>(
        &'a self,
        reception: &ScopedOriginalFormal<'a>,
        check: &'a GenericBoundCheck,
        label: &str,
    ) -> Check<MemberIdentity<'a>> {
        require(
            self.facts
                .generic_bound_checks
                .get(check.id.0 as usize)
                .is_some_and(|registered| std::ptr::eq(registered, check))
                && check.required == reception.identity.required
                && check.context == reception.context
                && check.allocation_epoch == reception.entry_epoch,
            "symbolic schema member borrowed another actual check or entry epoch",
        )?;
        let occurrence = reception
            .occurrences
            .first()
            .ok_or_else(|| "symbolic schema member has no complete T path coverage".to_owned())?;
        let actual_path = reception
            .identity
            .occurrences
            .first()
            .ok_or_else(|| "symbolic schema member has no real primary T path".to_owned())?;
        require(
            check.argument_index == actual_path.argument_index
                && same_material_path(&check.selection_path, &actual_path.selection_path),
            "symbolic schema member selected another actual argument or child",
        )?;
        self.snapshot(&check.actual)?;
        require(
            self.same_snapshot(&check.actual, occurrence.actual),
            "symbolic schema member changed the canonical frozen argument graph",
        )?;
        let StructuralSchemaSource::RigidParameter {
            definition,
            parameter_index,
            syntax,
            scope,
        } = &check.actual_schema.source
        else {
            return Err("symbolic schema member has no complete scoped rigid source".into());
        };
        require(
            *definition == actual_path.formal.definition
                && *parameter_index == actual_path.formal.parameter_index
                && scope == &occurrence.scope
                && syntax.span == occurrence.header.span
                && self.normalized_key(syntax, scope)? == reception.identity.key,
            "symbolic schema member borrowed another rigid header or namespace",
        )?;
        let TypeKind::Record { fields, .. } = &occurrence.header.kind else {
            return Err("symbolic schema member has no original record header".into());
        };
        let field = fields
            .iter()
            .find(|field| field.name == label)
            .ok_or_else(|| "symbolic schema member invented an original field".to_owned())?;
        let receiver = self.selected_value(&check.actual, &check.selection_path)?;
        let member = self.existing_member(&check.actual, receiver, label)?;
        let key = self.normalized_key(&field.ty, &occurrence.scope)?;
        self.member_coordinates(&key, &occurrence.scope)?;
        let identity = MemberIdentity {
            label: &field.name,
            mutable: field.mutable,
            header: &field.ty,
            key,
            scope: occurrence.scope.clone(),
            snapshot: &check.actual,
            member,
            entry_epoch: reception.entry_epoch,
        };
        self.stored_symbolic_member(&check.actual, member, &identity)?;
        Ok(identity)
    }

    /// Hook: only the missing complete-witness branch in stored_schema(). The
    /// caller must retain all existing field/row equations and physical checks.
    /// Scope/key/mode are rechecked, so a U-bearing field cannot authorize a
    /// sibling [0][3]U, a different binder, or another callable qualification.
    pub(super) fn require_member_identity(
        &self,
        identity: &MemberIdentity<'_>,
        snapshot: &CopyValueSnapshot,
        stored: &Value,
        field: &RecordBoundField,
        scope: &BoundScope,
    ) -> Check {
        require(
            identity.label == field.label
                && identity.mutable == field.mutable
                && identity.scope == *scope
                && identity.key == field.key
                && self.normalized_key(&field.syntax, scope)? == identity.key,
            "symbolic member fallback changed the full field key or lexical scope",
        )?;
        self.stored_symbolic_member(snapshot, stored, identity)
    }

    fn existing_member<'a>(
        &self,
        snapshot: &'a CopyValueSnapshot,
        receiver: &Value,
        label: &str,
    ) -> Check<&'a Value> {
        require(
            receiver.origins.nodes.len() == 1,
            "symbolic member source needs its existing exact received object",
        )?;
        let origin = receiver
            .origins
            .nodes
            .first()
            .ok_or_else(|| "symbolic member source has no actual receiver".to_owned())?;
        snapshot
            .nodes
            .iter()
            .find(|node| node.origin == *origin)
            .and_then(|node| {
                node.fields
                    .iter()
                    .find(|(slot, _)| slot == &Slot::Field(label.into()))
            })
            .map(|(_, value)| value)
            .ok_or_else(|| "symbolic member proof cannot invent a missing stored field".to_owned())
    }

    /// Checks type identity against existing storage only. In particular an
    /// empty array does not create a U value, a Result inspection, or a copy
    /// proof. Existing fixed-storage and opaque-row checks remain mandatory.
    pub(super) fn stored_symbolic_member(
        &self,
        snapshot: &CopyValueSnapshot,
        member: &Value,
        identity: &MemberIdentity<'_>,
    ) -> Check {
        require(
            std::ptr::eq(snapshot, identity.snapshot) && std::ptr::eq(member, identity.member),
            "symbolic member borrowed another object's header proof or frozen value occurrence",
        )?;
        require(
            identity.entry_epoch <= self.facts.allocation_history.len(),
            "symbolic member has no registered frozen entry epoch",
        )?;
        require(
            self.normalized_key(identity.header, &identity.scope)? == identity.key,
            "symbolic member descriptor no longer matches its genuine source header",
        )?;
        self.ty_matches(&member.ty, &identity.key, &identity.scope, 0)?;
        self.storage_shape(snapshot, member, &identity.key, 0)?;
        self.symbolic_member_sources(snapshot, member)?;
        if let Some(witness) = &member.source_type_witness {
            require(
                witness.validate_closed()
                    && self.normalized_key(&witness.syntax, &BoundScope::default())?
                        == identity.key,
                "symbolic member replaced an existing complete closed identity",
            )?;
        }
        if let ArgumentKey::Callable {
            parameters,
            result,
            annotations,
        } = &identity.key
        {
            let actual = member.signature.as_ref().ok_or_else(|| {
                "symbolic callable member has no actual received signature".to_owned()
            })?;
            require(
                actual.len() == parameters.len(),
                "symbolic callable member changed its actual parameter arity",
            )?;
            for (actual, (mode, key)) in actual.iter().zip(parameters) {
                let syntax = actual.ty.as_ref().ok_or_else(|| {
                    "symbolic callable member parameter lacks complete source syntax".to_owned()
                })?;
                require(
                    actual.mode == *mode && self.normalized_key(syntax, &identity.scope)? == *key,
                    "symbolic callable member changed a mode or genuine U coordinate",
                )?;
            }
            require(
                member.callable_returns.iter().any(|returned| {
                    !returned.raw
                        && returned.typing_environment.generic_context == identity.scope.types
                        && returned.typing_environment.bound_row_context == identity.scope.rows
                        && returned.callables == member.callables
                        && self
                            .ty_matches(&returned.target, result, &identity.scope, 0)
                            .is_ok()
                        && self
                            .normalized_key(&returned.syntax, &identity.scope)
                            .is_ok_and(|key| key == **result)
                }),
                "symbolic callable return needs its actual original scoped descriptor",
            )?;
            if !annotations.is_empty() {
                require(
                    member.callable_bounds.iter().any(|bound| {
                        bound.span == identity.header.span
                            && bound
                                .annotations
                                .iter()
                                .map(|annotation| annotation.text.replace(' ', ""))
                                .eq(annotations.iter().cloned())
                    }),
                    "symbolic callable qualification lacks its original received bound descriptor",
                )?;
            }
        }
        Ok(())
    }
}
