//! Postfix propagation has a normal payload path and a distinct early-return
//! path. Only the failed wrapper is exported on that path.
use super::*;
impl Checker {
    pub(super) fn propagate_value(
        &mut self,
        input: EvaluatedValue,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let value = input.value.clone();
        if value.ty == Ty::Never {
            return value;
        }
        if frame.owner == ScopeId(0) {
            self.error(
                "E0205",
                span,
                "postfix propagation requires an enclosing callable",
                [value.cause],
            );
        }
        let source = self.expanded(&value.ty, &mut BTreeSet::new());
        let (success_ty, error_ty, tag) = match &source {
            Ty::Optional(inner) => (*inner.clone(), None, value.option_tag),
            Ty::Result(ok, error) => (*ok.clone(), Some(*error.clone()), value.result_tag),
            _ => {
                self.error(
                    "E0712",
                    span,
                    "postfix propagation requires Option or Result",
                    [value.cause],
                );
                return Value::scalar(Ty::Unknown, None, value.cause);
            }
        };
        let target = frame
            .expected_return
            .as_ref()
            .map(|ty| self.expanded(ty, &mut BTreeSet::new()));
        let valid = match (&source, &target) {
            (Ty::Optional(_), Some(Ty::Optional(_))) => true,
            (Ty::Result(_, error), Some(Ty::Result(_, expected))) => {
                self.compatible(error, expected)
            }
            _ => false,
        };
        if !valid {
            if frame.anonymous && target.is_none() {
                self.unsupported(
                    span,
                    "inferred anonymous propagation target requires an early-return type equation",
                );
            } else {
                self.error(
                    "E0713",
                    span,
                    "enclosing callable cannot return this propagation failure",
                    [value.cause],
                );
            }
        }
        if self
            .fallback_boundaries
            .iter()
            .any(|(owner, _)| *owner == frame.owner)
        {
            self.error(
                "E0710",
                span,
                "propagation escapes a fallback expression",
                [value.cause],
            );
        }
        if error_ty.is_some() {
            self.inspect_result(&value);
        }
        let transport = self.concurrent_transport(&value);
        let transport_payload = if transport {
            value
                .result_success
                .as_ref()
                .map(|payload| payload.results.clone())
                .unwrap_or_default()
        } else {
            BTreeSet::new()
        };
        if !transport
            && tag.is_none()
            && (!value.results.is_subset(&value.outer_results)
                || contains_result_type(&success_ty)
                || error_ty.as_ref().is_some_and(contains_result_type))
        {
            self.unsupported(span,"conditional propagation of nested Result duties requires tag-indexed early-exit coverage");
        }
        if tag.is_none()
            && frame.locals.iter().any(|id| {
                matches!(
                    self.bindings[*id].mode,
                    BindingMode::Scoped | BindingMode::ScopedMut
                ) && self.bindings[*id].alive
                    && !self.is_file_handle(&self.bindings[*id].value)
            })
        {
            self.unsupported(span,"conditional propagation must summarize the current cleanup callbacks at each early exit");
        }
        let channel_before = self.channel_save_flow();
        if matches!(source, Ty::Result(..)) {
            self.channel_assume_result(&value, false, span, frame);
        }
        let mut failure = if let Some(error_ty) = error_ty {
            let mut payload = self.result_payload(&value, false, span, frame);
            if payload.ty.scalar() {
                payload.origins = Origins::default();
            }
            if tag.is_none()
                && self.reference_bearing(&error_ty)
                && !(payload.construction || payload.publication == Publication::Immutable)
            {
                self.unsupported(span,"conditional reference error returns require a heap snapshot for the early exit");
            }
            let mut failure = payload.clone();
            failure.source_type_witness = None;
            failure.ty = Ty::Result(Box::new(Ty::Unknown), Box::new(error_ty));
            failure.result_error = Some(Box::new(payload.clone()));
            failure.result_success = None;
            failure.result_payload = Some(Box::new(payload));
            failure.result_tag = Some(false);
            failure.callables.clear();
            failure.signature = None;
            failure.callable_bounds.clear();
            failure.callable_returns.clear();
            failure.static_coordinate = None;
            failure.option_payload = None;
            failure.option_tag = None;
            failure.option_identity = None;
            failure.variant_payload = None;
            failure.variant_witnesses.clear();
            failure.variant_tag = None;
            failure.outer_results = value.outer_results.clone();
            failure.must_outer_results = value.must_outer_results.clone();
            failure.results.extend(&value.outer_results);
            failure.must_results.extend(&value.must_outer_results);
            failure.constant = None;
            failure
        } else {
            self.none_value(span)
        };
        failure.cause = self.cause(
            CauseKind::Call,
            span,
            "propagation failure exports only the failed wrapper and its actual payload",
            [value.cause],
        );
        if tag != Some(true) {
            self.channel_return_at(frame.owner, &failure);
            let outstanding: Vec<_> = self
                .result_duties
                .iter()
                .filter(|duty| {
                    if self.channel_known_producer(duty.id) {
                        return self.channel_obligations_complete()
                            && !self.channel_can_finish(duty.id, frame.owner);
                    }
                    duty.owner == frame.owner
                        && !duty.covered
                        && !duty.abnormal
                        && !failure.must_results.contains(&duty.id)
                        && !transport_payload.contains(&duty.id)
                })
                .cloned()
                .collect();
            for duty in outstanding {
                self.error(
                    "E0720",
                    duty.span,
                    "a propagation failure can leave this Result uninspected and unreturned",
                    [duty.cause, value.cause],
                );
            }
            if tag == Some(false) {
                if matches!(source, Ty::Optional(_)) {
                    self.discharge_absent_results(&value, span);
                }
                self.return_results(&failure);
            }
            let dormant: Vec<_> = transport_payload
                .iter()
                .map(|id| (*id, self.result_duties[*id as usize].abnormal))
                .collect();
            for (id, _) in &dormant {
                self.result_duties[*id as usize].abnormal = true;
            }
            self.record_result_return(frame.owner, &failure);
            for (id, abnormal) in dormant {
                self.result_duties[id as usize].abnormal = abnormal;
            }
            let packet =
                self.propagation_return_packet(failure.clone(), &input, frame, valid, span);
            frame.returned.push(packet);
        }
        if tag == Some(false) {
            failure.ty = Ty::Never;
            return failure;
        }
        self.channel_restore_flow(channel_before);
        if matches!(source, Ty::Result(..)) {
            self.channel_assume_result(&value, true, span, frame);
        }
        let mut payload = if matches!(source, Ty::Result(..)) {
            self.result_payload(&value, true, span, frame)
        } else {
            self.optional_payload(&value, success_ty.clone())
        };
        payload.ty = success_ty;
        if payload.ty.scalar() {
            payload.origins = Origins::default();
            payload.participants.clear();
            payload.temporary = false;
            payload.scoped.clear();
        }
        payload.cause = self.cause(
            CauseKind::Projection,
            span,
            "normal propagation path preserves the success payload access permissions",
            [value.cause],
        );
        payload
    }
    fn propagation_return_packet(
        &mut self,
        failure: Value,
        input: &EvaluatedValue,
        frame: &Frame,
        valid: bool,
        span: Span,
    ) -> EvaluatedValue {
        use crate::sema::{
            evaluated::{CapturedSource, SourceRef},
            source_types::{SourcePath, SourceSensitivity, SourceTypesError},
        };
        let mut packet = EvaluatedValue::unobserved(failure, self.recency_moves.len(), valid);
        let Some(target) = frame.expected_return_source.as_ref().filter(|_| valid) else {
            return packet;
        };
        let Some(schema) = &target.schema else {
            return packet;
        };
        let mut lease = self.application_effect.lease_work(32768);
        let received = (|| {
            let work = lease.work();
            if matches!(packet.value.ty, Ty::Result(..)) {
                let expected_error = schema.project_steps(&[SourcePath::ResultError], work)?;
                if !matches!(
                    expected_error.sensitivity(work),
                    SourceSensitivity::Absent { .. }
                ) {
                    let (actual, environment) = self
                        .owned_result_type(input, work)?
                        .ok_or(SourceTypesError::Unresolved)?;
                    let error = actual.project_steps(&[SourcePath::ResultError], work)?;
                    if !expected_error.receive_schema_in(
                        &error,
                        &target.environment,
                        &environment,
                        None,
                        work,
                    )? {
                        return Ok(None);
                    }
                }
            }
            SourceRef::intern(
                schema,
                target.environment.clone(),
                self.type_source.storage.live_types_mut(),
                work,
            )
            .map(Some)
        })();
        let returned = self.application_effect.return_work(lease);
        match received.and_then(|source| returned.map(|()| source)) {
            Ok(Some(source)) => {
                if let Some(expected) = &frame.expected_return {
                    packet.value.ty = expected.clone();
                }
                if let Err(error) = packet.set_current_type(CapturedSource::Known(source)) {
                    packet.fail_current_source(error);
                }
            }
            Ok(None) => {
                self.error(
                    "E0301",
                    span,
                    "propagated error does not fit the complete return error type",
                    [packet.value.cause],
                );
                packet.source_valid = false;
            }
            Err(error) => {
                self.unsupported(
                    span,
                    format!("propagation return type is incomplete: {error}"),
                );
                packet.fail_current_source(error);
            }
        }
        packet
    }
}
fn contains_result_type(ty: &Ty) -> bool {
    match ty {
        Ty::Result(..) | Ty::Projection { .. } => true,
        Ty::Optional(inner)
        | Ty::Immutable(inner)
        | Ty::Array(inner)
        | Ty::Set(inner)
        | Ty::Range(inner) => contains_result_type(inner),
        Ty::Tuple(items) => items.iter().any(contains_result_type),
        Ty::Record(fields) => fields.values().any(|(_, ty)| contains_result_type(ty)),
        Ty::Map(key, value) => contains_result_type(key) || contains_result_type(value),
        Ty::Generic(_) => true,
        _ => false,
    }
}
