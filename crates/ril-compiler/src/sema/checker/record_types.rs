//! Record types are composed from the packets actually evaluated by construction.
//! Spread operands keep their complete fields and row tails; no extent, callable
//! contract or generic identity is inferred from the stored heap contents.
use super::*;
use crate::sema::{
    context::FrozenEnvironment,
    evaluated::{CapturedSource, CheckedSource, SourceRef},
    source_types::{SourceSchema, SourceTypesError},
};

impl Checker {
    pub(super) fn record_result_type(
        &mut self,
        explicit: &BTreeMap<String, EvaluatedValue>,
        spreads: &[EvaluatedValue],
        receiving: Option<&crate::sema::source_reception::Target>,
        span: Span,
    ) -> CheckedSource {
        let fallback = self.capture_typing_environment();
        let mut lease = self.application_effect.lease_work(65536);
        let result = (|| {
            let work = lease.work();
            let modes = receiving
                .and_then(|target| target.schema.as_ref())
                .map(|schema| match schema.record_parts(work) {
                    Ok(parts) => Ok(parts),
                    // An opaque receiving type supplies no structural slot
                    // modes. Keep the actual record graph for normal checking.
                    Err(SourceTypesError::Unresolved) => Ok(None),
                    Err(error) => Err(error),
                })
                .transpose()?
                .flatten()
                .map(|(fields, _)| {
                    fields
                        .into_iter()
                        .map(|(label, mutable, _)| (label, mutable))
                        .collect::<BTreeMap<_, _>>()
                })
                .unwrap_or_default();
            let mut fields = BTreeMap::<String, (bool, SourceSchema, FrozenEnvironment)>::new();
            let mut tail: Option<(SourceSchema, FrozenEnvironment)> = None;
            for spread in spreads {
                let Some((schema, environment)) = self.owned_result_type(spread, work)? else {
                    return Ok(None);
                };
                let parts = match schema.record_parts(work) {
                    Ok(parts) => parts,
                    Err(SourceTypesError::Unresolved) => return Ok(None),
                    Err(error) => return Err(error),
                };
                let Some((parts, row)) = parts else {
                    return Ok(None);
                };
                for (label, mutable, schema) in parts {
                    if !explicit.contains_key(&label) {
                        let mode = modes.get(&label).copied().unwrap_or(mutable);
                        fields.insert(label, (mode, schema, environment.clone()));
                    }
                }
                if let Some(row) = row {
                    if let Some((previous, context)) = &tail {
                        if !previous.equivalent_in(&row, context, &environment, work)? {
                            return Ok(None);
                        }
                    } else {
                        tail = Some((row, environment));
                    }
                }
            }
            for (label, packet) in explicit {
                let Some((schema, environment)) = self.owned_result_type(packet, work)? else {
                    return Ok(None);
                };
                fields.insert(
                    label.clone(),
                    (
                        modes.get(label).copied().unwrap_or(false),
                        schema,
                        environment,
                    ),
                );
            }
            let environment = super::boundary_results::result_environment(
                fields
                    .values()
                    .map(|(_, schema, context)| (schema, context))
                    .chain(tail.iter().map(|(schema, context)| (schema, context))),
                &fallback,
                work,
            )?;
            let fields = fields
                .into_iter()
                .map(|(label, (mutable, schema, _))| (label, mutable, schema))
                .collect::<Vec<_>>();
            SourceSchema::record(&fields, tail.as_ref().map(|(schema, _)| schema), None, work)
                .map(|schema| Some((schema, environment)))
        })();
        let returned = self.application_effect.return_work(lease);
        let result = result.and_then(|result| returned.map(|()| result));
        if let Err(error) = &result {
            self.unsupported(
                span,
                format!("record type composition is incomplete: {error}"),
            );
        }
        result
    }

    pub(super) fn finish_record_type(
        &mut self,
        value: Value,
        source: CheckedSource,
        expression: &Expr,
        declared: Option<&crate::sema::source_reception::Target>,
        valid: bool,
    ) -> EvaluatedValue {
        let mut packet = EvaluatedValue::unobserved(value, self.recency_moves.len(), valid);
        let mut lease = self.application_effect.lease_work(32768);
        let captured = (|| {
            let source = match source? {
                Some((schema, environment)) => {
                    if let Some(target) = declared {
                        let expected =
                            target.schema.as_ref().ok_or(SourceTypesError::Unresolved)?;
                        // New slots take their declared modes. Only explicitly
                        // written children supply construction context; spread
                        // values keep their already selected inner types.
                        let (parts, _) = schema
                            .record_parts(lease.work())?
                            .ok_or(SourceTypesError::Unresolved)?;
                        let mut fields = parts
                            .into_iter()
                            .map(|(label, _, _)| {
                                (label, crate::sema::source_reception::Construction::Opaque)
                            })
                            .collect::<BTreeMap<_, _>>();
                        if let ExprKind::Record { members, .. } = &expression.kind {
                            for member in members {
                                if let RecordMember::Field(field) = member {
                                    let mut remaining = lease.work().remaining();
                                    let context = crate::sema::source_reception::construction(
                                        &field.value,
                                        &mut remaining,
                                    )
                                    .ok_or(SourceTypesError::BudgetExceeded)?;
                                    let cost = lease.work().remaining() - remaining;
                                    lease.work().charge(cost)?;
                                    fields.insert(field.name.clone(), context);
                                }
                            }
                        }
                        let fresh = crate::sema::source_reception::Construction::Record(fields);
                        if !expected.receive_schema(&schema, Some(&fresh), lease.work())? {
                            self.error(
                                "E0301",
                                expression.span,
                                "record fields do not fit the complete declared type",
                                [packet.value.cause],
                            );
                            packet.source_valid = false;
                        } else if packet.source_valid {
                            return SourceRef::intern(
                                expected,
                                target.environment.clone(),
                                self.type_source.storage.live_types_mut(),
                                lease.work(),
                            )
                            .map(CapturedSource::Known);
                        }
                    }
                    SourceRef::intern(
                        &schema,
                        environment,
                        self.type_source.storage.live_types_mut(),
                        lease.work(),
                    )
                    .map(CapturedSource::Known)?
                }
                None => {
                    if declared.is_some_and(|target| {
                        target.sensitivity
                            != crate::sema::source_reception::SchemaSensitivity::NotRequired
                    }) {
                        return Err(SourceTypesError::Unresolved);
                    }
                    CapturedSource::Unknown(self.freeze_evaluation_environment(lease.work())?)
                }
            };
            Ok(source)
        })();
        let returned = self.application_effect.return_work(lease);
        match captured
            .and_then(|source| returned.map(|()| source))
            .and_then(|source| packet.set_current_type(source))
        {
            Ok(()) => {}
            Err(error) => {
                self.unsupported(
                    expression.span,
                    format!("record result type is unavailable: {error}"),
                );
                packet.fail_current_source(error);
            }
        }
        packet
    }
}
