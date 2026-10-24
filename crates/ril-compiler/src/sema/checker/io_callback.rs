//! Stream helpers repeatedly invoke the operation supplied in the ordinary
//! record. The record never substitutes a trusted empty callback footprint.
use super::*;
use crate::sema::{
    application_effect::{EntryOrigin, InputOrigin, ScalarInput},
    evaluated::{CurrentValueStep, catalog_callable_bound, read_handle},
    source_types::{SourceTypesError, projection_receipts::ProjectionOccurrence},
};
use std::sync::Arc;

struct CallbackPackets {
    origin: EntryOrigin,
    field: &'static str,
    operations: Arc<EvaluatedValue>,
    callee: Arc<EvaluatedValue>,
}

impl Checker {
    fn generated_callback_packets(
        &mut self,
        read: bool,
        frame: &Frame,
    ) -> Result<CallbackPackets, SourceTypesError> {
        use crate::hir::nodes::{ExprKind, RecordMember};
        use ril_compiler_core::ids::EvaluationOccurrenceId;

        // This borrows the recorder's existing allowance. In particular the
        // original child lookup never gets a fresh quota after another probe.
        let mut lease = self.application_effect.lease_work(4_000_000);
        let selected = (|| {
            let work = lease.work();
            work.charge(10 + self.call_arguments.len())?;
            let anchor = self
                .application_effect
                .current_activation()
                .ok_or(SourceTypesError::MissingNode)?;
            let event = self
                .application_effect
                .current_call_event()
                .ok_or(SourceTypesError::MissingNode)?;
            let mut rows = self
                .call_arguments
                .iter()
                .filter(|row| row.source_event == event);
            let row = rows.next().ok_or(SourceTypesError::MissingNode)?;
            if rows.next().is_some() {
                return Err(SourceTypesError::Unresolved);
            }
            let operation = self
                .copy_call_events
                .get(event.0 as usize)
                .and_then(|event| event.callee_expression)
                .ok_or(SourceTypesError::MissingNode)?;
            let [Callable::Builtin(name)] = self
                .application_effect
                .expressions
                .get(operation)
                .ok_or(SourceTypesError::MissingNode)?
                .value
                .callables
                .as_slice()
            else {
                return Err(SourceTypesError::Unresolved);
            };
            work.text(name)?;
            let contract = crate::sema::application_effect::record_callback(name)
                .ok_or(SourceTypesError::Unresolved)?;
            if (contract.field == "read") != read {
                return Err(SourceTypesError::Unresolved);
            }
            let supplied = |slot| {
                row.supplied
                    .get(&slot)
                    .map(|input| input.expression)
                    .ok_or(SourceTypesError::MissingNode)
            };
            work.charge(3 + row.supplied.len())?;
            let receiver = supplied(contract.receiver)?;
            let operations = supplied(contract.operations)?;
            let fact = self
                .application_effect
                .expressions
                .get(operations)
                .ok_or(SourceTypesError::MissingNode)?;
            let record = self
                .application_effect
                .evaluations
                .get(operations)
                .ok_or(SourceTypesError::MissingNode)?;
            let source = fact.source_id.ok_or(SourceTypesError::MissingNode)?;
            let identity = record.identity.ok_or(SourceTypesError::MissingNode)?;
            if identity.source != source
                || record.context != self.invocation_context(frame.callable_owner)
            {
                return Err(SourceTypesError::Unresolved);
            }
            let ExprKind::Record { members, .. } = &self
                .semantic_hir
                .expression(source)
                .ok_or(SourceTypesError::MissingNode)?
                .kind
            else {
                return Err(SourceTypesError::MissingProjection);
            };
            work.charge(members.len())?;
            let mut field = None;
            for member in members {
                let RecordMember::Field { name, value, .. } = member else {
                    return Err(SourceTypesError::MissingProjection);
                };
                work.text(name)?;
                if name == contract.field && field.replace(*value).is_some() {
                    return Err(SourceTypesError::DuplicateField);
                }
            }
            let callee = self.source_projection_receipts().child_observation(
                ProjectionOccurrence {
                    identity,
                    context: record.context,
                    cause: fact.value.cause,
                },
                field.ok_or(SourceTypesError::MissingProjection)?,
                work,
            )?;
            let occurrence = |index| {
                u32::try_from(index)
                    .map(EvaluationOccurrenceId)
                    .map_err(|_| SourceTypesError::IdentityExhausted)
            };
            let scalar = match contract.scalar_source {
                crate::sema::application_effect::ScalarSource::PositiveInt => {
                    ScalarInput::PositiveInt
                }
                crate::sema::application_effect::ScalarSource::ByteSuffix(slot) => {
                    ScalarInput::ByteSuffix(occurrence(supplied(slot)?)?)
                }
                crate::sema::application_effect::ScalarSource::BufferedBytes(slot) => {
                    ScalarInput::BufferedBytes(occurrence(supplied(slot)?)?)
                }
            };
            work.charge(3)?;
            Ok((
                EntryOrigin::Generated {
                    anchor,
                    callee,
                    inputs: vec![
                        InputOrigin::Widened(occurrence(receiver)?),
                        InputOrigin::Scalar(scalar),
                    ],
                },
                event,
                contract.operations,
                contract.field,
                operations,
                callee,
            ))
        })();
        let returned = self.application_effect.return_work(lease);
        let (origin, _, _, field, operations, callee) = selected?;
        returned?;
        let operations = self.application_effect.packet_at(operations)?;
        let callee = self.application_effect.packet_at(callee.0 as usize)?;
        Ok(CallbackPackets {
            origin,
            field,
            operations,
            callee,
        })
    }

    fn read_callback_operations(
        &mut self,
        operations: &Arc<EvaluatedValue>,
        span: Span,
    ) -> Result<Arc<EvaluatedValue>, SourceTypesError> {
        if !self.application_effect.admit(1) {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let operations = self
            .freeze_entry_callee(Some(operations.clone()), span)?
            .ok_or(SourceTypesError::MissingNode)?;
        let mut value = self.read_evaluation_packet(&operations, span)?;
        read_handle(&mut value);
        self.derive_callback_current(operations, CurrentValueStep::ReadHandle, value)
    }

    fn derive_record_callback(
        &mut self,
        prepared: &CallbackPackets,
        operations: Arc<EvaluatedValue>,
        callback: Value,
        span: Span,
    ) -> Result<Arc<EvaluatedValue>, SourceTypesError> {
        if !self.application_effect.admit(2 + prepared.field.len()) {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let input = self
            .freeze_entry_callee(Some(prepared.callee.clone()), span)?
            .ok_or(SourceTypesError::MissingNode)?;
        let field = Slot::Field(prepared.field.into());
        let projected = self.derive_callback_current(
            input,
            CurrentValueStep::FieldProjection {
                receiver: operations,
                slot: field,
            },
            callback,
        )?;
        let mut value = self.read_evaluation_packet(&projected, span)?;
        // The bound contributes one vector entry, its annotation and text,
        // plus the shared catalog environment handle; it is never a probe.
        if !self.application_effect.admit(9 + prepared.field.len()) {
            return Err(SourceTypesError::BudgetExceeded);
        }
        value.callable_bounds.push(catalog_callable_bound(span));
        self.derive_callback_current(projected, CurrentValueStep::CatalogCallableBound, value)
    }

    fn derive_callback_current(
        &mut self,
        input: Arc<EvaluatedValue>,
        step: CurrentValueStep,
        value: Value,
    ) -> Result<Arc<EvaluatedValue>, SourceTypesError> {
        let types = self.type_source.storage.live_types_mut();
        self.application_effect.with_work(|work| {
            *work = work
                .checked_sub(1)
                .ok_or(SourceTypesError::BudgetExceeded)?;
            EvaluatedValue::derive_current(input, step, value, types, work).map(Arc::new)
        })
    }

    pub(super) fn io_all(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let read = name == "Io::read_all";
        let count = if read { 2 } else { 3 };
        if args.len() != count {
            self.error("E0314", span, "stream helper argument count mismatch", []);
            return self.unit(span);
        }
        for (index, (mode, value, argument)) in args.iter().enumerate() {
            let expected = if index == 0 {
                ParameterMode::Mut
            } else {
                ParameterMode::Read
            };
            if *mode != expected {
                self.error(
                    "E0405",
                    *argument,
                    "stream helper receiver uses mut and remaining arguments use read reception",
                    [value.cause],
                );
            }
        }
        let receiver = &args[0].1;
        if receiver.permission != Permission::Write {
            self.error(
                "E0520",
                args[0].2,
                "stream helper requires a writable receiver",
                [receiver.cause],
            );
        }
        let receiver_ty = self.collection_type(receiver);
        let Some(receiver_syntax) = super::io_types::receiver_type(receiver, &receiver_ty, span)
        else {
            self.unsupported(
                span,
                "stream receiver needs a complete data schema preserving its type identity",
            );
            return self.unit(span);
        };
        // Source identity supplies the declaration schema. Actual storage must
        // independently satisfy it before repeated scalar-array widening; this
        // preserves an existing fixed scratch proof across callback summaries.
        let shape_diagnostics = self.diagnostics.len();
        let shape_unknown = self.unsupported.len();
        self.check_storage_shape(receiver, &receiver_syntax, frame);
        if self.unsupported.len() != shape_unknown
            || self.diagnostics[shape_diagnostics..]
                .iter()
                .any(|diagnostic| diagnostic.severity == Severity::Error)
        {
            return self.unit(span);
        }
        let syntax = TypeExpr {
            hir_id: None,
            text: String::new(),
            kind: TypeKind::Name {
                path: vec![
                    "Io".into(),
                    if read { "ReadOps" } else { "WriteOps" }.into(),
                ],
                arguments: vec![receiver_syntax],
            },
            span,
        };
        let prepared = match self.generated_callback_packets(read, frame) {
            Ok(prepared) => prepared,
            Err(error) => {
                self.unsupported(
                    span,
                    format!("stream callback lost its physical inputs: {error}"),
                );
                return self.unit(span);
            }
        };
        let operations = match self.read_callback_operations(&prepared.operations, span) {
            Ok(operations) => operations,
            Err(error) => {
                self.unsupported(span, format!("stream read-handle derivation: {error}"));
                return self.unit(span);
            }
        };
        let expected = self.ty(&syntax);
        self.require_type(operations.value(), &expected, args[count - 1].2);
        let callback = self.project(
            operations.value(),
            Slot::Field(if read { "read" } else { "write" }.into()),
            span,
            frame,
            true,
        );
        // This is the standard operation's constraint on its actual generated
        // invocation. The declaration is a catalog contract, not a hypothetical
        // call whose formals can be manufactured from the receiver's shape.
        let callback = match self.derive_record_callback(&prepared, operations, callback, span) {
            Ok(callback) => callback,
            Err(error) => {
                self.unsupported(span, format!("stream field/capability derivation: {error}"));
                return self.unit(span);
            }
        };
        match callback.value().signature.as_ref() {
            Some(parameters) if parameters.len() == 2 => {
                if parameters[0].mode != ParameterMode::Mut
                    || parameters[1].mode != ParameterMode::Read
                {
                    self.error(
                        "E0407",
                        args[count - 1].2,
                        "stream operation parameter modes must be temporary mut followed by read",
                        [callback.value().cause],
                    );
                }
            }
            _ => self.unsupported(
                span,
                "stream operation needs a complete two-parameter temporary-mut callable signature",
            ),
        }
        let input = if read {
            Value::scalar(
                Ty::Int("int".into()),
                None,
                self.cause(
                    CauseKind::Source,
                    span,
                    "positive internal stream read request",
                    [],
                ),
            )
        } else {
            self.require_type(&args[1].1, &Ty::Bytes, args[1].2);
            // Later writes receive a remaining suffix, with unknown contents.
            Value::scalar(Ty::Bytes, None, args[1].1.cause)
        };
        let mut borrowed = receiver.clone();
        borrowed.temporary = true;
        let receiver_graph = self.heap.reachable(borrowed.origins.nodes.iter().copied());
        self.summarize_repeated_scalar_arrays(&receiver_graph);
        let mut invocation = vec![
            (ParameterMode::Mut, borrowed, args[0].2),
            (ParameterMode::Read, input, span),
        ];
        let repeated = self.begin_repeated_callback(&mut invocation, frame);
        let family = self.begin_loop_results(frame.owner);
        let output = self.invoke_generated_arguments_from(
            callback,
            invocation,
            span,
            frame,
            prepared.origin,
        );
        if output.ty == Ty::Never {
            let mut iteration = self.unit(span);
            self.finish_loop_results(
                family,
                &mut iteration,
                frame,
                span,
                &Block {
                    statements: vec![],
                    where_items: vec![],
                    span,
                },
            );
            self.finish_repeated_callback(repeated, span);
            return output;
        }
        let error_ty = self.ty(&TypeExpr {
            hir_id: None,
            text: "Io::IoError".into(),
            kind: TypeKind::Name {
                path: vec!["Io".into(), "IoError".into()],
                arguments: vec![],
            },
            span,
        });
        let (tag, error) = if read {
            let chunk = self.ty(&TypeExpr {
                hir_id: None,
                text: "Io::ReadChunk".into(),
                kind: TypeKind::Name {
                    path: vec!["Io".into(), "ReadChunk".into()],
                    arguments: vec![],
                },
                span,
            });
            self.require_type(
                &output,
                &Ty::Result(Box::new(chunk), Box::new(error_ty.clone())),
                span,
            );
            self.inspect_result(&output);
            let error = if output.result_tag == Some(true) {
                None
            } else {
                Some(self.result_payload(&output, false, span, frame))
            };
            (output.result_tag, error)
        } else {
            let progress = self.ty(&TypeExpr {
                hir_id: None,
                text: "Io::WriteProgress".into(),
                kind: TypeKind::Name {
                    path: vec!["Io".into(), "WriteProgress".into()],
                    arguments: vec![],
                },
                span,
            });
            self.require_type(&output, &progress, span);
            let error = self.project(&output, Slot::Field("error".into()), span, frame, true);
            let tag = error.option_tag.map(|present| !present);
            let payload = if error.option_tag == Some(false) {
                None
            } else {
                Some(self.optional_payload(&error, error_ty.clone()))
            };
            (tag, payload)
        };
        let mut iteration = self.unit(span);
        self.finish_guaranteed_callback_results(
            family,
            &mut iteration,
            frame,
            span,
            &Block {
                statements: vec![],
                where_items: vec![],
                span,
            },
        );
        self.finish_repeated_callback(repeated, span);
        let success = if read {
            Value::scalar(Ty::Bytes, None, output.cause)
        } else {
            self.unit(span)
        };
        self.io_result(success, error, error_ty, tag, span, frame.owner)
    }

    fn io_result(
        &mut self,
        success: Value,
        error: Option<Value>,
        error_ty: Ty,
        tag: Option<bool>,
        span: Span,
        owner: ScopeId,
    ) -> Value {
        if tag == Some(false)
            && let Some(error) = error.clone()
        {
            let mut value = self.make_result(false, error, span, owner);
            value.ty = Ty::Result(Box::new(success.ty), Box::new(error_ty));
            return value;
        }
        let mut value = self.make_result(true, success, span, owner);
        let Ty::Result(ok, _) = value.ty.clone() else {
            unreachable!()
        };
        value.ty = Ty::Result(ok, Box::new(error_ty));
        if tag == Some(true) {
            return value;
        }
        let Some(error) = error else {
            self.unsupported(
                span,
                "unknown stream result requires a witnessed error branch",
            );
            return value;
        };
        let mut failed = error.clone();
        failed.ty = value.ty.clone();
        failed.constant = None;
        failed.option_tag = None;
        failed.option_identity = None;
        failed.option_payload = None;
        failed.variant_tag = None;
        failed.variant_payload = None;
        failed.variant_witnesses.clear();
        failed.callables.clear();
        failed.signature = None;
        failed.callable_bounds.clear();
        failed.callable_returns.clear();
        failed.static_coordinate = None;
        failed.unsuffixed_numeric = false;
        failed.literal_number = false;
        failed.result_tag = Some(false);
        failed.result_success = None;
        failed.result_error = Some(Box::new(error.clone()));
        failed.result_payload = Some(Box::new(error));
        failed.outer_results = value.outer_results.clone();
        failed.must_outer_results = value.must_outer_results.clone();
        failed.results.extend(&value.outer_results);
        failed.must_results.extend(&value.must_outer_results);
        let cause = self.cause(
            CauseKind::BranchJoin,
            span,
            "stream helper returns one inspected-operation outcome with a new Result producer",
            [value.cause, failed.cause],
        );
        value.join(&failed, self.choice(), cause)
    }
}
