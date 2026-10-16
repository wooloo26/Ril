//! Stream helpers repeatedly invoke the operation supplied in the ordinary
//! record. The record never substitutes a trusted empty callback footprint.
use super::*;

impl Checker {
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
        let mut operations = args[count - 1].1.clone();
        operations.permission = Permission::Read;
        self.set_contract_environment(&frame.env);
        self.ascribe_signature(&mut operations, &syntax);
        let expected = self.ty(&syntax);
        self.require_type(&operations, &expected, args[count - 1].2);
        let callback = self.project(
            &operations,
            Slot::Field(if read { "read" } else { "write" }.into()),
            span,
            frame,
            true,
        );
        if callback.signature.as_ref().is_none_or(|parameters| {
            parameters.len() != 2
                || parameters[0].mode != ParameterMode::Mut
                || parameters[1].mode != ParameterMode::Read
        }) {
            self.unsupported(
                span,
                "stream operation needs a complete two-parameter temporary-mut callable signature",
            );
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
        let output = self.invoke(&callback, invocation, span, frame);
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
            text: "Io::IoError".into(),
            kind: TypeKind::Name {
                path: vec!["Io".into(), "IoError".into()],
                arguments: vec![],
            },
            span,
        });
        let (tag, error) = if read {
            let chunk = self.ty(&TypeExpr {
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
