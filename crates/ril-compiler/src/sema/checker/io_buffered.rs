//! Buffered streams borrow both their buffer and the actual receiver. The
//! supplied operation keeps its transitive contract even on a buffered hit.
use super::*;

impl Checker {
    pub(super) fn io_buffered(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let read = name == "Io::read_buffered";
        let flush = name == "Io::flush";
        if args.len() != if flush { 3 } else { 4 } {
            self.error("E0314", span, "buffered stream argument count mismatch", []);
            return self.unit(span);
        }
        for (index, (mode, value, argument_span)) in args.iter().enumerate() {
            let expected = if index < 2 {
                ParameterMode::Mut
            } else {
                ParameterMode::Read
            };
            if *mode != expected {
                self.error(
                    "E0405",
                    *argument_span,
                    "buffer and receiver require temporary mut reception",
                    [value.cause],
                );
            }
            if index < 2 && value.permission != Permission::Write {
                self.error(
                    "E0520",
                    *argument_span,
                    "buffered stream receiver is read-only",
                    [value.cause],
                );
            }
        }
        let buffer_ty = Ty::Named(
            if read {
                "Io::ReadBuffer"
            } else {
                "Io::WriteBuffer"
            }
            .into(),
        );
        self.require_type(&args[0].1, &buffer_ty, args[0].2);
        let buffer_region = self.heap.reachable(args[0].1.origins.nodes.iter().copied());
        let receiver_region = self.heap.reachable(args[1].1.origins.nodes.iter().copied());
        if !self.nodes_disjoint(&buffer_region, &receiver_region) {
            self.error(
                "E0523",
                span,
                "buffer and receiver temporary regions must be disjoint",
                [args[0].1.cause, args[1].1.cause],
            );
        }
        self.access(&args[0].1, None, Mode::Write, args[0].2, frame);
        if !flush {
            self.require_type(
                &args[3].1,
                &if read {
                    Ty::Int("int".into())
                } else {
                    Ty::Bytes
                },
                args[3].2,
            );
        }
        let mut invocation = vec![args[1].clone()];
        if !read {
            invocation.push((
                ParameterMode::Read,
                Value::scalar(Ty::Bytes, None, args[0].1.cause),
                span,
            ));
        }
        invocation.push(args[2].clone());
        let before = self.snapshot_flow();
        let recency = self.recency_moves.len();
        let accesses_before = frame.obligations.accesses.len();
        let mut result = self.io_all(
            if read {
                "Io::read_all"
            } else {
                "Io::write_all"
            },
            &invocation,
            span,
            frame,
        );
        let mut buffer = args[0].1.origins.clone();
        for &(recent, older) in &self.recency_moves[recency..] {
            buffer.remap(recent, older);
        }
        for access in self.current_accesses(&frame.obligations.accesses[accesses_before..]) {
            if !self.origins_disjoint(&buffer, &access.origins) {
                self.error(
                    "E0523",
                    access.span,
                    "buffer operation and receiver callback access overlapping temporary regions",
                    [args[0].1.cause, access.cause],
                );
                break;
            }
        }
        // The receiver operation can be skipped because the buffer satisfies
        // the request. It can also be invoked repeatedly on a miss or flush.
        let skipped = self.unit(span);
        let executed = if result.ty == Ty::Never {
            result.clone()
        } else {
            self.unit(span)
        };
        let _ = self.conditional_flow(&before, &skipped, &executed, None, span);
        let error_ty = self.buffered_type("Io::IoError", span);
        if result.ty == Ty::Never {
            let success = if read {
                let ty = self.buffered_type("Io::ReadChunk", span);
                self.standard_value(ty, span, frame.owner, 0x1040)
            } else {
                self.unit(span)
            };
            result = self.make_result(true, success, span, frame.owner);
            result.ty = Ty::Result(
                Box::new(if read {
                    self.buffered_type("Io::ReadChunk", span)
                } else {
                    Ty::Unit
                }),
                Box::new(error_ty.clone()),
            );
        }
        if !read && !flush {
            self.inspect_result(&result);
            let ty = self.buffered_type("Io::WriteProgress", span);
            return self.standard_value(ty, span, frame.owner, 0x1041);
        }
        if read {
            let ty = self.buffered_type("Io::ReadChunk", span);
            let payload = self.standard_value(ty.clone(), span, frame.owner, 0x1042);
            result.ty = Ty::Result(Box::new(ty), Box::new(error_ty.clone()));
            result.result_success = Some(Box::new(payload));
        }
        result.result_tag = None;
        result.result_payload = None;
        if result.result_error.is_none() {
            let error = self.standard_value(error_ty, span, frame.owner, 0x1043);
            result.result_error = Some(Box::new(error));
        }
        // read_all's success is bytes; this boundary instead returns a fresh
        // ReadChunk. Rebuild the wrapper's alternatives from its actual final
        // payloads. Extending only nodes would leave the old success/error
        // choice partition incomplete and could falsely prove correlations.
        let success = result
            .result_success
            .as_ref()
            .map(|value| value.origins.clone())
            .unwrap_or_default();
        let error = result
            .result_error
            .as_ref()
            .map(|value| value.origins.clone())
            .unwrap_or_default();
        result.origins = success.join(&error, self.choice());
        result
    }

    fn buffered_type(&mut self, name: &str, span: Span) -> Ty {
        self.ty(&TypeExpr {
            hir_id: None,
            text: name.into(),
            kind: TypeKind::Name {
                path: name.split("::").map(str::to_owned).collect(),
                arguments: vec![],
            },
            span,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const READER: &str = "type Reader={mut offset:int}\nfn read(mut reader:Reader,maximum:int)->Result<Io::ReadChunk,Io::IoError> &mut {reader.offset+=1;Ok(.{data:b\"x\",end:true})}\n";
    fn check(source: &str) -> crate::sema::AnalyzeOutcome {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        crate::sema::analyze(&parsed.program, FileId(0))
    }
    #[test]
    fn buffered_contracts_keep_actual_operation_and_result_obligations() {
        let result = check(&format!(
            "{READER}fn example(){{let mut reader=Reader.{{offset:0}};let mut buffer=Io::read_buffer(2);assert(Io::read_buffered(mut buffer,mut reader,.{{read:read}},1) is Ok(_))}}"
        ));
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        for (source, code) in [
            (
                format!(
                    "{READER}fn example(){{let mut reader=Reader.{{offset:0}};let mut buffer=Io::read_buffer(2);let _=Io::read_buffered(mut buffer,mut reader,.{{read:read}},1)}}"
                ),
                "E0720",
            ),
            (
                format!(
                    "{READER}fn example(){{let mut reader=Reader.{{offset:0}};let mut buffer=Io::read_buffer(2);assert(Io::read_buffered(buffer,mut reader,.{{read:read}},1) is Ok(_))}}"
                ),
                "E0405",
            ),
            (
                format!(
                    "{READER}fn overlapping(mut buffer:Io::ReadBuffer,maximum:int)->Result<Io::ReadChunk,Io::IoError> &mut {{let mut reader=Reader.{{offset:0}};Io::read_buffered(mut buffer,mut reader,.{{read:read}},maximum)}}\nfn example(){{let mut buffer=Io::read_buffer(2);assert(Io::read_buffered(mut buffer,mut buffer,.{{read:overlapping}},1) is Ok(_))}}"
                ),
                "E0523",
            ),
        ] {
            let result = check(&source);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "expected {code}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
}
