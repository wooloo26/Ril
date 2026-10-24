//! Opaque standard data has explicit proof contracts; runtime availability is
//! never used as evidence for permissions, effects, or Result inspection.
use super::*;

pub(super) fn is_temporal_builtin(name: &str) -> bool {
    matches!(
        name,
        "Time::duration_nanos"
            | "Time::timestamp"
            | "Time::add"
            | "Time::elapsed"
            | "Time::monotonic"
            | "Time::sleep"
            | "Clock::now"
            | "Random::seeded"
            | "Random::next_u64"
            | "Random::below"
            | "Random::entropy"
            | "Test::assert_eq"
            | "Test::assert_ne"
    )
}
pub(super) fn temporal_constant(name: &str) -> Option<Ty> {
    matches!(
        name,
        "Time::TimeError::OutOfRange" | "Time::TimeError::DifferentClock"
    )
    .then(|| Ty::Named("Time::TimeError".into()))
}
pub(super) fn timestamp() -> Ty {
    Ty::Record(
        [
            ("seconds".into(), (false, integer("i64"))),
            ("nanos".into(), (false, integer("u32"))),
        ]
        .into(),
    )
}
fn io_error() -> Ty {
    Ty::Record(
        [
            ("kind".into(), (false, Ty::Named("Io::ErrorKind".into()))),
            ("message".into(), (false, Ty::Str)),
            (
                "native_code".into(),
                (false, Ty::Optional(Box::new(integer("i64")))),
            ),
        ]
        .into(),
    )
}

impl Checker {
    pub(super) fn standard_temporal_builtin(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        if !is_temporal_builtin(name) {
            return None;
        }
        if name.starts_with("Test::") {
            return Some(self.standard_test_helper(args, span, frame));
        }
        let duration = Ty::Named("Time::Duration".into());
        let instant = Ty::Named("Time::Instant".into());
        let rng = Ty::Named("Random::Rng".into());
        let error = Ty::Named("Time::TimeError".into());
        let inputs = match name {
            "Time::duration_nanos" => vec![integer("i64")],
            "Time::timestamp" => vec![integer("i64"), integer("u32")],
            "Time::add" => vec![timestamp(), duration.clone()],
            "Time::elapsed" => vec![instant.clone(), instant.clone()],
            "Time::sleep" => vec![duration.clone()],
            "Random::seeded" => vec![integer("u64")],
            "Random::next_u64" => vec![rng.clone()],
            "Random::below" => vec![rng.clone(), integer("u64")],
            "Random::entropy" => vec![integer("int")],
            _ => vec![],
        };
        let writes = matches!(name, "Random::next_u64" | "Random::below");
        if writes {
            if args.len() != inputs.len() {
                self.error("E0314", span, "wrong random argument count", []);
            }
            for (index, ((mode, value, argument_span), ty)) in args.iter().zip(&inputs).enumerate()
            {
                self.require_type(value, ty, *argument_span);
                if *mode
                    != if index == 0 {
                        ParameterMode::Mut
                    } else {
                        ParameterMode::Read
                    }
                {
                    self.error(
                        "E0405",
                        *argument_span,
                        "random argument mode mismatch",
                        [value.cause],
                    );
                }
                if index == 0 {
                    if value.permission != Permission::Write {
                        self.error(
                            "E0520",
                            *argument_span,
                            "random generator is read-only",
                            [value.cause],
                        );
                    }
                    self.access(value, None, Mode::Write, *argument_span, frame);
                }
            }
        } else {
            self.standard_arguments(name, args, &inputs, inputs.len(), span);
            for (_, value, argument_span) in args {
                if !value.origins.nodes.is_empty() {
                    self.access(value, None, Mode::Read, *argument_span, frame);
                }
            }
        }
        if matches!(
            name,
            "Time::monotonic" | "Time::sleep" | "Clock::now" | "Random::entropy"
        ) {
            frame.obligations.effects.insert("Fiber".into());
            frame.obligations.concrete_effects.insert("Fiber".into());
        }
        Some(match name {
            "Random::seeded" => self.standard_value(rng, span, frame.owner, 0),
            "Random::next_u64" | "Random::below" => {
                self.standard_value(integer("u64"), span, frame.owner, 0)
            }
            "Random::entropy" => self.standard_result(Ty::Bytes, io_error(), span, frame.owner),
            "Time::timestamp" | "Time::add" => {
                self.standard_result(timestamp(), error, span, frame.owner)
            }
            "Time::elapsed" => self.standard_result(duration, error, span, frame.owner),
            "Clock::now" => self.standard_value(timestamp(), span, frame.owner, 0),
            "Time::duration_nanos" | "Time::monotonic" => {
                let ty = if name == "Time::duration_nanos" {
                    duration
                } else {
                    instant
                };
                let cause = self.cause(CauseKind::Source, span, "opaque immutable time value", []);
                let mut value = Value::scalar(ty, None, cause);
                value.permission = Permission::Read;
                value.publication = Publication::Immutable;
                value
            }
            _ => self.unit(span),
        })
    }
    pub(super) fn standard_duration_inner(
        &mut self,
        value: &Value,
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        if self.expanded(&value.ty, &mut BTreeSet::new()) != Ty::Named("Time::Duration".into()) {
            return None;
        }
        if !value.origins.nodes.is_empty() {
            self.access(value, None, Mode::Read, span, frame);
        }
        let cause = self.cause(
            CauseKind::Projection,
            span,
            "Duration exposes signed nanoseconds",
            [value.cause],
        );
        Some(Value::scalar(integer("i64"), None, cause))
    }
    fn standard_test_helper(
        &mut self,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let minimum = 2;
        if !(minimum..=minimum + 1).contains(&args.len()) {
            self.error("E0314", span, "wrong testing helper argument count", []);
            return self.unit(span);
        }
        for (mode, value, argument_span) in args {
            if *mode != ParameterMode::Read {
                self.error(
                    "E0405",
                    *argument_span,
                    "testing helpers borrow read-only values",
                    [value.cause],
                );
            }
        }
        if let Some((_, message, message_span)) = args.get(minimum) {
            self.require_type(message, &Ty::Str, *message_span);
        }
        self.require_type(&args[1].1, &args[0].1.ty, args[1].2);
        for (_, value, argument_span) in &args[..2] {
            self.deep_read(value, *argument_span, frame);
            if self.contains_callable(value) || self.contains_resource(value) {
                self.error(
                    "E0327",
                    *argument_span,
                    "structural equality cannot contain callable values",
                    [value.cause],
                );
            }
            if unknown_type(&value.ty) || self.equality_has_generic(&value.ty) {
                self.unsupported(
                    *argument_span,
                    "testing equality requires proven constituent types",
                );
            }
        }
        self.unit(span)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn check(source: &str) -> crate::sema::AnalyzeOutcome {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        crate::sema::analyze(&parsed.program, FileId(0))
    }
    #[test]
    fn temporal_contracts_preserve_mutability_effects_and_inspection() {
        let good = check(
            "fn example() @Fiber { let mut rng=Random::seeded(0u64); let mut copy=clone(rng); assert(Random::next_u64(mut rng)==Random::next_u64(mut copy)); let a=Time::monotonic(); let b=Time::monotonic(); let d=Time::elapsed(a,b) ?? \\_error->panic(\"clock\"); assert(inner(d)>=0i64); assert(Random::entropy(0) is Ok(b\"\")); assert(Time::timestamp(0i64,0u32) is Ok(_)) }",
        );
        assert!(
            good.program.is_some(),
            "{:?} {:?}",
            good.diagnostics,
            good.unsupported
        );
        for (source, code) in [
            (
                "fn example(){let rng=Random::seeded(0u64);let _=Random::next_u64(mut rng)}",
                "E0520",
            ),
            (
                "fn example(){let mut rng=Random::seeded(0u64);let _=Random::next_u64(rng)}",
                "E0405",
            ),
            ("fn example(){let _=Time::timestamp(0i64,0u32)}", "E0720"),
            ("fn example() @{}{let _=Time::monotonic()}", "E0534"),
            ("fn example(){Test::assert_eq(\\->(),\\->())}", "E0327"),
            (
                ril_test::case_source(
                    "tests/regressions/stdlib-declarations.ril::reject-uninspected-nested-result-via-ok",
                ),
                "E0720",
            ),
        ] {
            let result = check(source);
            assert!(
                result.diagnostics.iter().any(|d| d.code == code),
                "expected {code}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
}
