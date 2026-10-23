//! Immutable optional constructor choices are separate from Result inspection.
//! A constructor choice proves presence only, never payload inspection.
use super::*;

impl Checker {
    pub(in crate::sema::checker) fn formal_channel_optional_graph(
        &mut self,
        ty: Ty,
        index: u32,
        span: Span,
        seen: &mut BTreeSet<String>,
    ) -> Value {
        let Ty::Optional(inner) = &ty else {
            return Value::scalar(
                ty,
                None,
                self.cause(CauseKind::Source, span, "unresolved optional input", []),
            );
        };
        if seen.len() >= 64 || !seen.insert(format!("incoming-optional:{ty:?}")) {
            let cause = self.cause(
                CauseKind::Source,
                span,
                "incomplete recursive optional input",
                [],
            );
            let mut value = if ty.scalar() {
                Value::scalar(ty, None, cause)
            } else {
                let node =
                    self.heap
                        .symbolic(Pivot(self.heap.nodes.len() as u32), ScopeId(0), cause);
                let mut value = Value::reference(ty, node, cause);
                value.permission = Permission::Read;
                value.publication = Publication::Live;
                value
            };
            value.construction = false;
            return value;
        }
        let payload = self.formal_value(*inner.clone(), index, span, seen);
        let mut value = self.standard_option(payload, None, span, ScopeId(u32::MAX));
        if seen.contains("\0optional-member-family") {
            value.option_identity = None;
        }
        value.ty = ty;
        value
    }

    pub(in crate::sema::checker) fn new_optional_identity(
        &mut self,
        payload_type: Ty,
        cause: CauseId,
        owner: ScopeId,
        span: Span,
    ) -> Option<ril_compiler_core::ids::OptionalTagId> {
        if self.optional_tags.len() >= 4096 {
            self.unsupported(span, "optional constructor identity work bound exceeded");
            return None;
        }
        let id = ril_compiler_core::ids::OptionalTagId(self.optional_tags.len() as u32);
        self.optional_tags
            .push(crate::sema::optional_tags::OptionalTagFact {
                id,
                creation_owner: owner,
                cause,
                payload_type,
            });
        Some(id)
    }

    pub(in crate::sema::checker) fn channel_optional_outcome(
        &self,
        value: &Value,
        present: bool,
    ) -> ChannelGuard {
        if let Some(known) = value.option_tag {
            return if known == present {
                ChannelGuard::always()
            } else {
                ChannelGuard::never()
            };
        }
        match value.option_identity {
            Some(identity) => ChannelGuard::literal(GuardLiteral::Optional { identity, present }),
            None if value.results.is_empty() => ChannelGuard::always(),
            None => ChannelGuard::unavailable(),
        }
    }

    pub(in crate::sema::checker) fn channel_assume_optional(
        &mut self,
        value: &Value,
        present: bool,
        pattern: Span,
        frame: &Frame,
    ) {
        self.channel_optional_tag_test(value, present, pattern, frame);
        let guard = self.channel_optional_outcome(value, present);
        if !self.concurrency.message_flow.select(&guard) {
            self.unsupported(
                pattern,
                "optional constructor selection needs its complete immutable tag identity",
            );
        }
    }

    pub(in crate::sema::checker) fn channel_optional_tag_test(
        &mut self,
        value: &Value,
        present: bool,
        pattern: Span,
        frame: &Frame,
    ) {
        // A tag test records which bit was tested. It never inspects the
        // business Result inside Some, including when the test succeeds.
        if value.option_identity.is_none() {
            return;
        }
        let Some(sequence) = self.channel_sequence(pattern) else {
            return;
        };
        use crate::sema::channel_messages::{ChannelAction, ChannelMessageFact};
        self.channel_message_facts.push(ChannelMessageFact {
            repetition: self.active_channel_repetitions.last().copied(),
            source_event: self.channel_source_event(frame),
            id: ChannelMessageId(self.channel_message_facts.len() as u32),
            sequence,
            context: self.invocation_context(frame.callable_owner),
            activation: frame.owner,
            span: pattern,
            cause: value.cause,
            allocation_epoch: self.recency_moves.len(),
            guard: self.concurrency.message_flow.guard(),
            task: self.concurrency.task_context.last().copied(),
            action: ChannelAction::TagTest {
                subject: self.channel_value_snapshot(value),
                success: present,
                pattern,
                producer_versions: self.channel_versions(value),
            },
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn optional_refinements_keep_the_created_choice_cause() {
        for source in [
            "fn example(value:?int){if value is Some(1){}else if value is Some(2){}}",
            "fn example(value:?(fn()->int))->int{(value ?? (\\->{return 1}))()}",
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            let mut checker = Checker::new(FileId(0));
            checker.run(&parsed.program);
            if std::env::var_os("RIL_OPTIONAL_CAUSES").is_some() {
                for tag in &checker.optional_tags {
                    println!("TAG {tag:?}");
                }
                for cause in &checker.explanations.causes {
                    println!("CAUSE {cause:?}");
                }
                for value in &checker.application_effect.expressions {
                    println!(
                        "EXPR {:?} {:?} {:?}",
                        value.span, value.value.option_identity, value.value.cause
                    );
                }
            }
            assert!(checker.diagnostics.is_empty(), "{:?}", checker.diagnostics);
            crate::Session::new(source.as_bytes().to_vec())
                .verify()
                .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
        }
    }
}
