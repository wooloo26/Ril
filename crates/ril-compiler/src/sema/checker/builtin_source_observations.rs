//! Original builtin contracts are minted once, then attached to the actual
//! paired expression emission. Neither a reused Cause nor a current Builtin
//! tag can create another observation.
use super::*;
use crate::sema::{builtin_sources::BuiltinSourceObservation, effect_identity::InvocationContext};

#[path = "builtin_source_validation.rs"]
mod validation;
pub(crate) use validation::actual_prelude_name;
pub(crate) use validation::validate;

pub(crate) fn original_canonical_key(
    facts: &SemanticFacts,
    value: &Value,
    actual: &Expr,
    context: InvocationContext,
) -> Option<crate::sema::effect_identity::ArgumentKey> {
    validation::original_canonical_key(facts, value, actual, context)
}

struct Pending {
    context: InvocationContext,
    span: Span,
    contract: builtin_source_types::Contract,
}

#[derive(Default)]
pub(super) struct State {
    pending: BTreeMap<u32, Pending>,
    observations: Vec<BuiltinSourceObservation>,
}

impl State {
    pub(super) fn into_observations(self) -> Vec<BuiltinSourceObservation> {
        self.observations
    }
}

impl Checker {
    /// Original direct leaf only. The index is recovered from the unique
    /// physical observation and full Value, never from a current builtin tag.
    pub(super) fn original_canonical_builtin_source_key(
        &self,
        value: &Value,
        actual: &Expr,
        frame: &Frame,
    ) -> Option<crate::sema::effect_identity::ArgumentKey> {
        let context = self.invocation_context(frame.callable_owner);
        let name = match &actual.kind {
            ExprKind::Name(name) => name.clone(),
            ExprKind::Path(path) => path.join("::"),
            _ => return None,
        };
        if !value.sources.is_empty() {
            return None;
        }
        let mut matching = self
            .builtin_sources
            .observations
            .iter()
            .filter(|observation| {
                observation.context == context
                    && observation.identity == name
                    && observation.cause == value.cause
                    && self
                        .expression_facts
                        .get(observation.expression)
                        .is_some_and(|fact| fact.span == actual.span && fact.value == *value)
                    && self
                        .invocation_expressions
                        .get(observation.expression)
                        .is_some_and(|row| {
                            row.expression == observation.expression && row.context == context
                        })
            });
        let observation = matching.next()?;
        if matching.next().is_some() {
            return None;
        }
        // Normalize only against the canonical builtin data schemas, not a
        // caller's local aliases. Keep all original annotations in the key.
        let syntax = super::source_types::expand_builtin_source_syntax(
            &BTreeMap::new(),
            &observation.full_header,
            0,
        )?;
        let key = crate::static_eval::effects::bounded_argument_key(&syntax, &BTreeMap::new())?;
        crate::sema::source_reception::complete(&key, &mut 4096)?;
        Some(key)
    }

    pub(super) fn mark_canonical_builtin_source(
        &mut self,
        name: &str,
        value: &Value,
        span: Span,
        frame: &Frame,
    ) {
        if self.operations.contains_key(name)
            || !matches!(value.callables.as_slice(), [Callable::Builtin(actual)] if actual == name)
        {
            return;
        }
        let Some(contract) = builtin_source_types::contract(name, span) else {
            return;
        };
        let expected_effects = BTreeSet::from(["Fiber".to_owned()]);
        let expected_writes = BTreeSet::from([0]);
        let Some(summary) = self.probe_canonical_builtin_summary(value, &contract.source, span)
        else {
            self.unsupported(
                span,
                "canonical builtin source has no completed original latent summary",
            );
            return;
        };
        if summary.effects != expected_effects
            || summary.concrete_effects != expected_effects
            || summary.written_formals != expected_writes
            || !summary.captures.is_empty()
        {
            self.unsupported(
                span,
                "canonical builtin original header differs from its actual latent summary",
            );
            return;
        }
        let context = self.invocation_context(frame.callable_owner);
        self.builtin_sources.pending.insert(
            value.cause.0,
            Pending {
                context,
                span,
                contract,
            },
        );
    }

    pub(super) fn record_builtin_source_observation(
        &mut self,
        expr: &Expr,
        value: &Value,
        expression: usize,
        frame: &Frame,
    ) {
        let Some(pending) = self.builtin_sources.pending.remove(&value.cause.0) else {
            return;
        };
        let context = self.invocation_context(frame.callable_owner);
        let name = match &expr.kind {
            ExprKind::Name(name) => name.clone(),
            ExprKind::Path(path) => path.join("::"),
            _ => return,
        };
        let TypeKind::Callable { parameters, .. } = &pending.contract.source.kind else {
            return;
        };
        if pending.context != context
            || pending.span != expr.span
            || name != pending.contract.identity.name()
            || value.signature.as_ref() != Some(parameters)
            || !matches!(value.callables.as_slice(), [Callable::Builtin(actual)] if actual == &name)
            || !self
                .expression_facts
                .get(expression)
                .is_some_and(|fact| fact.span == expr.span && fact.value == *value)
            || !self
                .invocation_expressions
                .get(expression)
                .is_some_and(|fact| fact.expression == expression && fact.context == context)
        {
            self.unsupported(
                expr.span,
                "canonical builtin source lost its original physical Name emission",
            );
            return;
        }
        self.builtin_sources
            .observations
            .push(BuiltinSourceObservation {
                expression,
                context,
                identity: name,
                full_header: pending.contract.source,
                concrete_effects: pending
                    .contract
                    .effects
                    .into_iter()
                    .map(|effect| match effect {
                        builtin_source_types::SystemEffect::Fiber => "Fiber".to_owned(),
                    })
                    .collect(),
                written_formals: pending.contract.written_formals.into_iter().collect(),
                captures: pending.contract.captures,
                cause: value.cause,
            });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn physical_builtin_observations_require_reverse_coverage_and_unchanged_contracts() {
        let source = "fn example(){let read:fn(mut File::Handle,int)->Result<Io::ReadChunk,Io::IoError>=File::read_chunk;let write:fn(mut File::Handle,bytes)->Io::WriteProgress=File::write;let wait:fn(mut Process::Child)->Result<Process::ExitStatus,Process::ProcessError>=Process::wait;let terminate:fn(mut Process::Child)->Result<(),Process::ProcessError>=Process::terminate}";
        let verified = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap_or_else(|outcome| panic!("{outcome:?}"));
        let original = verified.facts();
        assert_eq!(
            original
                .builtin_source_observations
                .iter()
                .map(|observation| observation.identity.as_str())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([
                "File::read_chunk",
                "File::write",
                "Process::wait",
                "Process::terminate"
            ])
        );
        assert!(validate(original).is_ok());
        for mutation in 0..7 {
            let mut changed = original.clone();
            match mutation {
                0 => changed.builtin_source_observations.clear(),
                1 => {
                    changed.builtin_source_observations[0]
                        .context
                        .budget_validation = !changed.builtin_source_observations[0]
                        .context
                        .budget_validation;
                }
                2 => {
                    let TypeKind::Callable { annotations, .. } =
                        &mut changed.builtin_source_observations[0].full_header.kind
                    else {
                        panic!("canonical contract must be Fn")
                    };
                    annotations.clear();
                }
                3 => changed.builtin_source_observations[0]
                    .concrete_effects
                    .clear(),
                4 => changed.builtin_source_observations[0]
                    .written_formals
                    .clear(),
                5 => {
                    changed.builtin_source_observations[0].expression =
                        changed.builtin_source_observations[1].expression;
                }
                6 => changed.source_program = None,
                _ => unreachable!(),
            }
            assert!(
                validate(&changed).is_err(),
                "physical builtin mutation {mutation} erased a required Source proof"
            );
        }
    }
}
