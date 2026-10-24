//! Original builtin contracts are minted once, then attached to the actual
//! paired expression emission. Neither a reused Cause nor a current Builtin
//! tag can create another observation.
use super::*;
use crate::sema::builtin_sources::BuiltinDeclaration;
use crate::sema::{builtin_sources::BuiltinSourceObservation, effect_identity::InvocationContext};

struct Pending {
    context: InvocationContext,
    span: Span,
    contract: builtin_source_types::Contract,
    environment: crate::sema::context::FrozenEnvironment,
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
    pub(super) fn numeric_builtin_observation(
        &self,
        expression: usize,
        context: InvocationContext,
        work: &mut crate::sema::source_types::WorkLimit,
    ) -> Result<
        Option<ril_compiler_core::numeric_builtins::NumericBuiltin>,
        crate::sema::source_types::SourceTypesError,
    > {
        use crate::sema::source_types::SourceTypesError;
        let actual = self
            .application_effect
            .expressions
            .get(expression)
            .ok_or(SourceTypesError::MissingNode)?;
        work.charge(self.builtin_sources.observations.len())?;
        let mut matches = self
            .builtin_sources
            .observations
            .iter()
            .filter(|row| row.expression == expression);
        let Some(row) = matches.next() else {
            return Ok(None);
        };
        let BuiltinDeclaration::Numeric(id) = row.full_header else {
            return Ok(None);
        };
        if matches.next().is_some()
            || row.context != context
            || row.identity != id.name()
            || row.cause != actual.value.cause
            || !crate::sema::builtin_sources::is_catalog_environment(&row.environment)
            || !row.concrete_effects.is_empty()
            || !row.written_formals.is_empty()
            || !row.captures.is_empty()
            || actual.value.ty != Ty::Unknown
            || actual.value.signature.is_some()
            || !actual.value.sources.is_empty()
            || !matches!(actual.value.callables.as_slice(), [Callable::Builtin(name)] if name == id.name())
        {
            return Err(SourceTypesError::Unresolved);
        }
        Ok(Some(id))
    }
    /// Original direct leaf only. The index is recovered from the unique
    /// physical observation and full Value, never from a current builtin tag.
    pub(super) fn original_canonical_builtin_source_schema(
        &self,
        value: &Value,
        actual: &Expr,
        frame: &Frame,
        actual_observation: Option<usize>,
        work: &mut crate::sema::source_types::WorkLimit,
    ) -> Result<
        Option<(
            crate::sema::source_types::SourceSchema,
            crate::sema::context::FrozenEnvironment,
        )>,
        crate::sema::source_types::SourceTypesError,
    > {
        use crate::sema::source_types::SourceTypesError;
        let context = self.invocation_context(frame.callable_owner);
        let name = match &actual.kind {
            ExprKind::Name(name) => {
                work.text(name)?;
                name.clone()
            }
            ExprKind::Path(path) => {
                work.charge(path.len())?;
                for part in path {
                    work.text(part)?;
                }
                path.join("::")
            }
            _ => return Ok(None),
        };
        if !value.sources.is_empty() {
            return Ok(None);
        }
        work.charge(
            (1 + name.len().div_ceil(32))
                .saturating_mul(1 + self.operations.len().checked_ilog2().unwrap_or(0) as usize),
        )?;
        if self.operations.contains_key(&name) {
            return Ok(None);
        }
        let Some(contract) = builtin_source_types::contract(&name, actual.span) else {
            return Ok(None);
        };
        let actual_observation = actual_observation.ok_or(SourceTypesError::MissingNode)?;
        work.charge(self.builtin_sources.observations.len())?;
        let mut matching = self
            .builtin_sources
            .observations
            .iter()
            .filter(|observation| observation.expression == actual_observation);
        let Some(observation) = matching.next() else {
            return Err(SourceTypesError::MissingNode);
        };
        if matching.next().is_some()
            || observation.context != context
            || observation.identity != name
            || observation.cause != value.cause
            || observation.full_header != contract.source
            || !self
                .application_effect
                .expressions
                .get(actual_observation)
                .is_some_and(|fact| fact.source_id.is_some() && fact.source_id == actual.hir_id)
            || !self
                .application_effect
                .evaluations
                .get(actual_observation)
                .is_some_and(|record| {
                    record.id.0 as usize == actual_observation
                        && record.context == context
                        && record
                            .identity
                            .is_some_and(|identity| Some(identity.source) == actual.hir_id)
                })
        {
            return Err(SourceTypesError::Unresolved);
        }
        work.charge(8)?;
        if !crate::sema::builtin_sources::is_catalog_environment(&observation.environment) {
            return Err(SourceTypesError::Unresolved);
        }
        let before = work.remaining();
        let mut remaining = before;
        let agrees = crate::sema::evaluated::same_birth_value(
            &self.application_effect.expressions[actual_observation].value,
            value,
            &mut remaining,
        );
        work.charge(before - remaining)?;
        if !agrees? {
            return Err(SourceTypesError::Unresolved);
        }
        // Normalize only against the canonical builtin data schemas, not a
        // caller's local aliases. Keep all original annotations in the key.
        builtin_source_types::source_schema(&observation.full_header, actual.hir_id, work)
            .map(|schema| schema.map(|schema| (schema, observation.environment.clone())))
    }

    pub(super) fn mark_canonical_builtin_source(
        &mut self,
        name: &str,
        value: &mut Value,
        span: Span,
        frame: &Frame,
    ) {
        if self.operations.contains_key(name) {
            return;
        }
        let Some(contract) = builtin_source_types::contract(name, span) else {
            return;
        };
        if matches!(
            contract.identity,
            builtin_source_types::Identity::Constant(_)
                | builtin_source_types::Identity::Nullary(_)
        ) {
            if !value.callables.is_empty() {
                return;
            }
        } else {
            if !matches!(value.callables.as_slice(), [Callable::Builtin(actual)] if contract.identity.matches_name(actual))
            {
                return;
            }
            let expected_effects = contract
                .effects
                .iter()
                .map(|effect| match effect {
                    builtin_source_types::SystemEffect::Fiber => "Fiber".to_owned(),
                })
                .collect::<BTreeSet<_>>();
            let expected_writes = contract
                .written_formals
                .iter()
                .copied()
                .collect::<BTreeSet<_>>();
            // An unapplied universal declaration has no invented concrete
            // arguments. Its closed primitive contract is instantiated only
            // when a full receiving Source selects one of its alternatives.
            let summary = contract
                .source
                .syntax()
                .map(|source| self.probe_canonical_builtin_summary(value, source, span));
            if let Some(summary) = summary {
                let Some(summary) = summary else {
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
            }
        }
        if matches!(
            contract.identity,
            builtin_source_types::Identity::Closed(_) | builtin_source_types::Identity::Constant(_)
        ) {
            value.source_type_witness = contract
                .source
                .syntax()
                .and_then(|source| self.source_type_from_frozen_syntax(source));
            if value.source_type_witness.is_none() {
                self.unsupported(
                    span,
                    "canonical builtin reference lost its original source declaration",
                );
            }
        }
        let context = self.invocation_context(frame.callable_owner);
        self.builtin_sources.pending.insert(
            value.cause.0,
            Pending {
                context,
                span,
                contract,
                environment: crate::sema::builtin_sources::catalog_environment().clone(),
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
        let original_declaration = match &pending.contract.source {
            BuiltinDeclaration::Nullary(id) => {
                builtin_source_types::nullary_descriptor(*id, value, &mut 4096).unwrap_or(false)
            }
            BuiltinDeclaration::Numeric(id) => {
                value.signature.is_none()
                    && value.ty == Ty::Unknown
                    && matches!(value.callables.as_slice(), [Callable::Builtin(actual)] if actual == id.name())
            }
            BuiltinDeclaration::Generic(id) => {
                value.signature.is_none()
                    && value.ty == Ty::Unknown
                    && matches!(value.callables.as_slice(), [Callable::Builtin(actual)] if actual == id.name())
            }
            BuiltinDeclaration::Syntax(TypeExpr {
                kind: TypeKind::Callable { parameters, .. },
                ..
            }) => {
                value
                    .signature
                    .as_ref()
                    .map(|signature| &signature.parameters)
                    == Some(parameters)
                    && matches!(value.callables.as_slice(), [Callable::Builtin(actual)] if pending.contract.identity.matches_name(actual))
            }
            BuiltinDeclaration::Syntax(_)
                if matches!(
                    pending.contract.identity,
                    builtin_source_types::Identity::Constant(_)
                ) =>
            {
                value.signature.is_none()
                    && value.callables.is_empty()
                    && standard::constant_ty(&name).as_ref() == Some(&value.ty)
            }
            _ => false,
        };
        if pending.context != context
            || pending.span != expr.span
            || !pending.contract.identity.matches_name(&name)
            || !original_declaration
            || !crate::sema::builtin_sources::is_catalog_environment(&pending.environment)
            || !self
                .application_effect
                .expressions
                .get(expression)
                .is_some_and(|fact| {
                    fact.source_id.is_some()
                        && fact.source_id == expr.hir_id
                        && fact.value == *value
                })
            || !self
                .application_effect
                .contexts
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
                environment: pending.environment,
                concrete_effects: pending
                    .contract
                    .effects
                    .iter()
                    .map(|effect| match effect {
                        builtin_source_types::SystemEffect::Fiber => "Fiber".to_owned(),
                    })
                    .collect(),
                written_formals: pending.contract.written_formals.iter().copied().collect(),
                captures: pending.contract.captures,
                cause: value.cause,
            });
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn actual_effect_declarations_keep_their_source_when_they_shadow_a_catalog_name() {
        let case = "tests/regressions/builtin-source.ril::shadowed-effect-declaration";
        for target in ["pointer32", "pointer64"] {
            let verified = crate::Session::with_options(
                ril_test::case_bytes(case).to_vec(),
                crate::CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|failure| panic!("{case} on {target}: {failure:?}"));
            let facts = verified.facts();
            let declaration = facts
                .source_program
                .as_ref()
                .unwrap()
                .statements
                .iter()
                .find_map(|statement| match &statement.kind {
                    ril_syntax::ast::StmtKind::Effect(effect)
                        if effect
                            .operations
                            .iter()
                            .any(|operation| operation.name == "from_string") =>
                    {
                        statement.hir_id
                    }
                    _ => None,
                })
                .expect("the corpus declares the shadowing effect");
            assert!(facts.operations.values().any(|operation| {
                operation
                    .source
                    .as_ref()
                    .is_some_and(|source| source.effect == declaration && source.index == 0)
            }));
            assert!(
                facts
                    .builtin_source_observations
                    .iter()
                    .all(|row| row.identity != "Path::from_string"),
                "an actual effect operation must retain its own declaration rather than a catalog receipt"
            );
        }
    }
}
