//! Delimited results keep the actual value and its complete type together.
//! Receiving an abort answer constrains that packet; it does not execute or
//! manufacture the protected computation's normal result.
use super::*;
use crate::sema::{
    evaluated::{CapturedSource, SourceRef},
    source_reception,
    source_types::{SourceSchema, SourceSensitivity, SourceTypesError},
};

impl Checker {
    /// Exact compiler-defined types can be interned without any lost source
    /// coordinates. Arrays, callables, open rows, user names and inference
    /// variables deliberately have no such path.
    pub(super) fn complete_builtin_type_key(
        ty: &Ty,
        work: &mut crate::sema::source_types::WorkLimit,
    ) -> Result<Option<crate::sema::effect_identity::ArgumentKey>, SourceTypesError> {
        use crate::sema::{
            effect_identity::ArgumentKey as K,
            source_types::{legacy, standard_data},
        };
        fn walk(
            ty: &Ty,
            work: &mut crate::sema::source_types::WorkLimit,
            depth: usize,
        ) -> Result<Option<K>, SourceTypesError> {
            work.charge(1)?;
            if depth > 64 {
                return Err(SourceTypesError::BudgetExceeded);
            }
            let name = match ty {
                Ty::Unit => return Ok(Some(K::Tuple(vec![]))),
                Ty::Never => Some("never"),
                Ty::Bool => Some("bool"),
                Ty::Str => Some("str"),
                Ty::Bytes => Some("bytes"),
                Ty::Int(name) | Ty::Float(name) if legacy::scalar(name).is_some() => {
                    Some(name.as_str())
                }
                Ty::Named(name)
                    if standard_data::schema(name).is_some() || legacy::scalar(name).is_some() =>
                {
                    Some(name.as_str())
                }
                _ => None,
            };
            if let Some(name) = name {
                work.text(name)?;
                return Ok(Some(K::Name {
                    name: name.into(),
                    arguments: vec![],
                }));
            }
            let (name, children): (&str, Vec<&Ty>) = match ty {
                Ty::Immutable(inner) => ("Prelude::Immut", vec![inner]),
                Ty::Optional(inner) => ("Prelude::Option", vec![inner]),
                Ty::Result(ok, error) => ("Prelude::Result", vec![ok, error]),
                Ty::Set(inner) => ("Prelude::Set", vec![inner]),
                Ty::Range(inner) => ("Prelude::Range", vec![inner]),
                Ty::Applied {
                    constructor,
                    arguments,
                } if crate::sema::source_types::IntrinsicNominal::lookup(constructor).is_some() => {
                    let Some(arguments) = arguments
                        .iter()
                        .map(|argument| match argument {
                            TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. } => {
                                Some(ty.as_ref())
                            }
                            _ => None,
                        })
                        .collect::<Option<Vec<_>>>()
                    else {
                        return Ok(None);
                    };
                    (constructor, arguments)
                }
                Ty::Map(key, value) => ("", vec![key, value]),
                Ty::Tuple(items) => ("", items.iter().collect()),
                _ => return Ok(None),
            };
            work.charge(children.len())?;
            let mut arguments = Vec::with_capacity(children.len());
            for child in children {
                let Some(child) = walk(child, work, depth + 1)? else {
                    return Ok(None);
                };
                arguments.push(child);
            }
            Ok(Some(match ty {
                Ty::Tuple(_) => K::Tuple(arguments),
                Ty::Map(..) => {
                    let value = arguments.pop().unwrap();
                    let key = arguments.pop().unwrap();
                    K::Map {
                        key: Box::new(key),
                        value: Box::new(value),
                    }
                }
                _ => K::Name {
                    name: name.into(),
                    arguments,
                },
            }))
        }
        walk(ty, work, 0)
    }

    pub(super) fn record_received_type(
        &mut self,
        packet: &mut EvaluatedValue,
        target: &source_reception::Target,
        span: Span,
    ) {
        let Some(schema) = &target.schema else {
            return;
        };
        let mut lease = self.application_effect.lease_work(32768);
        let source = SourceRef::intern(
            schema,
            target.environment.clone(),
            self.type_source.storage.live_types_mut(),
            lease.work(),
        );
        let returned = self.application_effect.return_work(lease);
        if let Err(error) = source.and_then(|source| {
            returned?;
            packet.set_current_type(CapturedSource::Known(source))
        }) {
            self.unsupported(
                span,
                format!("received type could not be retained: {error}"),
            );
            packet.fail_current_source(error);
        }
    }

    pub(super) fn inherit_result_type(
        &mut self,
        output: &mut EvaluatedValue,
        input: &EvaluatedValue,
        span: Span,
    ) {
        let mut lease = self.application_effect.lease_work(32768);
        let source = (|| {
            let work = lease.work();
            match self.owned_result_type(input, work)? {
                Some((schema, environment)) => SourceRef::intern(
                    &schema,
                    environment,
                    self.type_source.storage.live_types_mut(),
                    work,
                )
                .map(CapturedSource::Known),
                None => self
                    .freeze_evaluation_environment(work)
                    .map(CapturedSource::Unknown),
            }
        })();
        let returned = self.application_effect.return_work(lease);
        let source = source.and_then(|source| returned.map(|()| source));
        match source.and_then(|source| output.set_current_type(source)) {
            Ok(()) => output.source_valid &= input.source_valid,
            Err(error) => {
                self.unsupported(
                    span,
                    format!("owned boundary result type is unavailable: {error}"),
                );
                output.fail_current_source(error);
            }
        }
    }

    pub(super) fn receive_boundary_type(
        &mut self,
        actual: &mut EvaluatedValue,
        normal: &mut EvaluatedValue,
        span: Span,
    ) -> bool {
        if actual.value.ty == Ty::Never {
            return true;
        }
        let mut lease = self.application_effect.lease_work(32768);
        let target = self.owned_result_type(normal, lease.work());
        let returned = self.application_effect.return_work(lease);
        match target.and_then(|target| returned.map(|()| target)) {
            Ok(Some((schema, environment))) => {
                self.receive_owned_type(actual, &normal.value.ty, &schema, &environment, span)
            }
            Ok(None) => {
                // A continuing constructor can still have inference variables
                // (for example Ok() beside an early Err). Use the other actual
                // exit's complete type as its receiving constraint.
                let mut lease = self.application_effect.lease_work(32768);
                let expected = join_type_holes(&normal.value.ty, &actual.value.ty);
                let source = (|| {
                    // Complementary scalar constructor holes can be solved
                    // without losing any source coordinates. Reference/array,
                    // callable and user nominal coordinates still require an
                    // owned graph from an actual exit.
                    if let Some(key) = Self::complete_builtin_type_key(&expected, lease.work())? {
                        return self.input_header_schema(
                            &key,
                            None,
                            self.capture_typing_environment(),
                            lease.work(),
                        );
                    }
                    self.owned_result_type(actual, lease.work())
                })();
                let returned = self.application_effect.return_work(lease);
                match source.and_then(|source| returned.map(|()| source)) {
                    Ok(Some((schema, environment))) => {
                        self.receive_owned_type(normal, &expected, &schema, &environment, span)
                            && self.receive_owned_type(
                                actual,
                                &expected,
                                &schema,
                                &environment,
                                span,
                            )
                    }
                    Ok(None) => {
                        self.unsupported(span, "boundary result types remain unresolved");
                        actual.source_valid = false;
                        false
                    }
                    Err(error) => {
                        self.unsupported(
                            span,
                            format!("boundary result type is unavailable: {error}"),
                        );
                        actual.fail_current_source(error);
                        false
                    }
                }
            }
            Err(error) => {
                self.unsupported(
                    span,
                    format!("normal boundary result type is unavailable: {error}"),
                );
                actual.fail_current_source(error);
                false
            }
        }
    }

    pub(super) fn receive_owned_type(
        &mut self,
        actual: &mut EvaluatedValue,
        expected: &Ty,
        schema: &SourceSchema,
        environment: &crate::sema::context::FrozenEnvironment,
        span: Span,
    ) -> bool {
        if actual.value.ty == Ty::Never {
            return true;
        }
        let errors = self.diagnostics.len();
        if self.select_numeric_packet(actual, expected, span).is_err() {
            return false;
        }
        self.require_type(&actual.value, expected, span);
        let mut lease = self.application_effect.lease_work(32768);
        let received = (|| {
            let work = lease.work();
            let compatible = match schema.sensitivity(work) {
                SourceSensitivity::Absent { .. } => true,
                _ => match self.owned_result_type(actual, work)? {
                    Some((source, source_environment)) => schema.receive_schema_in(
                        &source,
                        environment,
                        &source_environment,
                        Some(actual.fresh()),
                        work,
                    )?,
                    None => schema
                        .empty_context(actual.fresh(), work)?
                        .ok_or(SourceTypesError::Unresolved)?,
                },
            };
            if !compatible || self.diagnostics.len() != errors {
                return Ok(None);
            }
            SourceRef::intern(
                schema,
                environment.clone(),
                self.type_source.storage.live_types_mut(),
                work,
            )
            .map(Some)
        })();
        let returned = self.application_effect.return_work(lease);
        match received.and_then(|source| returned.map(|()| source)) {
            Ok(Some(source)) => {
                actual.value.ty = expected.clone();
                actual.value.requires_inference =
                    !self.pending_result_binders(&actual.value).is_empty();
                if let Err(error) = actual.set_current_type(CapturedSource::Known(source)) {
                    actual.fail_current_source(error);
                    return false;
                }
                actual.source_valid
            }
            Ok(None) => {
                if self.diagnostics.len() == errors {
                    self.error(
                        "E0301",
                        span,
                        "boundary answer does not fit its complete receiving type",
                        [actual.value.cause],
                    );
                }
                actual.source_valid = false;
                false
            }
            Err(error) => {
                self.unsupported(
                    span,
                    format!("boundary answer receiving is incomplete: {error}"),
                );
                actual.fail_current_source(error);
                false
            }
        }
    }

    pub(super) fn receive_boundary_target(
        &mut self,
        answer: &mut EvaluatedValue,
        expected: Option<&Ty>,
        target: &source_reception::Target,
        span: Span,
    ) {
        if answer.value.ty == Ty::Never {
            return;
        }
        if let Some(schema) = &target.schema {
            let expected = expected.unwrap_or(&answer.value.ty).clone();
            if self.receive_owned_type(answer, &expected, schema, &target.environment, span) {
                self.ascribe_received_signature(&mut answer.value, target);
            }
        } else if target.sensitivity != source_reception::SchemaSensitivity::NotRequired {
            self.unsupported(span, "boundary receiving target has no complete type");
            answer.source_valid = false;
        }
    }
}

pub(super) fn result_environment<'a>(
    parts: impl IntoIterator<
        Item = (
            &'a SourceSchema,
            &'a crate::sema::context::FrozenEnvironment,
        ),
    >,
    fallback: &crate::sema::context::FrozenEnvironment,
    work: &mut crate::sema::source_types::WorkLimit,
) -> Result<crate::sema::context::FrozenEnvironment, SourceTypesError> {
    if fallback.is_poisoned() {
        return Err(SourceTypesError::Unresolved);
    }
    let mut parts_owned = Vec::new();
    for (schema, environment) in parts {
        work.charge(1)?;
        if environment.is_poisoned() {
            return Err(SourceTypesError::Unresolved);
        }
        if schema.requires_environment(work)? {
            parts_owned.push((schema, environment));
        }
    }
    for candidate in
        std::iter::once(fallback).chain(parts_owned.iter().map(|(_, environment)| *environment))
    {
        let mut compatible = true;
        for (schema, environment) in &parts_owned {
            if !schema.same_interpretation_in(environment, candidate, work)? {
                compatible = false;
                break;
            }
        }
        if compatible {
            return Ok(candidate.clone());
        }
    }
    Err(SourceTypesError::Unresolved)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::source_types::WorkLimit;

    #[test]
    fn exact_intrinsic_types_never_reconstruct_erased_or_unresolved_coordinates() {
        let mut work = WorkLimit::new(4096);
        let int = Ty::Int("int".into());
        assert!(
            Checker::complete_builtin_type_key(
                &Ty::Result(Box::new(int.clone()), Box::new(Ty::Str)),
                &mut work
            )
            .unwrap()
            .is_some()
        );
        for ty in [
            Ty::Array(Box::new(int.clone())),
            Ty::Optional(Box::new(Ty::Array(Box::new(int.clone())))),
            Ty::Result(Box::new(int), Box::new(Ty::Unknown)),
            Ty::Named("UserNominal".into()),
            Ty::Generic("owner:T".into()),
            Ty::Callable(vec![], Box::new(Ty::Unit)),
        ] {
            assert!(
                Checker::complete_builtin_type_key(&ty, &mut work)
                    .unwrap()
                    .is_none(),
                "{ty:?}"
            );
        }
        assert!(Checker::complete_builtin_type_key(&Ty::Bool, &mut WorkLimit::new(0)).is_err());
    }
}
