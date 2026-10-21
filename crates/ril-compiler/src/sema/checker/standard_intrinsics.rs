//! Fixed data-producing declarations use one source graph for their signatures
//! and every produced payload. No erased runtime shape defines a source view.
use super::*;
use crate::sema::source_types::{
    SourceTypeQueries, WorkLimit,
    builtins::{self, BuiltinId, Schema},
};

pub(super) fn callable_signature(name: &str, span: Span) -> Option<(Ty, Vec<Parameter>)> {
    let definition = BuiltinId::lookup(name)?.definition();
    let mut work = WorkLimit::new(4096);
    let graph = definition.graph(&mut work).ok()?;
    let ty = builtins::erased_type(&graph.types, graph.root, &mut work).ok()?;
    let TypeKind::Callable { parameters, .. } = definition.syntax(span, &mut work).ok()?.kind
    else {
        return None;
    };
    Some((ty, parameters))
}

pub(super) fn constant_type(name: &str) -> Option<Ty> {
    let mut work = WorkLimit::new(4096);
    let (types, root) = builtins::constant(name)?.graph(&mut work).ok()?;
    builtins::erased_type(&types, root, &mut work).ok()
}

impl Checker {
    pub(in crate::sema::checker) fn standard_intrinsic_constant(
        &mut self,
        name: &str,
        span: Span,
        frame: &Frame,
    ) -> Option<Value> {
        let schema = builtins::constant(name)?;
        let mut work = WorkLimit::new(4096);
        let (types, root) = schema.graph(&mut work).ok()?;
        let ty = builtins::erased_type(&types, root, &mut work).ok()?;
        let cause = self.cause(
            CauseKind::Source,
            span,
            "canonical standard data constant",
            [],
        );
        let mut value = Value::scalar(ty, None, cause);
        self.attach_intrinsic_source(&mut value, schema, span, &mut work);
        self.mark_canonical_builtin_source(name, &mut value, span, frame);
        Some(value)
    }

    pub(super) fn standard_intrinsic_builtin(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        let definition = BuiltinId::lookup(name)?.definition();
        if definition.implementation == builtins::Implementation::Dedicated {
            return None;
        }
        let result = (|| {
            let mut work = WorkLimit::new(4096);
            let graph = definition.graph(&mut work).ok()?;
            work.charge(graph.parameters.len()).ok()?;
            let inputs = graph
                .parameters
                .iter()
                .map(|&id| builtins::erased_type(&graph.types, id, &mut work))
                .collect::<Result<Vec<_>, _>>()
                .ok()?;
            self.standard_arguments(name, args, &inputs, inputs.len(), span);
            for (_, value, actual_span) in args {
                if definition.deep {
                    self.deep_read(value, *actual_span, frame);
                } else if !value.ty.scalar() {
                    self.access(value, None, Mode::Read, *actual_span, frame);
                }
            }
            self.intrinsic_value(
                &graph.types,
                graph.result,
                definition.output,
                span,
                frame.owner,
                0,
                &mut work,
            )
        })();
        Some(result.unwrap_or_else(|| {
            self.unsupported(
                span,
                "canonical builtin source graph or value projection exhausted its work bound",
            );
            self.unit(span)
        }))
    }

    pub(super) fn attach_intrinsic_source(
        &mut self,
        value: &mut Value,
        schema: Schema,
        span: Span,
        work: &mut WorkLimit,
    ) {
        let syntax = schema.syntax(span, work).ok();
        value.source_type_witness = syntax
            .as_ref()
            .and_then(|syntax| self.source_type_from_frozen_syntax(syntax));
        if value.source_type_witness.is_none() {
            self.unsupported(
                span,
                "canonical builtin declaration lost its complete original source schema",
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn intrinsic_value(
        &mut self,
        types: &crate::sema::source_types::SourceTypes,
        id: crate::sema::source_types::SourceTypeId,
        schema: Schema,
        span: Span,
        owner: ScopeId,
        discriminator: u32,
        work: &mut WorkLimit,
    ) -> Option<Value> {
        work.charge(1).ok()?;
        let ty = builtins::erased_type(types, id, work).ok()?;
        let mut value = match schema {
            Schema::Nominal(_) | Schema::Tuple(_) | Schema::Record(_) => return None,
            Schema::Scalar(_) => self.standard_value(ty, span, owner, discriminator),
            Schema::Array(_) => {
                let Ty::Array(element) = ty else { return None };
                let mut value = self.standard_array(*element, span, owner);
                // These closed declarations produce ordinary immutable native
                // snapshots. The source schema grants no mutation authority.
                value.permission = Permission::Read;
                value.publication = Publication::Immutable;
                value.construction = false;
                value
            }
            Schema::Optional(element) => {
                let child = types
                    .project(
                        id,
                        &[crate::sema::source_types::SourcePath::OptionalPayload],
                        work,
                    )
                    .ok()?;
                let payload = self.intrinsic_value(
                    types,
                    child,
                    *element,
                    span,
                    owner,
                    discriminator + 1,
                    work,
                )?;
                self.standard_option(payload, None, span, owner)
            }
            Schema::Result(ok, error) => {
                let success_id = types
                    .project(
                        id,
                        &[crate::sema::source_types::SourcePath::ResultSuccess],
                        work,
                    )
                    .ok()?;
                let error_id = types
                    .project(
                        id,
                        &[crate::sema::source_types::SourcePath::ResultError],
                        work,
                    )
                    .ok()?;
                let payload = self.intrinsic_value(
                    types,
                    success_id,
                    *ok,
                    span,
                    owner,
                    discriminator + 1,
                    work,
                )?;
                let error = self.intrinsic_value(
                    types,
                    error_id,
                    *error,
                    span,
                    owner,
                    discriminator + 2,
                    work,
                )?;
                let mut value = self.make_result(true, payload.clone(), span, owner);
                value.origins = payload.origins.join(&error.origins, self.choice());
                value.result_error = Some(Box::new(error));
                value.ty = ty;
                value.result_tag = None;
                value.result_payload = None;
                value
            }
        };
        self.attach_intrinsic_source(&mut value, schema, span, work);
        Some(value)
    }
}
