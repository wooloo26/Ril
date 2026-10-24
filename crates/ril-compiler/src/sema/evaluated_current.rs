//! Derive the current value and type view once. The resulting value retains
//! its type reference, without storing a replay tree of earlier values.
use super::*;
use crate::sema::{
    facts::{Permission, Slot},
    model::CallableBound,
};
use ril_compiler_core::source::Span;
use ril_syntax::ast::{Annotation, AnnotationKind};

#[derive(Debug, Clone)]
pub(crate) enum CurrentValueStep {
    ReadHandle,
    FieldProjection {
        receiver: Arc<EvaluatedValue>,
        slot: Slot,
    },
    CatalogCallableBound,
}

impl EvaluatedValue {
    /// Called by a transfer, after its real input has been selected. Source is
    /// obtained from that input or receiver, never inferred from the output Ty.
    pub(crate) fn derive_current(
        input: Arc<Self>,
        step: CurrentValueStep,
        value: Value,
        types: &mut LiveSourceTypes,
        work: &mut usize,
    ) -> Result<Self, SourceTypesError> {
        *work = work
            .checked_sub(3)
            .ok_or(SourceTypesError::BudgetExceeded)?;
        let mut graph_work = WorkLimit::new(*work);
        let source = (|| {
            let input_source =
                input.current_source(SourceTypesRef::Live(types), &mut graph_work)?;
            let schema = input_source.schema.ok_or(SourceTypesError::Unresolved)?;
            let (schema, environment) = match &step {
                CurrentValueStep::FieldProjection { receiver, slot, .. } => {
                    if receiver.current_epoch() != input.current_epoch() {
                        return Err(SourceTypesError::Unresolved);
                    }
                    let receiver_source =
                        receiver.current_source(SourceTypesRef::Live(types), &mut graph_work)?;
                    let path = match slot {
                        Slot::Field(label) => {
                            graph_work.text(label)?;
                            crate::sema::source_types::SourcePath::Field(label.clone())
                        }
                        Slot::Tuple(index) => crate::sema::source_types::SourcePath::Tuple(*index),
                        _ => return Err(SourceTypesError::MissingProjection),
                    };
                    let projected = receiver_source
                        .schema
                        .ok_or(SourceTypesError::Unresolved)?
                        .project_steps(&[path], &mut graph_work)?;
                    if !projected.equivalent_in(
                        &schema,
                        &receiver_source.environment,
                        &input_source.environment,
                        &mut graph_work,
                    )? || (projected.requires_environment(&mut graph_work)?
                        && receiver_source.environment.id() != input_source.environment.id())
                    {
                        return Err(SourceTypesError::Unresolved);
                    }
                    (projected, receiver_source.environment)
                }
                _ => (schema, input_source.environment),
            };
            SourceRef::intern(&schema, environment, types, &mut graph_work)
        })();
        *work = graph_work.remaining();
        let source = source?;
        let recency = input.current_epoch();
        let source_valid = input.source_valid;
        let birth = input.birth.clone();
        Ok(Self {
            value,
            recency,
            source_valid,
            birth,
            current_source: CurrentSource::Derived(source),
        })
    }
}

pub(crate) fn catalog_callable_bound(span: Span) -> CallableBound {
    CallableBound {
        annotations: vec![Annotation {
            kind: AnnotationKind::Capability,
            text: "&mut".into(),
            span,
        }],
        source: None,
        typing_environment: crate::sema::builtin_sources::catalog_environment().clone(),
        span,
    }
}

/// Restrict the handle while preserving its identity, contents and duties.
pub(crate) fn read_handle(value: &mut Value) {
    value.permission = Permission::Read;
}
