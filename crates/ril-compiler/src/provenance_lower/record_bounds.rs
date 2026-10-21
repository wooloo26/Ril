//! Preserve scoped structural constraints without making symbolic keys closed.
use super::*;
use crate::sema::record_bounds as b;
use std::collections::BTreeMap;

fn scope(value: &b::BoundScope) -> p::BoundScope {
    p::BoundScope {
        types: value.types.clone(),
        rows: value.rows.clone(),
    }
}

pub(super) fn key(value: &crate::sema::effect_identity::ArgumentKey) -> p::RecordBoundKey {
    use crate::sema::effect_identity::ArgumentKey as K;
    use p::RecordBoundKey as O;
    match value {
        K::GenericBuiltin(id) => O::GenericBuiltin(*id),
        K::Closed(value) => O::Closed(value.clone()),
        K::Binder { identity, .. } => O::Binder {
            identity: identity.clone(),
        },
        K::Name { name, arguments } => O::Name {
            name: name.clone(),
            arguments: arguments.iter().map(key).collect(),
        },
        K::Array { length, element } => O::Array {
            length: length.clone(),
            element: Box::new(key(element)),
        },
        K::Map {
            key: map_key,
            value,
        } => O::Map {
            key: Box::new(key(map_key)),
            value: Box::new(key(value)),
        },
        K::Tuple(items) => O::Tuple(items.iter().map(key).collect()),
        K::Record { fields, row } => O::Record {
            fields: fields
                .iter()
                .map(|(name, mutable, value)| (name.clone(), *mutable, key(value)))
                .collect(),
            row: row.as_ref().map(|row| Box::new(key(row))),
        },
        K::Callable {
            parameters,
            result,
            annotations,
        } => O::Callable {
            parameters: parameters
                .iter()
                .map(|(mode, value)| (parameter_mode(*mode), key(value)))
                .collect(),
            result: Box::new(key(result)),
            annotations: annotations.clone(),
        },
    }
}

fn field(value: &b::RecordBoundField, types: &mut Vec<p::Type>) -> p::RecordBoundField {
    p::RecordBoundField {
        label: value.label.clone(),
        mutable: value.mutable,
        ty: ty(types, &value.ty),
        syntax: contract(&value.syntax),
        key: key(&value.key),
    }
}

fn tail(value: &m::rows::RowTail) -> p::BoundRowTail {
    match value {
        m::rows::RowTail::Closed => p::BoundRowTail::Closed,
        m::rows::RowTail::Open(value) => p::BoundRowTail::Open(p::OpenTail {
            identity: row_identity(&value.identity),
            lacks: value.lacks.iter().cloned().collect(),
        }),
    }
}

pub(super) fn selection(
    value: &b::BoundRowSelection,
    types: &mut Vec<p::Type>,
    contracts: &mut ReturnContracts,
) -> p::BoundRowSelection {
    p::BoundRowSelection {
        row: value.row,
        remainder: p::BoundRowShape {
            fields: value
                .remainder
                .fields
                .iter()
                .map(|(name, (mutable, value))| (name.clone(), (*mutable, ty(types, value))))
                .collect(),
            tail: tail(&value.remainder.tail),
        },
        fields: value
            .fields
            .iter()
            .map(|value| field(value, types))
            .collect(),
        source_type_witness: contracts.source_type_witness(value.source_type_witness.as_ref()),
    }
}

fn schema(
    value: &b::StructuralSchema,
    types: &mut Vec<p::Type>,
    contracts: &mut ReturnContracts,
) -> Result<p::StructuralSchema, NotImplemented> {
    let source = match &value.source {
        b::StructuralSchemaSource::Closed(witness) => p::StructuralSchemaSource::Closed(
            contracts
                .source_type_witness(Some(witness))
                .ok_or_else(|| {
                    NotImplemented::new(
                        ril_compiler_core::phase::Stage::Lowering,
                        "record-bound schema has no complete closed type identity",
                    )
                })?,
        ),
        b::StructuralSchemaSource::CallerBound(id) => p::StructuralSchemaSource::CallerBound(*id),
        b::StructuralSchemaSource::RigidParameter {
            definition,
            parameter_index,
            syntax,
            scope: environment,
        } => p::StructuralSchemaSource::RigidParameter {
            definition: *definition,
            parameter_index: *parameter_index,
            syntax: contract(syntax),
            scope: scope(environment),
        },
    };
    Ok(p::StructuralSchema {
        source,
        fields: value
            .fields
            .iter()
            .map(|value| field(value, types))
            .collect(),
        tail: tail(&value.tail),
    })
}

fn path(value: &b::BoundDeclarationPath) -> p::BoundDeclarationPath {
    p::BoundDeclarationPath {
        generic_index: value.generic_index,
        path: value
            .path
            .iter()
            .map(|step| match step {
                b::BoundPathStep::Bound => p::BoundPathStep::Bound,
                b::BoundPathStep::Field(name) => p::BoundPathStep::Field(name.clone()),
                b::BoundPathStep::RowTail => p::BoundPathStep::RowTail,
                b::BoundPathStep::TypeArgument(index) => p::BoundPathStep::TypeArgument(*index),
            })
            .collect(),
    }
}

fn selection_step(value: &b::BoundTypeSelectionStep) -> p::BoundTypeSelectionStep {
    use b::BoundTypeSelectionStep as S;
    use p::BoundTypeSelectionStep as O;
    match value {
        S::ArrayElement => O::ArrayElement,
        S::MapKey => O::MapKey,
        S::MapValue => O::MapValue,
        S::Tuple(index) => O::Tuple(*index),
        S::Field(name) => O::Field(name.clone()),
        S::OptionalPayload => O::OptionalPayload,
        S::ResultSuccess => O::ResultSuccess,
        S::ResultError => O::ResultError,
        S::AppliedArgument(index) => O::AppliedArgument(*index),
        S::ImmutableInner => O::ImmutableInner,
        S::CallableParameter(index) => O::CallableParameter(*index),
        S::CallableResult => O::CallableResult,
    }
}

pub(super) fn project(
    facts: &SemanticFacts,
    graph: &mut p::Graph,
    contracts: &mut ReturnContracts,
) -> Result<(), NotImplemented> {
    graph.bound_rows = facts
        .bound_rows
        .iter()
        .map(|value| p::BoundRowDeclaration {
            id: value.id,
            definition: value.definition,
            ordinal: value.ordinal,
            name: value.name.clone(),
            role: match &value.role {
                b::BoundRowRole::ImplicitResidual => p::BoundRowRole::ImplicitResidual,
                b::BoundRowRole::DeclaredTypeParameter { binder } => {
                    p::BoundRowRole::DeclaredTypeParameter {
                        binder: binder.clone(),
                    }
                }
            },
            declaration_paths: value.declaration_paths.iter().map(path).collect(),
            identity: row_identity(&value.identity),
            lacks: value.lacks.clone(),
            span: value.span,
        })
        .collect();
    graph.record_bounds = facts
        .record_bounds
        .iter()
        .map(|value| p::GenericRecordBound {
            id: value.id,
            definition: value.definition,
            binder: value.binder.clone(),
            generic_index: value.generic_index,
            syntax: contract(&value.syntax),
            scope: scope(&value.scope),
            fields: value
                .fields
                .iter()
                .map(|value| field(value, &mut graph.types))
                .collect(),
            tail: match &value.tail {
                b::DeclaredBoundTail::Closed => p::DeclaredBoundTail::Closed,
                b::DeclaredBoundTail::Row(id) => p::DeclaredBoundTail::Row(*id),
                b::DeclaredBoundTail::Concrete { syntax, key: value } => {
                    p::DeclaredBoundTail::Concrete {
                        syntax: contract(syntax),
                        key: key(value),
                    }
                }
            },
            span: value.span,
        })
        .collect();
    graph.generic_bound_checks = facts
        .generic_bound_checks
        .iter()
        .map(|value| {
            Ok(p::GenericBoundCheck {
                id: value.id,
                required: value.required,
                context: resumption_context(value.context),
                activation: value.activation.0,
                allocation_epoch: value.allocation_epoch as u64,
                argument_index: value.argument_index,
                selection_path: value.selection_path.iter().map(selection_step).collect(),
                actual: copy_snapshot(&value.actual, value.span, &mut graph.types, contracts),
                actual_schema: schema(&value.actual_schema, &mut graph.types, contracts)?,
                substitutions: value
                    .substitutions
                    .iter()
                    .map(|(name, value)| (name.clone(), key(value)))
                    .collect::<BTreeMap<_, _>>(),
                rows: value
                    .rows
                    .iter()
                    .map(|value| selection(value, &mut graph.types, contracts))
                    .collect(),
                cause: value.cause,
                span: value.span,
            })
        })
        .collect::<Result<_, NotImplemented>>()?;
    graph.generic_bound_projections = facts
        .generic_bound_projections
        .iter()
        .map(|value| p::GenericBoundProjection {
            required: value.required,
            check: value.check,
            context: resumption_context(value.context),
            activation: value.activation.0,
            allocation_epoch: value.allocation_epoch as u64,
            source: copy_snapshot(&value.source, value.span, &mut graph.types, contracts),
            slot: projection(&value.slot),
            output: copy_snapshot(&value.output, value.span, &mut graph.types, contracts),
            access: match value.access {
                b::BoundAccess::Read => p::BoundAccess::Read,
                b::BoundAccess::Write => p::BoundAccess::Write,
                b::BoundAccess::ValueOnly => p::BoundAccess::ValueOnly,
            },
            cause: value.cause,
            span: value.span,
        })
        .collect();
    graph.scoped_source_identities = facts
        .scoped_source_identities
        .iter()
        .map(|identity| p::ScopedSourceIdentity {
            id: identity.id,
            required: identity.required,
            binder: identity.binder.clone(),
            context: resumption_context(identity.context),
            syntax: contract(&identity.syntax),
            scope: scope(&identity.scope),
            key: key(&identity.key),
            occurrences: identity
                .occurrences
                .iter()
                .map(|occurrence| p::ScopedSourceOccurrence {
                    argument_index: occurrence.argument_index,
                    selection_path: occurrence
                        .selection_path
                        .iter()
                        .map(selection_step)
                        .collect(),
                    formal: p::FormalSourceAnchor {
                        definition: occurrence.formal.definition,
                        invocation: p::CopyInstanceId(occurrence.formal.invocation.0),
                        parameter_index: occurrence.formal.parameter_index,
                        type_path: occurrence
                            .formal
                            .type_path
                            .iter()
                            .map(selection_step)
                            .collect(),
                        activation: occurrence.formal.activation.0,
                        binding: occurrence.formal.binding as u32,
                        root_expression: occurrence.formal.root_expression,
                        entry_allocation_epoch: occurrence.formal.entry_allocation_epoch as u64,
                    },
                })
                .collect(),
            cause: identity.cause,
            span: identity.span,
        })
        .collect();
    graph.observed_accesses = facts
        .observed_accesses
        .iter()
        .map(|observation| p::ObservedAccess {
            id: observation.id,
            context: resumption_context(observation.context),
            activation: observation.activation.0,
            access: conditional_access(&observation.access),
        })
        .collect();
    graph.bound_field_writes = facts
        .bound_field_writes
        .iter()
        .map(|write| p::BoundFieldWrite {
            projection_index: write.projection_index,
            rhs_expression: write.rhs_expression,
            receiver_expression: write.receiver_expression,
            access: write.access,
            operator: write.operator.clone(),
            replacement: copy_snapshot(&write.replacement, write.span, &mut graph.types, contracts),
            updated_receiver: copy_snapshot(
                &write.updated_receiver,
                write.span,
                &mut graph.types,
                contracts,
            ),
            cause: write.cause,
            span: write.span,
        })
        .collect();
    Ok(())
}
