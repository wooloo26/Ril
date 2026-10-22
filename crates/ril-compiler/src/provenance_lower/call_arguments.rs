//! Keep original operand coordinates and default snapshots across Core lowering.
use super::*;
use crate::sema::{copy_contract::CopyInvocationStatus, default_uses as d};

fn static_argument(
    value: &crate::sema::effect_identity::StaticArgumentWitness,
) -> p::DefaultStaticArgument {
    p::DefaultStaticArgument {
        definition: value.definition,
        index: value.index,
        binder: value.binder.clone(),
        key: value.key.as_ref().map(record_bounds::key),
        syntax: value.syntax.as_ref().map(contract),
    }
}

fn status(value: CopyInvocationStatus) -> p::CopyInvocationStatus {
    match value {
        CopyInvocationStatus::Incomplete => p::CopyInvocationStatus::Incomplete,
        CopyInvocationStatus::Completed => p::CopyInvocationStatus::Completed,
        CopyInvocationStatus::Rejected => p::CopyInvocationStatus::Rejected,
        CopyInvocationStatus::Unsupported => p::CopyInvocationStatus::Unsupported,
    }
}

pub(super) fn lower(
    facts: &SemanticFacts,
    graph: &mut p::Graph,
    contracts: &mut ReturnContracts,
) -> Result<(), NotImplemented> {
    super::storage_sources::lower(facts, graph, contracts)?;
    graph.generated_sources = facts
        .generated_sources
        .iter()
        .map(|source| {
            let ril_syntax::ast::ExprKind::Lambda {
                parameters,
                return_type,
                annotations,
                body,
            } = &source.syntax.kind
            else {
                return Err(NotImplemented::new(
                    ril_compiler_core::phase::Stage::Lowering,
                    "generated iterator source has no complete Lambda signature",
                ));
            };
            let syntax = ril_syntax::ast::TypeExpr {
                hir_id: None,
                text: String::new(),
                span: source.syntax.span,
                kind: ril_syntax::ast::TypeKind::Callable {
                    parameters: parameters.clone(),
                    result: return_type.clone().map(Box::new),
                    annotations: annotations.clone(),
                },
            };
            Ok(p::GeneratedSource {
                id: source.id.0,
                origin_event: p::CopyCallEventId(source.origin_event.0),
                origin_context: resumption_context(source.origin_context),
                adapter: match source.adapter {
                    crate::sema::IterAdapterKind::Indexed => p::GeneratedAdapter::Indexed,
                    crate::sema::IterAdapterKind::Map => p::GeneratedAdapter::Map,
                    crate::sema::IterAdapterKind::Filter => p::GeneratedAdapter::Filter,
                    crate::sema::IterAdapterKind::Take => p::GeneratedAdapter::Take,
                },
                closure: ril_compiler_core::ids::ClosureObjectId(source.closure as u32),
                site: source.site,
                signature: contract(&syntax),
                body: body.span,
                captures: source
                    .captures
                    .iter()
                    .map(|capture| p::GeneratedCapture {
                        binding: capture.binding as u32,
                        origin_slot: capture.origin_slot,
                        path: capture.path.iter().map(projection).collect(),
                    })
                    .collect(),
            })
        })
        .collect::<Result<_, _>>()?;
    let mut builtin_work = crate::sema::source_types::WorkLimit::new(1 << 20);
    builtin_work
        .charge(facts.builtin_source_observations.len())
        .map_err(|error| {
            NotImplemented::new(
                ril_compiler_core::phase::Stage::Lowering,
                format!("builtin Source observations cannot be retained: {error}"),
            )
        })?;
    graph.builtin_source_observations = facts
        .builtin_source_observations
        .iter()
        .map(|value| {
            builtin_work.charge(8).map_err(|error| {
                NotImplemented::new(
                    ril_compiler_core::phase::Stage::Lowering,
                    format!("builtin Source environment cannot be retained: {error}"),
                )
            })?;
            if !crate::sema::builtin_sources::is_catalog_environment(&value.environment) {
                return Err(NotImplemented::new(
                    ril_compiler_core::phase::Stage::Lowering,
                    "builtin Source lost its canonical declaration environment",
                ));
            }
            Ok(p::BuiltinSourceObservation {
                expression: value.expression,
                context: resumption_context(value.context),
                identity: value.identity.clone(),
                full_header: match &value.full_header {
                    crate::sema::builtin_sources::BuiltinDeclaration::Syntax(syntax) => {
                        p::BuiltinDeclaration::Syntax(contract(syntax))
                    }
                    crate::sema::builtin_sources::BuiltinDeclaration::Generic(id) => {
                        p::BuiltinDeclaration::Generic(*id)
                    }
                    crate::sema::builtin_sources::BuiltinDeclaration::Numeric(id) => {
                        p::BuiltinDeclaration::Numeric(*id)
                    }
                },
                environment: contracts.environment(&mut graph.types, &value.environment),
                concrete_effects: value.concrete_effects.clone(),
                written_formals: value.written_formals.clone(),
                captures: value
                    .captures
                    .iter()
                    .map(|binding| *binding as u32)
                    .collect(),
                cause: value.cause,
            })
        })
        .collect::<Result<_, NotImplemented>>()?;
    graph.invocation_expressions = facts
        .invocation_expressions
        .iter()
        .map(|value| p::InvocationExpression {
            context: resumption_context(value.context),
            expression: value.expression,
            argument_of: value
                .argument_of
                .map(|(event, slot)| (p::CopyCallEventId(event.0), slot)),
        })
        .collect();
    graph.call_arguments = facts
        .call_arguments
        .iter()
        .map(|value| p::CallArguments {
            source_event: p::CopyCallEventId(value.source_event.0),
            target: value.target,
            evaluated: value
                .evaluated
                .iter()
                .map(|step| p::ApplicationEvaluation {
                    role: match step.role {
                        d::EvaluationRole::Callee => p::EvaluationRole::Callee,
                        d::EvaluationRole::Piped => p::EvaluationRole::Piped,
                        d::EvaluationRole::Written(index) => p::EvaluationRole::Written(index),
                    },
                    observation: p::SuppliedArgument {
                        expression: step.observation.expression,
                        allocation_epoch: step.observation.allocation_epoch as u64,
                    },
                })
                .collect(),
            slots_bound: value.slots_bound,
            slots: value
                .slots
                .iter()
                .map(|source| match source {
                    d::ArgumentSource::Supplied => p::ArgumentSource::Supplied,
                    d::ArgumentSource::Default(id) => {
                        p::ArgumentSource::Default(ril_ir::specialization::DefaultUseId(id.0))
                    }
                    d::ArgumentSource::Missing => p::ArgumentSource::Missing,
                })
                .collect(),
            supplied: value
                .supplied
                .iter()
                .map(|(&slot, original)| {
                    (
                        slot,
                        p::SuppliedArgument {
                            expression: original.expression,
                            allocation_epoch: original.allocation_epoch as u64,
                        },
                    )
                })
                .collect(),
            evaluation_complete: value.evaluation_complete,
        })
        .collect();
    graph.default_uses = facts
        .default_uses
        .iter()
        .map(|value| p::DefaultUse {
            id: ril_ir::specialization::DefaultUseId(value.id.0),
            origin: match value.origin {
                d::DefaultOrigin::Call(id) => p::DefaultOrigin::Call(p::CopyCallEventId(id.0)),
                d::DefaultOrigin::DeclarationProbe => p::DefaultOrigin::DeclarationProbe,
                d::DefaultOrigin::InvocationFallback(id) => {
                    p::DefaultOrigin::InvocationFallback(p::CopyInstanceId(id.0))
                }
            },
            target: value.target,
            parameter: value.parameter,
            caller: resumption_context(value.caller),
            owner: value.owner,
            span: value.span,
            arguments: value.arguments.iter().map(static_argument).collect(),
            captured_arguments: value
                .captured_arguments
                .iter()
                .map(static_argument)
                .collect(),
            unresolved_captured_binders: value.unresolved_captured_binders.clone(),
            evaluation_complete: value.evaluation_complete,
            status: status(value.status),
            entered: value
                .entered
                .iter()
                .map(|id| p::CopyInstanceId(id.0))
                .collect(),
            result: value
                .result
                .as_ref()
                .map(|snapshot| copy_snapshot(snapshot, value.span, &mut graph.types, contracts)),
            result_allocation_epoch: value.result_allocation_epoch.map(|epoch| epoch as u64),
            result_expression: value.result_expression,
        })
        .collect();
    Ok(())
}
