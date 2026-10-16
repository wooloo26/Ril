//! Copy verified semantic evidence across the frontend-independent IR boundary.
use crate::sema::{SemanticFacts, facts as f, model as m, relations as r, summary as s};
use ril_compiler_core::{
    ids::{DefinitionId, OriginId, TypeId},
    phase::NotImplemented,
    source::Span,
};
use ril_ir::provenance as p;
use ril_syntax::ast::{ParameterMode, PatternKind};
mod call_arguments;
mod record_bounds;
mod storage_sources;

fn callable(value: &m::Callable) -> p::Callable {
    match value {
        m::Callable::Constructor(name) => p::Callable::Constructor(name.clone()),
        m::Callable::Named(id) => p::Callable::Named(DefinitionId(*id as u32)),
        m::Callable::Closure(id) => p::Callable::Closure(*id as u32),
        m::Callable::Symbolic(id, path) => p::Callable::Symbolic(*id, path.clone()),
        m::Callable::Builtin(name) => p::Callable::Builtin(name.clone()),
    }
}
fn parameter_mode(mode: ParameterMode) -> p::Access {
    match mode {
        ParameterMode::Read => p::Access::Read,
        ParameterMode::Mut => p::Access::Write,
        ParameterMode::SharedMut => p::Access::Retain,
    }
}
fn annotation(value: &ril_syntax::ast::Annotation) -> p::Annotation {
    p::Annotation {
        kind: match value.kind {
            ril_syntax::ast::AnnotationKind::Effect => p::AnnotationKind::Effect,
            ril_syntax::ast::AnnotationKind::Capability => p::AnnotationKind::Capability,
        },
        text: value.text.clone(),
        span: value.span,
    }
}
fn contract(value: &ril_syntax::ast::TypeExpr) -> p::ContractSyntax {
    use p::ContractKind as C;
    use ril_syntax::ast::TypeKind as T;
    let kind = match &value.kind {
        T::Name { path, arguments } => C::Name {
            path: path.clone(),
            arguments: arguments.iter().map(contract).collect(),
        },
        T::Optional(inner) => C::Optional(Box::new(contract(inner))),
        T::Array { length, element } => C::Array {
            length: length.as_ref().map(|value| value.span),
            element: Box::new(contract(element)),
        },
        T::Map { key, value } => C::Map {
            key: Box::new(contract(key)),
            value: Box::new(contract(value)),
        },
        T::Tuple(items) => C::Tuple(items.iter().map(contract).collect()),
        T::Record { fields, row } => C::Record {
            fields: fields
                .iter()
                .map(|field| p::ContractField {
                    name: field.name.clone(),
                    mutable: field.mutable,
                    ty: contract(&field.ty),
                    span: field.span,
                })
                .collect(),
            row: row.as_ref().map(|row| Box::new(contract(row))),
        },
        T::Callable {
            parameters,
            result,
            annotations,
        } => C::Callable {
            parameters: parameters
                .iter()
                .map(|parameter| p::ContractParameter {
                    pattern: parameter.pattern.span,
                    mode: parameter_mode(parameter.mode),
                    ty: parameter.ty.as_ref().map(contract),
                    default: parameter.default.as_ref().map(|value| value.span),
                    span: parameter.span,
                })
                .collect(),
            result: result.as_ref().map(|value| Box::new(contract(value))),
            annotations: annotations.iter().map(annotation).collect(),
        },
        T::TypeFunction { parameters, body } => C::TypeFunction {
            parameters: parameters
                .iter()
                .map(|parameter| p::ContractGeneric {
                    name: parameter.name.clone(),
                    bound: parameter.bound.as_ref().map(contract),
                    default: parameter.default.as_ref().map(contract),
                    span: parameter.span,
                })
                .collect(),
            body: body.span,
        },
        T::Projection { base, field } => C::Projection {
            base: Box::new(contract(base)),
            field: field.clone(),
        },
        T::ComputedProjection { base, key } => C::ComputedProjection {
            base: Box::new(contract(base)),
            key: key.span,
        },
        T::KeyOf(base) => C::KeyOf(Box::new(contract(base))),
        T::Computation(body) => C::Computation(body.span),
        T::Mapped {
            binder,
            keys,
            value,
            tuple,
        } => C::Mapped {
            binder: binder.clone(),
            keys: keys.span,
            value: Box::new(contract(value)),
            tuple: *tuple,
        },
        T::Rest(base) => C::Rest(Box::new(contract(base))),
        T::KindArrow { parameter, result } => C::KindArrow {
            parameter: Box::new(contract(parameter)),
            result: Box::new(contract(result)),
        },
        T::Error => C::Error,
    };
    p::ContractSyntax {
        text: value.text.clone(),
        span: value.span,
        kind,
    }
}

fn origin(value: f::NodeId) -> OriginId {
    OriginId(value.0)
}
fn resumption_context(
    context: crate::sema::effect_identity::InvocationContext,
) -> p::ResumptionContext {
    p::ResumptionContext {
        invocation: context.invocation.map(|id| p::CopyInstanceId(id.0)),
        owner: context.owner,
        closure: context
            .closure
            .map(|id| ril_compiler_core::ids::ClosureObjectId(id as u32)),
        closure_invocation: context.closure_invocation,
        budget_validation: context.budget_validation,
        default_use: context
            .default_use
            .map(|id| ril_ir::specialization::DefaultUseId(id.0)),
    }
}
fn copy_snapshot(
    snapshot: &crate::sema::copy_contract::CopyValueSnapshot,
    span: Span,
    types: &mut Vec<p::Type>,
    contracts: &mut ReturnContracts,
) -> p::CopyValueSnapshot {
    p::CopyValueSnapshot {
        value: value(types, contracts, &snapshot.value, span),
        nodes: snapshot
            .nodes
            .iter()
            .map(|node| copy_node(node, span, types, contracts))
            .collect(),
        relations: snapshot
            .relations
            .iter()
            .map(|(a, b, relation)| p::Relation {
                left: origin(*a),
                right: origin(*b),
                equal: relation.equal.0,
                disjoint: relation.disjoint.0,
            })
            .collect(),
    }
}
fn copy_node(
    node: &crate::sema::copy_contract::CopyNode,
    span: Span,
    types: &mut Vec<p::Type>,
    contracts: &mut ReturnContracts,
) -> p::CopyNode {
    p::CopyNode {
        origin: origin_fact(node.origin, &node.fact),
        fields: node
            .fields
            .iter()
            .map(|(slot, field)| (projection(slot), value(types, contracts, field, span)))
            .collect(),
        length: node.length,
        fixed: node.fixed,
    }
}
fn continuation_scope_exit(
    exit: &crate::sema::resumption::ContinuationScopeExit,
    span: Span,
    types: &mut Vec<p::Type>,
    contracts: &mut ReturnContracts,
) -> p::ContinuationScopeExit {
    p::ContinuationScopeExit {
        activation: exit.activation.0,
        boundary: exit.boundary,
        epoch: exit.epoch as u64,
        binding_frontier: exit.binding_frontier as u32,
        retired_bindings: exit.retired_bindings.iter().map(|id| *id as u32).collect(),
        protected_bindings: exit
            .protected_bindings
            .iter()
            .map(|id| *id as u32)
            .collect(),
        alive_bindings: exit.alive_bindings.iter().map(|id| *id as u32).collect(),
        bindings: exit
            .bindings
            .iter()
            .map(|binding| p::ScopeBindingObservation {
                binding: binding.binding as u32,
                value: value(types, contracts, &binding.value, span),
                cell: binding.cell.map(origin),
                forwarded: binding.forwarded.iter().map(|id| *id as u32).collect(),
                alive: binding.alive,
            })
            .collect(),
        nodes: exit
            .nodes
            .iter()
            .map(|node| copy_node(node, span, types, contracts))
            .collect(),
        answer_before: copy_snapshot(&exit.answer_before, span, types, contracts),
        answer_received: copy_snapshot(&exit.answer_received, span, types, contracts),
    }
}
fn copy_invocation(
    record: &crate::sema::copy_contract::CopyInvocation,
    types: &mut Vec<p::Type>,
    contracts: &mut ReturnContracts,
) -> p::CopyInvocation {
    use crate::sema::copy_contract::CopyInvocationStatus as S;
    p::CopyInvocation {
        id: p::CopyInstanceId(record.id.0),
        parent: record.parent.map(|id| p::CopyInstanceId(id.0)),
        caller: record.caller,
        caller_owner: record.caller_owner,
        caller_activation: record.caller_activation.map(|owner| owner.0),
        entry_allocation_epoch: record.entry_allocation_epoch as u64,
        target: record.target,
        span: record.span,
        declaration_probe: record.declaration_probe,
        direct: record.direct,
        source_event: record.source_event.map(|id| p::CopyCallEventId(id.0)),
        arguments: record
            .arguments
            .iter()
            .map(|(mode, snapshot)| {
                (
                    match mode {
                        m::Mode::Read => p::Access::Read,
                        m::Mode::Write => p::Access::Write,
                        m::Mode::Retain => p::Access::Retain,
                    },
                    copy_snapshot(snapshot, record.span, types, contracts),
                )
            })
            .collect(),
        boundaries: record
            .boundaries
            .iter()
            .map(|id| p::CopyBoundaryId(id.0))
            .collect(),
        result: record
            .result
            .as_ref()
            .map(|snapshot| copy_snapshot(snapshot, record.span, types, contracts)),
        resource_copies: record
            .resource_copies
            .iter()
            .map(|id| p::ResourceCloneId(id.0))
            .collect(),
        status: match record.status {
            S::Incomplete => p::CopyInvocationStatus::Incomplete,
            S::Completed => p::CopyInvocationStatus::Completed,
            S::Rejected => p::CopyInvocationStatus::Rejected,
            S::Unsupported => p::CopyInvocationStatus::Unsupported,
        },
    }
}
fn resource_clone(
    event: &crate::sema::resource_copy::ResourceCloneEvent,
    types: &mut Vec<p::Type>,
    contracts: &mut ReturnContracts,
) -> p::ResourceCloneEvent {
    use crate::sema::resource_copy as r;
    let descriptor = |source: &r::ResourceDescriptor| p::ResourceDescriptor {
        origin: origin(source.origin),
        scope: origin(source.scope),
        task: source.task.map(origin),
        channel: source.channel.map(origin),
        formal: source.formal,
    };
    p::ResourceCloneEvent {
        id: p::ResourceCloneId(event.id.0),
        owner: event.owner,
        lexical_owner: event.lexical_owner,
        invocation: event.invocation.map(|id| p::CopyInstanceId(id.0)),
        source_event: event.source_event.map(|id| p::CopyCallEventId(id.0)),
        span: event.span,
        contract: p::ResourceCloneContract::Sender,
        required_effect: p::ResourceCloneEffect::Fiber,
        effect_registered: event.effect_registered,
        source: copy_snapshot(&event.source, event.span, types, contracts),
        source_descriptor: event.source_descriptor.as_ref().map(descriptor),
        output: copy_snapshot(&event.output, event.span, types, contracts),
        output_descriptor: event.output_descriptor.as_ref().map(descriptor),
        channel: event.channel.map(|channel| match channel {
            r::ResourceChannel::Known(node) => p::ResourceChannel::Known(origin(node)),
            r::ResourceChannel::FromSourceDescriptor(node) => {
                p::ResourceChannel::FromSourceDescriptor(origin(node))
            }
        }),
        boundary: event.boundary.as_ref().map(concurrent_boundary),
        anchors: event
            .anchors
            .iter()
            .map(|node| p::CopyNode {
                origin: origin_fact(node.origin, &node.fact),
                fields: node
                    .fields
                    .iter()
                    .map(|(slot, field)| {
                        (projection(slot), value(types, contracts, field, event.span))
                    })
                    .collect(),
                length: node.length,
                fixed: node.fixed,
            })
            .collect(),
    }
}
fn concurrent_boundary(boundary: &crate::sema::ConcurrentBoundary) -> p::ConcurrentBoundary {
    use crate::sema::ConcurrentBoundaryKind as S;
    use p::ConcurrentBoundaryKind as P;
    p::ConcurrentBoundary {
        span: boundary.span,
        scope: origin(boundary.scope),
        task: boundary.task.map(origin),
        kind: match boundary.kind {
            S::Scope => P::Scope,
            S::Fork => P::Fork,
            S::Join => P::Join,
            S::ChannelCreate => P::ChannelCreate,
            S::Send => P::Send,
            S::Receive => P::Receive,
            S::Detach => P::Detach,
            S::Attach => P::Attach,
            S::Close => P::Close,
            S::CloneSender => P::CloneSender,
        },
        cause: boundary.cause,
    }
}

fn channel_guard(guard: &crate::sema::channel_messages::ChannelGuard) -> p::ChannelGuard {
    use crate::sema::channel_messages::GuardLiteral as S;
    p::ChannelGuard {
        terms: guard
            .terms
            .iter()
            .map(|term| {
                term.iter()
                    .map(|literal| match *literal {
                        S::Optional { identity, present } => {
                            p::ChannelGuardLiteral::Optional { identity, present }
                        }
                        S::Result {
                            producer,
                            version,
                            success,
                        } => p::ChannelGuardLiteral::Result {
                            producer,
                            version,
                            success,
                        },
                        S::Transport {
                            event,
                            producer,
                            version,
                            success,
                        } => p::ChannelGuardLiteral::Transport {
                            event: p::ChannelMessageId(event.0),
                            producer,
                            version,
                            success,
                        },
                        S::Boolean { evaluation, truth } => p::ChannelGuardLiteral::Boolean {
                            evaluation: p::ConditionEvaluationId(evaluation.0),
                            truth,
                        },
                    })
                    .collect()
            })
            .collect(),
        incomplete: guard.incomplete,
    }
}

fn channel_anchor(anchor: &crate::sema::channel_messages::ChannelAnchor) -> p::ChannelAnchor {
    use crate::sema::channel_messages::ChannelAnchor as S;
    match *anchor {
        S::Known { channel, scope } => p::ChannelAnchor::Known {
            channel: origin(channel),
            scope: origin(scope),
        },
        S::Formal { endpoint, scope } => p::ChannelAnchor::Formal {
            endpoint: origin(endpoint),
            scope: origin(scope),
        },
    }
}

fn channel_dependencies(
    dependencies: &std::collections::BTreeSet<crate::sema::channel_messages::ChannelBindingPath>,
) -> Vec<p::ChannelBindingPath> {
    dependencies
        .iter()
        .map(|dependency| p::ChannelBindingPath {
            binding: dependency.binding as u32,
            projection: dependency.projection.iter().map(projection).collect(),
        })
        .collect()
}

fn channel_message(
    event: &crate::sema::channel_messages::ChannelMessageFact,
    types: &mut Vec<p::Type>,
    contracts: &mut ReturnContracts,
) -> p::ChannelMessageFact {
    use crate::sema::channel_messages::ChannelAction as S;
    let action = match &event.action {
        S::TaskFork { child } => p::ChannelAction::TaskFork {
            child: origin(*child),
        },
        S::TaskJoin { child } => p::ChannelAction::TaskJoin {
            child: origin(*child),
        },
        S::Send {
            endpoint,
            anchor,
            payload,
            transport,
            producer_versions,
            original_owners,
            dependencies,
        } => p::ChannelAction::Send {
            endpoint: copy_snapshot(endpoint, event.span, types, contracts),
            anchor: channel_anchor(anchor),
            payload: copy_snapshot(payload, event.span, types, contracts),
            transport: copy_snapshot(transport, event.span, types, contracts),
            producer_versions: producer_versions
                .iter()
                .map(|(&producer, &version)| (producer, version))
                .collect(),
            original_owners: original_owners
                .iter()
                .map(|(&producer, owner)| (producer, owner.0))
                .collect(),
            dependencies: channel_dependencies(dependencies),
        },
        S::Receive {
            endpoint,
            anchor,
            payload,
            transport,
            producer_versions,
            sources,
            dependencies,
        } => p::ChannelAction::Receive {
            endpoint: copy_snapshot(endpoint, event.span, types, contracts),
            anchor: channel_anchor(anchor),
            payload: copy_snapshot(payload, event.span, types, contracts),
            transport: copy_snapshot(transport, event.span, types, contracts),
            producer_versions: producer_versions
                .iter()
                .map(|(&producer, &version)| (producer, version))
                .collect(),
            sources: sources
                .iter()
                .map(|source| p::ChannelReceiveSource {
                    guard: channel_guard(&source.guard),
                    send: source.send.map(|send| p::ChannelMessageId(send.0)),
                })
                .collect(),
            dependencies: channel_dependencies(dependencies),
        },
        S::TagTest {
            subject,
            success,
            pattern,
            producer_versions,
        } => p::ChannelAction::TagTest {
            subject: copy_snapshot(subject, event.span, types, contracts),
            success: *success,
            pattern: *pattern,
            producer_versions: producer_versions
                .iter()
                .map(|(&producer, &version)| (producer, version))
                .collect(),
        },
        S::ConditionEvaluated {
            evaluation,
            subject_expression,
            subject,
        } => p::ChannelAction::ConditionEvaluated {
            evaluation: p::ConditionEvaluationId(evaluation.0),
            subject_expression: *subject_expression,
            subject: copy_snapshot(subject, event.span, types, contracts),
        },
        S::Inspect {
            value,
            producer_versions,
        } => p::ChannelAction::Inspect {
            value: copy_snapshot(value, event.span, types, contracts),
            producer_versions: producer_versions
                .iter()
                .map(|(&producer, &version)| (producer, version))
                .collect(),
        },
        S::Select { evaluation, truth } => p::ChannelAction::Select {
            evaluation: p::ConditionEvaluationId(evaluation.0),
            truth: *truth,
        },
        S::ResultAliases { map } => p::ChannelAction::ResultAliases {
            map: map
                .iter()
                .map(|(&family, members)| (family, members.iter().copied().collect()))
                .collect(),
        },
        S::ResultTransfer {
            from,
            to,
            source,
            producers,
        } => p::ChannelAction::ResultTransfer {
            from: from.0,
            to: to.0,
            source: copy_snapshot(source, event.span, types, contracts),
            producers: producers.iter().copied().collect(),
        },
    };
    p::ChannelMessageFact {
        id: p::ChannelMessageId(event.id.0),
        source_event: event.source_event.map(|id| p::CopyCallEventId(id.0)),
        repetition: event.repetition.map(|id| p::ChannelRepetitionId(id.0)),
        sequence: event.sequence,
        context: resumption_context(event.context),
        task: event.task.map(origin),
        activation: event.activation.0,
        span: event.span,
        cause: event.cause,
        allocation_epoch: event.allocation_epoch as u64,
        guard: channel_guard(&event.guard),
        action,
    }
}

fn channel_exit(
    event: &crate::sema::channel_messages::ChannelExitFact,
    types: &mut Vec<p::Type>,
    contracts: &mut ReturnContracts,
) -> p::ChannelExitFact {
    use crate::sema::channel_messages::ChannelExitKind as S;
    p::ChannelExitFact {
        sequence: event.sequence,
        context: resumption_context(event.context),
        activation: event.activation.0,
        span: event.span,
        cause: event.cause,
        allocation_epoch: event.allocation_epoch as u64,
        guard: channel_guard(&event.guard),
        kind: match event.kind {
            S::Complete => p::ChannelExitKind::Complete,
            S::Callable => p::ChannelExitKind::Callable,
            S::Return => p::ChannelExitKind::Return,
            S::Receiver => p::ChannelExitKind::Receiver,
            S::Scope => p::ChannelExitKind::Scope,
            S::Abnormal => p::ChannelExitKind::Abnormal,
        },
        anchor: event.anchor.as_ref().map(channel_anchor),
        returned: copy_snapshot(&event.returned, event.span, types, contracts),
    }
}
fn copy_boundary(
    boundary: &crate::sema::copy_contract::CopyBoundary,
    types: &mut Vec<p::Type>,
    contracts: &mut ReturnContracts,
) -> p::CopyBoundary {
    use crate::sema::{copy_contract as c, copy_eligibility as e};
    let project = |part: &c::CopyProjection| match part {
        c::CopyProjection::Storage(slot) => p::CopyProjection::Storage(projection(slot)),
        c::CopyProjection::OptionPayload => p::CopyProjection::OptionPayload,
        c::CopyProjection::ResultSuccess => p::CopyProjection::ResultSuccess,
        c::CopyProjection::ResultError => p::CopyProjection::ResultError,
        c::CopyProjection::Variant(tag) => p::CopyProjection::Variant(tag.clone()),
    };
    p::CopyBoundary {
        source_event: boundary.source_event.map(|id| p::CopyCallEventId(id.0)),
        invocation: boundary.invocation.map(|id| p::CopyInstanceId(id.0)),
        template: boundary.template,
        template_root: boundary.template_root.map(|id| p::CopyInstanceId(id.0)),
        id: p::CopyBoundaryId(boundary.id.0),
        owner: boundary.owner,
        activation: boundary.activation.0,
        span: boundary.span,
        cause: boundary.cause,
        mode: match boundary.mode {
            c::CopyMode::Mutable => p::CopyMode::Mutable,
            c::CopyMode::Immutable => p::CopyMode::Immutable,
        },
        source: value(types, contracts, &boundary.source, boundary.span),
        nodes: boundary
            .nodes
            .iter()
            .map(|node| p::CopyNode {
                origin: origin_fact(node.origin, &node.fact),
                fields: node
                    .fields
                    .iter()
                    .map(|(slot, field)| {
                        (
                            projection(slot),
                            value(types, contracts, field, boundary.span),
                        )
                    })
                    .collect(),
                length: node.length,
                fixed: node.fixed,
            })
            .collect(),
        relations: boundary
            .relations
            .iter()
            .map(|(a, b, relation)| p::Relation {
                left: origin(*a),
                right: origin(*b),
                equal: relation.equal.0,
                disjoint: relation.disjoint.0,
            })
            .collect(),
        constituents: boundary
            .constituents
            .iter()
            .map(|item| p::CopyConstituent {
                parent: item.parent.map(origin),
                path: item.path.iter().map(project).collect(),
                source: item
                    .source
                    .as_ref()
                    .map(|source| value(types, contracts, source, boundary.span)),
                ty: ty(types, &item.ty),
                cause: item.cause,
                qualification: match &item.qualification {
                    e::Constituent::Ordinary => p::CopyQualification::Ordinary,
                    e::Constituent::EnvironmentFreeCallable => {
                        p::CopyQualification::EnvironmentFreeCallable
                    }
                    e::Constituent::Deferred(e::AbstractMember::DataBinder(binder)) => {
                        p::CopyQualification::DeferredData(binder.clone())
                    }
                    e::Constituent::Deferred(e::AbstractMember::RowBinder(row)) => {
                        p::CopyQualification::DeferredRow(row_identity(row))
                    }
                    e::Constituent::Deferred(e::AbstractMember::CallableEnvironment) => {
                        p::CopyQualification::DeferredCallableEnvironment
                    }
                    e::Constituent::Rejected(e::Rejection::Resource) => {
                        p::CopyQualification::Resource
                    }
                    e::Constituent::Rejected(e::Rejection::RetainedEnvironment) => {
                        p::CopyQualification::RetainedEnvironment
                    }
                    e::Constituent::Incomplete => p::CopyQualification::Incomplete,
                },
            })
            .collect(),
        requirements: boundary
            .requirements
            .iter()
            .map(|requirement| p::CopyRequirement {
                constituent: requirement.constituent,
                kind: match requirement.kind {
                    c::CopyRequirementKind::Eligibility => p::CopyRequirementKind::Eligibility,
                    c::CopyRequirementKind::DeferredTransfer => {
                        p::CopyRequirementKind::DeferredTransfer
                    }
                    c::CopyRequirementKind::PriorBoundary(id) => {
                        p::CopyRequirementKind::PriorBoundary(p::CopyBoundaryId(id.0))
                    }
                    c::CopyRequirementKind::WindowGraph => p::CopyRequirementKind::WindowGraph,
                    c::CopyRequirementKind::ResultMembership => {
                        p::CopyRequirementKind::ResultMembership
                    }
                    c::CopyRequirementKind::Transfer => p::CopyRequirementKind::Transfer,
                },
            })
            .collect(),
        output: boundary
            .output
            .as_ref()
            .map(|output| value(types, contracts, output, boundary.span)),
        output_nodes: boundary
            .output_nodes
            .iter()
            .map(|node| p::CopyNode {
                origin: origin_fact(node.origin, &node.fact),
                fields: node
                    .fields
                    .iter()
                    .map(|(slot, field)| {
                        (
                            projection(slot),
                            value(types, contracts, field, boundary.span),
                        )
                    })
                    .collect(),
                length: node.length,
                fixed: node.fixed,
            })
            .collect(),
        output_relations: boundary
            .output_relations
            .iter()
            .map(|(a, b, relation)| p::Relation {
                left: origin(*a),
                right: origin(*b),
                equal: relation.equal.0,
                disjoint: relation.disjoint.0,
            })
            .collect(),
    }
}
fn computation(value: &crate::termination::Judgment) -> p::ComputationJudgment {
    p::ComputationJudgment {
        may_diverge: value.may_diverge,
        unresolved: value.unresolved,
        callable_parameters: value
            .callable_parameters
            .iter()
            .map(|&id| id as u32)
            .collect(),
    }
}
fn participant(value: f::Participant) -> p::Participant {
    match value {
        f::Participant::Loan(id) => p::Participant::Loan(id.0),
        f::Participant::Root(id) => p::Participant::Root(id.0),
    }
}
fn projection(value: &f::Slot) -> p::Projection {
    match value {
        f::Slot::Field(name) => p::Projection::Field(name.clone()),
        f::Slot::RowTail(identity) => p::Projection::RowTail(row_identity(identity)),
        f::Slot::Tuple(i) => p::Projection::Tuple(*i),
        f::Slot::Index(i) => p::Projection::Index(*i),
        f::Slot::AnyIndex => p::Projection::AnyIndex,
        f::Slot::Capture(i) => p::Projection::Capture(*i),
    }
}
fn row_identity(identity: &m::rows::RowIdentity) -> p::RowIdentity {
    match identity {
        m::rows::RowIdentity::Binder(identity) => p::RowIdentity::Binder(identity.clone()),
        m::rows::RowIdentity::Fresh { owner, ordinal } => p::RowIdentity::Fresh {
            owner: owner.clone(),
            ordinal: *ordinal,
        },
    }
}
fn access(value: s::Access) -> p::Access {
    match value {
        s::Access::Read => p::Access::Read,
        s::Access::Write => p::Access::Write,
        s::Access::Retain => p::Access::Retain,
    }
}

fn conditional_access(footprint: &m::AccessFact) -> p::ConditionalAccess {
    p::ConditionalAccess {
        observed_allocation_epoch: footprint.observed_recency as u64,
        allocation_epoch: footprint.recency as u64,
        origin_owners: footprint
            .origin_owners
            .iter()
            .map(|(node, owners)| {
                (
                    origin(*node),
                    match owners {
                        m::AccessOwners::Known(owners) => {
                            p::AccessOwners::Known(owners.iter().map(|owner| owner.0).collect())
                        }
                        m::AccessOwners::Unknown => p::AccessOwners::Unknown,
                    },
                )
            })
            .collect(),
        origins: footprint
            .origins
            .nodes
            .iter()
            .copied()
            .map(origin)
            .collect(),
        choices: footprint
            .origins
            .choices
            .iter()
            .map(|(&branch, alternatives)| {
                (
                    branch,
                    alternatives
                        .iter()
                        .map(|nodes| nodes.iter().copied().map(origin).collect())
                        .collect(),
                )
            })
            .collect(),
        slot: footprint.slot.as_ref().map(projection),
        access: match footprint.mode {
            m::Mode::Read => p::Access::Read,
            m::Mode::Write => p::Access::Write,
            m::Mode::Retain => p::Access::Retain,
        },
        participants: footprint
            .participants
            .iter()
            .copied()
            .map(participant)
            .collect(),
        cause: footprint.cause,
        span: footprint.span,
    }
}

pub(crate) fn lower(facts: &SemanticFacts) -> Result<p::Graph, NotImplemented> {
    let mut contracts = ReturnContracts::default();
    let mut graph = p::Graph {
        target_layout: facts.target_layout,
        causes: facts.explanations.causes.clone(),
        ..Default::default()
    };
    call_arguments::lower(facts, &mut graph, &mut contracts)?;
    record_bounds::project(facts, &mut graph, &mut contracts)?;
    graph.channel_repetitions = facts
        .channel_repetitions
        .iter()
        .map(|repetition| p::ChannelRepetition {
            id: p::ChannelRepetitionId(repetition.id.0),
            parent: repetition.parent.map(|id| p::ChannelRepetitionId(id.0)),
            context: resumption_context(repetition.context),
            activation: repetition.activation.0,
            call: repetition.call.map(|id| p::CopyCallEventId(id.0)),
            start_sequence: repetition.start_sequence,
            end_sequence: repetition.end_sequence,
        })
        .collect();
    graph.channel_messages = facts
        .channel_messages
        .iter()
        .map(|event| channel_message(event, &mut graph.types, &mut contracts))
        .collect();
    graph.channel_exits = facts
        .channel_exits
        .iter()
        .map(|event| channel_exit(event, &mut graph.types, &mut contracts))
        .collect();
    graph.channel_message_sequence = facts.channel_message_sequence;
    graph.allocation_history = facts
        .allocation_history
        .iter()
        .map(|&(recent, older)| (origin(recent), origin(older)))
        .collect();
    graph.operation_loan_starts = facts
        .operation_loan_starts
        .iter()
        .map(|start| p::OperationLoanStart {
            loan: start.loan.0,
            activation: start.activation.0,
            boundary: start.boundary,
            handler: start.handler as u32,
            operation: start.operation,
            parameter: start.parameter,
            temporary: start.temporary,
            context: resumption_context(start.context),
            source: copy_snapshot(&start.source, start.span, &mut graph.types, &mut contracts),
            allocation_epoch: start.allocation_epoch as u64,
            span: start.span,
            cause: start.cause,
        })
        .collect();
    graph.closure_invocations = facts
        .closure_invocations
        .iter()
        .map(|call| p::ClosureInvocation {
            id: call.id,
            source_event: call.source_event.map(|id| p::CopyCallEventId(id.0)),
            caller_activation: call.caller_activation.0,
            activation: call.activation.map(|scope| scope.0),
            closure: ril_compiler_core::ids::ClosureObjectId(call.closure as u32),
            parent_named: call.parent_named.map(|id| p::CopyInstanceId(id.0)),
            parent_closure: call.parent_closure,
            caller_owner: call.caller_owner,
            site: call.site,
            probe: call.probe,
            budget_validation: call.budget_validation,
            status: match call.status {
                crate::sema::copy_contract::CopyInvocationStatus::Incomplete => {
                    p::CopyInvocationStatus::Incomplete
                }
                crate::sema::copy_contract::CopyInvocationStatus::Completed => {
                    p::CopyInvocationStatus::Completed
                }
                crate::sema::copy_contract::CopyInvocationStatus::Rejected => {
                    p::CopyInvocationStatus::Rejected
                }
                crate::sema::copy_contract::CopyInvocationStatus::Unsupported => {
                    p::CopyInvocationStatus::Unsupported
                }
            },
        })
        .collect();
    graph.closure_exclusivity_checks = facts
        .closure_exclusivity_checks
        .iter()
        .map(|check| {
            use crate::sema::closure_exclusivity as c;
            p::ClosureExclusivityCheck {
                id: check.id,
                closure: check.closure,
                site: check.site,
                invocation: check.invocation,
                creation_named: check.creation_named.map(|id| p::CopyInstanceId(id.0)),
                creation_closure: check.creation_closure,
                creation_default: check
                    .creation_default
                    .map(|id| ril_ir::specialization::DefaultUseId(id.0)),
                probe: check.probe,
                body_complete: check.body_complete,
                span: check.span,
                allocation_epoch: check.allocation_epoch as u64,
                accesses: check.accesses.iter().map(conditional_access).collect(),
                nodes: check
                    .nodes
                    .iter()
                    .map(|(id, node)| origin_fact(*id, node))
                    .collect(),
                relations: check
                    .relations
                    .iter()
                    .map(|(a, b, relation)| p::Relation {
                        left: origin(*a),
                        right: origin(*b),
                        equal: relation.equal.0,
                        disjoint: relation.disjoint.0,
                    })
                    .collect(),
                requirements: check
                    .requirements
                    .iter()
                    .map(|requirement| p::ClosureRequirement {
                        left: requirement.left as u32,
                        right: requirement.right as u32,
                        conflict: match requirement.conflict {
                            c::Conflict::ReadWrite => p::ClosureConflict::ReadWrite,
                            c::Conflict::WriteWrite => p::ClosureConflict::WriteWrite,
                        },
                    })
                    .collect(),
                resolution: match &check.resolution {
                    c::Resolution::Proved => p::ClosureResolution::Proved,
                    c::Resolution::Pending => p::ClosureResolution::Pending,
                    c::Resolution::Discharged { calls, discards } => {
                        p::ClosureResolution::Discharged {
                            calls: calls.iter().copied().collect(),
                            discards: discards.iter().copied().collect(),
                        }
                    }
                    c::Resolution::Rejected => p::ClosureResolution::Rejected,
                    c::Resolution::Unsupported => p::ClosureResolution::Unsupported,
                },
            }
        })
        .collect();
    graph.closure_exposures = facts
        .closure_exposures
        .iter()
        .map(|exposure| p::ClosureExposure {
            closure: exposure.closure,
            kind: match exposure.kind {
                crate::sema::closure_exclusivity::ExposureKind::Returned => {
                    p::ClosureExposureKind::Returned
                }
                crate::sema::closure_exclusivity::ExposureKind::Stored => {
                    p::ClosureExposureKind::Stored
                }
            },
            owner: exposure.owner,
            named: exposure.named.map(|id| p::CopyInstanceId(id.0)),
            invocation: exposure.invocation,
            span: exposure.span,
        })
        .collect();
    graph.closure_discards = facts
        .closure_discards
        .iter()
        .map(|discard| p::ClosureDiscard {
            id: discard.id,
            closure: discard.closure,
            created_start: discard.created_start,
            created_end: discard.created_end,
            named_start: p::CopyInstanceId(discard.named_start.0),
            named_end: p::CopyInstanceId(discard.named_end.0),
            owner: discard.owner,
            named: discard.named.map(|id| p::CopyInstanceId(id.0)),
            invocation: discard.invocation,
            span: discard.span,
            allocation_epoch: discard.allocation_epoch as u64,
            value: copy_snapshot(
                &discard.value,
                discard.span,
                &mut graph.types,
                &mut contracts,
            ),
        })
        .collect();
    graph.closure_exclusivity_certificate =
        facts
            .closure_exclusivity_certificate
            .as_ref()
            .map(|certificate| p::ClosureExclusivityCertificate {
                discarded: certificate
                    .discarded
                    .iter()
                    .map(|(object, discard)| (*object, *discard))
                    .collect(),
                objects: certificate
                    .objects
                    .iter()
                    .map(|(object, calls)| (*object, calls.iter().copied().collect()))
                    .collect(),
                templates: certificate
                    .templates
                    .iter()
                    .map(|(object, instances)| (*object, instances.iter().copied().collect()))
                    .collect(),
            });
    graph.numeric_selections = facts
        .numeric_selections
        .iter()
        .map(|selection| {
            use crate::numeric_literals::{EncodedNumber, FloatFormat, NumberType};
            let selected_type = match selection.ty {
                NumberType::Int => m::Ty::Int("int".into()),
                NumberType::I8 => m::Ty::Int("i8".into()),
                NumberType::I16 => m::Ty::Int("i16".into()),
                NumberType::I32 => m::Ty::Int("i32".into()),
                NumberType::I64 => m::Ty::Int("i64".into()),
                NumberType::U8 => m::Ty::Int("u8".into()),
                NumberType::U16 => m::Ty::Int("u16".into()),
                NumberType::U32 => m::Ty::Int("u32".into()),
                NumberType::U64 => m::Ty::Int("u64".into()),
                NumberType::BigInt => m::Ty::Int("bigint".into()),
                NumberType::F32 => m::Ty::Float("f32".into()),
                NumberType::F64 => m::Ty::Float("f64".into()),
            };
            p::NumericSelection {
                id: selection.id,
                literal: selection.literal,
                span: selection.span,
                invocation: selection
                    .context
                    .invocation
                    .map(|id| p::CopyInstanceId(id.0)),
                owner: selection.context.owner,
                closure: selection.context.closure.map(|id| id as u32),
                closure_invocation: selection.context.closure_invocation.map(|id| id.0),
                default_use: selection.context.default_use.map(|id| id.0),
                budget_validation: selection.context.budget_validation,
                ty: ty(&mut graph.types, &selected_type),
                layout: selection.layout,
                cause: selection.cause,
                encoded: match &selection.encoded {
                    EncodedNumber::Integer {
                        value,
                        bits,
                        signed,
                        ..
                    } => p::NumericEncoding::Integer {
                        value: *value,
                        bits: *bits,
                        signed: *signed,
                    },
                    EncodedNumber::BigInteger(value) => {
                        p::NumericEncoding::BigInteger(value.to_string())
                    }
                    EncodedNumber::Float(value) => p::NumericEncoding::Float {
                        bits: match value.format() {
                            FloatFormat::F32 => 32,
                            FloatFormat::F64 => 64,
                        },
                        payload: value.bits(),
                    },
                },
            }
        })
        .collect();
    graph.condition_evaluations = facts
        .condition_evaluations
        .iter()
        .map(|event| p::ConditionEvaluation {
            id: p::ConditionEvaluationId(event.id.0),
            invocation: event.context.invocation.map(|id| p::CopyInstanceId(id.0)),
            owner: event.context.owner,
            closure: event.context.closure.map(|id| id as u32),
            closure_invocation: event.context.closure_invocation.map(|id| id.0),
            default_use: event.context.default_use.map(|id| id.0),
            budget_validation: event.context.budget_validation,
            span: event.span,
            cause: event.cause,
            constant: event.constant,
            kind: match event.kind {
                crate::sema::result_conditions::ConditionKind::Plain => p::ConditionKind::Plain,
                crate::sema::result_conditions::ConditionKind::Pattern => p::ConditionKind::Pattern,
                crate::sema::result_conditions::ConditionKind::Negation => {
                    p::ConditionKind::Negation
                }
                crate::sema::result_conditions::ConditionKind::Conjunction => {
                    p::ConditionKind::Conjunction
                }
                crate::sema::result_conditions::ConditionKind::Disjunction => {
                    p::ConditionKind::Disjunction
                }
            },
            inspections: condition_inspections(&event.inspections),
        })
        .collect();
    graph.constant_values = facts
        .constant_values
        .iter()
        .map(|constant| {
            (
                constant.reference,
                value(
                    &mut graph.types,
                    &mut contracts,
                    &constant.value,
                    constant.span,
                ),
            )
        })
        .collect();
    graph.concurrent_boundaries = facts
        .concurrent_boundaries
        .iter()
        .map(concurrent_boundary)
        .collect();
    graph.parallel_boundaries = facts
        .parallel_boundaries
        .iter()
        .map(|boundary| {
            use crate::sema::ParallelOperation as S;
            use p::ParallelOperation as P;
            p::ParallelBoundary {
                span: boundary.span,
                operation: match boundary.operation {
                    S::Map => P::Map,
                    S::MapBounded => P::MapBounded,
                    S::Find => P::Find,
                    S::First => P::First,
                    S::Any => P::Any,
                    S::Fold => P::Fold,
                    S::Join => P::Join,
                    S::Join3 => P::Join3,
                    S::ForEach => P::ForEach,
                },
                callbacks: boundary
                    .callbacks
                    .iter()
                    .map(|proof| p::ParallelCallbackProof {
                        cause: proof.cause,
                        accesses: proof.accesses.iter().map(conditional_access).collect(),
                        selected_handlers: proof
                            .selected_handlers
                            .iter()
                            .map(|&id| id as u32)
                            .collect(),
                        termination: computation(&proof.termination),
                    })
                    .collect(),
                cause: boundary.cause,
            }
        })
        .collect();
    graph.scope_parents = facts
        .scope_parents
        .iter()
        .map(|(child, parent)| (child.0, parent.0))
        .collect();
    graph.storage_types = facts
        .storage_types
        .iter()
        .map(|(node, storage)| (origin(*node), ty(&mut graph.types, storage)))
        .collect();
    graph.static_key_checks = facts
        .static_key_checks
        .iter()
        .map(|check| p::StaticKeyCheck {
            binder: check.binder.clone(),
            argument: check.argument,
            receiver: ty(&mut graph.types, &check.receiver),
            coordinate: match &check.coordinate {
                m::StaticCoordinate::Label(label) => p::StaticCoordinate::Label(label.clone()),
                m::StaticCoordinate::Index(index) => p::StaticCoordinate::Index(*index),
            },
            cause: check.cause,
        })
        .collect();
    graph.cleanup_events = facts
        .cleanup_events
        .iter()
        .map(|event| p::CleanupEvent {
            binding: event.binding as u32,
            owner: event.owner.0,
            span: event.span,
            resumed_boundary: event.resumed_boundary,
            cause: event.cause,
        })
        .collect();
    graph.contextual_types = facts
        .contextual_types
        .iter()
        .map(|(&(file, start, end), ty)| {
            (
                Span {
                    file: ril_compiler_core::source::FileId(file),
                    start,
                    end,
                },
                self::ty(&mut graph.types, ty),
            )
        })
        .collect();
    graph.origins = facts
        .heap
        .nodes
        .iter()
        .enumerate()
        .map(|(index, node)| origin_fact(f::NodeId(index as u32), node))
        .collect();
    graph.handlers = facts
        .handlers
        .iter()
        .map(|handler| p::Handler {
            definition: handler.site,
            callable_owner: handler.callable_owner,
            id: handler.id as u32,
            boundary: handler.boundary,
            span: handler.span,
            operations: handler.operations.clone(),
            arm_spans: handler.arm_spans.clone(),
            lexical: handler
                .lexical
                .iter()
                .map(|(name, &binding)| (name.clone(), binding as u32))
                .collect(),
            answer: handler
                .answer
                .as_ref()
                .map(|answer| ty(&mut graph.types, answer)),
        })
        .collect();
    graph.retained_handler_answers = facts
        .retained_handler_answers
        .iter()
        .map(|proof| p::RetainedHandlerAnswer {
            handler: proof.handler as u32,
            operation: proof.operation,
            declaration: ty(&mut graph.types, &proof.declaration),
            invocation: ty(&mut graph.types, &proof.invocation),
            parametric: proof.parametric,
            transport: match proof.transport {
                m::AnswerTransport::CopyChecked => p::AnswerTransport::CopyChecked,
                m::AnswerTransport::Identity => p::AnswerTransport::Identity,
                m::AnswerTransport::OrdinaryChecked => p::AnswerTransport::OrdinaryChecked,
            },
            span: proof.span,
            cause: proof.cause,
            activation: proof.activation.0,
            resumption_steps: proof
                .resumption_steps
                .iter()
                .map(|index| *index as u32)
                .collect(),
        })
        .collect();
    graph.closure_sites = facts
        .closure_sites
        .iter()
        .map(|site| p::ClosureSite {
            id: site.id,
            owner: site.owner,
            span: site.span,
        })
        .collect();
    graph.retained_handlers = facts
        .retained_handlers
        .iter()
        .map(|proof| p::RetainedHandler {
            callable: match proof.callable {
                m::Callable::Named(id) => Some(ril_compiler_core::ids::CallableOwner::Function(
                    facts.functions[id].definition,
                )),
                m::Callable::Closure(id) => facts.closures[id]
                    .site
                    .map(ril_compiler_core::ids::CallableOwner::Lambda),
                _ => None,
            },
            span: proof.span,
            handlers: proof.handlers.iter().map(|id| *id as u32).collect(),
            definitions: proof
                .handlers
                .iter()
                .map(|id| facts.handlers[*id].site)
                .collect(),
            answer: ty(&mut graph.types, &proof.answer),
            cause: proof.cause,
        })
        .collect();
    graph.operation_loan_ends = facts
        .operation_loan_ends
        .iter()
        .map(|(loan, &cause)| (loan.0, cause))
        .collect();
    graph.implicit_unwraps = facts
        .implicit_unwraps
        .iter()
        .map(|(&(file, start, end), proof)| p::ImplicitUnwrap {
            span: Span {
                file: ril_compiler_core::source::FileId(file),
                start,
                end,
            },
            cause: proof.cause,
            depth: proof.depth,
            tags: proof.tags.clone(),
        })
        .collect();
    graph.variant_projections = facts
        .variant_projections
        .iter()
        .map(|(&(file, start, end), proof)| p::VariantProjection {
            span: Span {
                file: ril_compiler_core::source::FileId(file),
                start,
                end,
            },
            tag: proof.tag.clone(),
            cause: proof.cause,
            direct: proof.direct,
        })
        .collect();
    graph.constructors = facts
        .constructors
        .iter()
        .map(|(name, info)| p::Constructor {
            name: name.clone(),
            tag: info.tag.clone(),
            owner: ty(&mut graph.types, &info.owner),
            payload: ty(&mut graph.types, &info.payload),
            nominal: info.nominal,
            has_payload: info.has_payload,
            span: info.span,
        })
        .collect();
    graph.operations = facts
        .operations
        .values()
        .map(|operation| p::Operation {
            identity: operation.identity,
            name: operation.name.clone(),
            effect: operation.effect.clone(),
            span: operation.span,
            parameters: operation
                .parameters
                .iter()
                .map(|(mode, parameter)| {
                    (
                        match mode {
                            ParameterMode::Read => p::Access::Read,
                            ParameterMode::Mut => p::Access::Write,
                            ParameterMode::SharedMut => p::Access::Retain,
                        },
                        ty(&mut graph.types, parameter),
                    )
                })
                .collect(),
            result: ty(&mut graph.types, &operation.result),
        })
        .collect();
    graph.expression_sources = facts
        .expressions
        .iter()
        .map(|expression| expression.source_id)
        .collect();
    graph.values = facts
        .expressions
        .iter()
        .map(|expression| {
            value(
                &mut graph.types,
                &mut contracts,
                &expression.value,
                expression.span,
            )
        })
        .collect();
    graph.fields = facts
        .fields
        .iter()
        .map(|((node, slot), field)| p::Field {
            origin: origin(*node),
            projection: projection(slot),
            value: value(
                &mut graph.types,
                &mut contracts,
                field,
                facts.explanations.causes[field.cause.0 as usize]
                    .span
                    .unwrap_or(Span {
                        file: facts.file.unwrap_or(ril_compiler_core::source::FileId(0)),
                        start: 0,
                        end: 0,
                    }),
            ),
        })
        .collect();
    graph.uncertain_slots = facts
        .uncertain_slots
        .iter()
        .map(|(node, slot)| (origin(*node), projection(slot)))
        .collect();
    graph.array_lengths = facts
        .array_lengths
        .iter()
        .map(|(node, length)| (origin(*node), *length))
        .collect();
    graph.fixed_arrays = facts.fixed_arrays.iter().copied().map(origin).collect();
    graph.bindings = facts
        .bindings
        .iter()
        .enumerate()
        .map(|(index, binding)| p::Binding {
            id: index as u32,
            name: binding.name.clone(),
            root: binding.root.0,
            cell: binding.cell.map(origin),
            owner: binding.owner.0,
            lexical_scope: binding.lexical_scope,
            reassignable: binding.mode.is_reassignable(),
            writable: binding.mode.is_mutable(),
            alive: binding.alive,
            slot_used: binding.slot_used,
            write_used: binding.write_used,
            used: binding.used,
            forwarded: binding.forwarded.iter().map(|id| *id as u32).collect(),
            parameter: binding.parameter,
            value: value(
                &mut graph.types,
                &mut contracts,
                &binding.value,
                binding.span,
            ),
        })
        .collect();
    graph.conditions = facts
        .heap
        .conditions
        .decisions()
        .map(|(id, atom, low, high)| p::Decision {
            id: id.0,
            atom: match atom {
                r::Atom::Equal(a, b) => p::Atom::Equal(a.0, b.0),
                r::Atom::Disjoint(a, b) => p::Atom::Disjoint(a.0, b.0),
            },
            low: low.0,
            high: high.0,
        })
        .collect();
    graph.relations = facts
        .heap
        .relations()
        .map(|(left, right, relation)| p::Relation {
            left: origin(left),
            right: origin(right),
            equal: relation.equal.0,
            disjoint: relation.disjoint.0,
        })
        .collect();
    graph.callables = facts
        .functions
        .iter()
        .enumerate()
        .map(|(id, function)| p::Environment {
            callable: p::Callable::Named(DefinitionId(id as u32)),
            span: function.syntax.span,
            owner: function.owner.map(|id| id.0),
            lexical_scope: Some(function.lexical_scope),
            published: function.environment_published,
            origin: function.environment.map(origin),
            lexical: function
                .lexical
                .iter()
                .map(|(name, id)| (name.clone(), *id as u32))
                .collect(),
            captures: function.captures.iter().map(|id| *id as u32).collect(),
            writes: function.writes.iter().map(|id| *id as u32).collect(),
            handler_context: function
                .handler_context
                .iter()
                .map(|&id| id as u32)
                .collect(),
        })
        .chain(facts.closures.iter().enumerate().map(|(id, closure)| {
            p::Environment {
                callable: p::Callable::Closure(id as u32),
                span: closure.body.span,
                owner: Some(closure.owner.0),
                lexical_scope: None,
                published: true,
                origin: Some(origin(closure.node)),
                lexical: closure
                    .lexical
                    .iter()
                    .map(|(name, id)| (name.clone(), *id as u32))
                    .collect(),
                captures: closure.captures.iter().map(|id| *id as u32).collect(),
                writes: closure.writes.iter().map(|id| *id as u32).collect(),
                handler_context: closure
                    .handler_context
                    .iter()
                    .map(|&id| id as u32)
                    .collect(),
            }
        }))
        .collect();
    graph.invocations = facts
        .invocations
        .iter()
        .map(|summary| p::Invocation {
            activation: summary.activation.map(|owner| owner.0),
            context: summary.context.map(resumption_context),
            channel_messages: summary
                .channel_messages
                .iter()
                .map(|id| p::ChannelMessageId(id.0))
                .collect(),
            copy_boundaries: summary
                .copy_boundaries
                .iter()
                .map(|id| p::CopyBoundaryId(id.0))
                .collect(),
            handler_environment: summary.handler_environment,
            selected_handlers: summary
                .selected_handlers
                .iter()
                .map(|&id| id as u32)
                .collect(),
            accesses: summary
                .accesses
                .iter()
                .map(|footprint| {
                    (
                        origin(footprint.origin),
                        participant(footprint.participant),
                        access(footprint.access),
                    )
                })
                .collect(),
            concrete_state: summary
                .concrete_state
                .iter()
                .map(|(id, mode)| (*id, access(*mode)))
                .collect(),
            effects: summary.effects.iter().cloned().collect(),
            performed_operations: summary.performed_operations.iter().copied().collect(),
            callbacks: summary
                .callbacks
                .iter()
                .map(|dependency| (dependency.parameter, dependency.projection.clone()))
                .collect(),
            escaped_origins: summary
                .escaped_origins
                .iter()
                .copied()
                .map(origin)
                .collect(),
            retained_origins: summary
                .retained_origins
                .iter()
                .copied()
                .map(origin)
                .collect(),
            new_environments: summary
                .new_environments
                .iter()
                .copied()
                .map(origin)
                .collect(),
            owners: summary.owners.iter().map(|owner| owner.0).collect(),
            unresolved: summary.unresolved.iter().copied().collect(),
        })
        .collect();
    graph.windows = facts
        .windows
        .iter()
        .map(|(&node, window)| p::Window {
            origin: origin(node),
            backing: window.backing.nodes.iter().copied().map(origin).collect(),
            choices: window
                .backing
                .choices
                .iter()
                .map(|(&branch, alternatives)| {
                    (
                        branch,
                        alternatives
                            .iter()
                            .map(|nodes| nodes.iter().copied().map(origin).collect())
                            .collect(),
                    )
                })
                .collect(),
            lower: window.lower,
            length: window.length,
            span: window.span,
            cause: window.cause,
        })
        .collect();
    graph.budget_proofs = facts
        .budget_proofs
        .iter()
        .map(|proof| p::BudgetProof {
            span: proof.span,
            exhaustion_operation: proof.exhaustion_operation,
            callee_coverage: proof.callee_coverage.clone(),
            cleanup_coverage: proof.cleanup_coverage.clone(),
            cause: proof.cause,
        })
        .collect();
    graph.budget_termination = facts
        .budget_termination
        .iter()
        .map(|witness| p::BudgetTermination {
            span: witness.span,
            cause: witness.cause,
            exhaustion_operation: witness.exhaustion_operation,
            callee_coverage: witness.callee_coverage.clone(),
            cleanup_coverage: witness.cleanup_coverage.clone(),
            explicit_evaluation: computation(&witness.explicit_evaluation),
            action_invocation: computation(&witness.action_invocation),
            recovery: computation(&witness.recovery),
        })
        .collect();
    graph.iter_steps = facts
        .iter_steps
        .iter()
        .map(|step| p::IterStep {
            identity: step.identity.clone(),
            closure: step.closure as u32,
            kind: match step.kind {
                crate::sema::IterAdapterKind::Indexed => p::IterAdapterKind::Indexed,
                crate::sema::IterAdapterKind::Map => p::IterAdapterKind::Map,
                crate::sema::IterAdapterKind::Filter => p::IterAdapterKind::Filter,
                crate::sema::IterAdapterKind::Take => p::IterAdapterKind::Take,
            },
            state: ty(&mut graph.types, &step.state),
            item: ty(&mut graph.types, &step.item),
            span: step.span,
            cause: step.cause,
        })
        .collect();
    graph.inference_resolutions = facts
        .inference_resolutions
        .iter()
        .map(|resolution| p::InferenceResolution {
            binder: resolution.binder.clone(),
            selected: ty(&mut graph.types, &resolution.selected),
            site: resolution.site,
            origin: resolution.origin,
            cause: resolution.cause,
        })
        .collect();
    graph.result_families = facts
        .result_families
        .iter()
        .map(|(&family, members)| (family, members.iter().copied().collect()))
        .collect();
    graph.static_key_parameters = facts
        .static_key_parameters
        .iter()
        .map(|parameter| p::StaticKeyParameter {
            binder: parameter.binder.clone(),
            owner: parameter.owner,
            parameter: parameter.parameter,
            name: parameter.name.clone(),
            cause: parameter.cause,
        })
        .collect();
    graph.definition_checks = facts
        .definition_checks
        .iter()
        .map(|check| p::DefinitionCheck {
            function: check.function as u32,
            span: check.span,
            returned: ty(&mut graph.types, &check.returned),
            declared: ty(&mut graph.types, &check.declared),
            invocation: facts
                .invocations
                .iter()
                .position(|summary| summary == &check.invocation)
                .map(|index| index as u32),
        })
        .collect();
    graph.resumption_steps = facts
        .resumption_steps
        .iter()
        .map(|step| p::ResumptionStep {
            span: step.span,
            owner: step.owner.0,
            handler: step.handler as u32,
            operation: step.operation,
            body_answer: ty(&mut graph.types, &step.body_answer),
            arm_answer: ty(&mut graph.types, &step.arm_answer),
            continuation: step.continuation,
            cause: step.cause,
            boundary: step.boundary,
            context: resumption_context(step.context),
            continuation_value: copy_snapshot(
                &step.continuation_value,
                step.span,
                &mut graph.types,
                &mut contracts,
            ),
            arm_value: copy_snapshot(&step.arm_value, step.span, &mut graph.types, &mut contracts),
            continuation_epoch: step.continuation_epoch as u64,
            completion_epoch: step.completion_epoch as u64,
            ended_operation_loans: step
                .ended_operation_loans
                .iter()
                .map(|loan| loan.0)
                .collect(),
            operation_receptions: step
                .operation_receptions
                .iter()
                .map(|receipt| p::OperationReception {
                    parameter: receipt.parameter,
                    mode: parameter_mode(receipt.mode),
                    loan: receipt.loan.map(|loan| loan.0),
                })
                .collect(),
            continuation_expression: step.continuation_expression as u32,
            arm_expression: step.arm_expression as u32,
            transport: match step.transport {
                m::AnswerTransport::CopyChecked => p::AnswerTransport::CopyChecked,
                m::AnswerTransport::Identity => p::AnswerTransport::Identity,
                m::AnswerTransport::OrdinaryChecked => p::AnswerTransport::OrdinaryChecked,
            },
            scope_exit: step.scope_exit.as_ref().map(|exit| {
                continuation_scope_exit(exit, step.span, &mut graph.types, &mut contracts)
            }),
        })
        .collect();
    graph.termination = facts
        .termination
        .iter()
        .map(|(name, judgment)| p::Termination {
            function: name.clone(),
            may_diverge: judgment.may_diverge,
            unresolved: judgment.unresolved,
            callable_parameters: judgment
                .callable_parameters
                .iter()
                .map(|id| *id as u32)
                .collect(),
        })
        .collect();
    graph.invocation_loan_starts = facts
        .invocation_loan_starts
        .iter()
        .map(|start| p::InvocationLoanStart {
            loan: start.loan.0,
            activation: start.activation.0,
            owner: start.owner,
            named: start.named.map(|id| p::CopyInstanceId(id.0)),
            closure: start.closure,
            parameter: start.parameter,
            retained: start.retained,
            source: value(&mut graph.types, &mut contracts, &start.source, start.span),
            bindings: start.bindings.iter().map(|id| *id as u32).collect(),
            allocation_epoch: start.allocation_epoch as u64,
            cause: start.cause,
            span: start.span,
        })
        .collect();
    graph.invocation_loan_ends = facts
        .invocation_loan_ends
        .iter()
        .map(|end| p::InvocationLoanEnd {
            activation: end.activation.0,
            owner: end.owner,
            named: end.named.map(|id| p::CopyInstanceId(id.0)),
            closure: end.closure,
            loans: end
                .loans
                .iter()
                .map(|(loan, parents)| (loan.0, parents.iter().copied().map(participant).collect()))
                .collect(),
            cause: end.cause,
            span: end.span,
        })
        .collect();
    graph.loan_parents = facts
        .loan_parents
        .iter()
        .map(|(loan, parents)| (loan.0, parents.iter().copied().map(participant).collect()))
        .collect();
    graph.generic_binders = facts
        .generic_binders
        .values()
        .map(|binder| p::GenericBinder {
            identity: binder.identity.clone(),
            definition: binder.definition,
            owner: binder.owner,
            index: binder.index,
            name: binder.name.clone(),
            ty: ty(&mut graph.types, &m::Ty::Generic(binder.identity.clone())),
        })
        .collect();
    graph.optional_tags = facts
        .optional_tags
        .iter()
        .map(|tag| p::OptionalTagFact {
            id: tag.id,
            creation_owner: tag.creation_owner.0,
            cause: tag.cause,
            payload_type: ty(&mut graph.types, &tag.payload_type),
        })
        .collect();
    graph.result_duties = facts
        .result_duties
        .iter()
        .map(|duty| p::ResultDuty {
            id: duty.id,
            creation_owner: duty.creation_owner.0,
            owner: duty.owner.0,
            span: duty.span,
            cause: duty.cause,
            inspected: duty.inspected,
            returned: duty.returned,
            abnormal: duty.abnormal,
            covered: duty.covered,
        })
        .collect();
    graph.copy_boundaries = facts
        .copy_boundaries
        .iter()
        .map(|boundary| copy_boundary(boundary, &mut graph.types, &mut contracts))
        .collect();
    graph.copy_references = facts
        .copy_references
        .iter()
        .map(|reference| p::CopyReference {
            id: p::CopyReferenceId(reference.id.0),
            expression: reference.expression,
            owner: reference.owner,
            parent: reference.parent.map(|id| p::CopyInstanceId(id.0)),
            target: reference.target,
            span: reference.span,
            direct_call: reference.direct_call.map(|id| p::CopyCallEventId(id.0)),
        })
        .collect();
    graph.copy_call_events = facts
        .copy_call_events
        .iter()
        .map(|event| p::CopyCallEvent {
            id: p::CopyCallEventId(event.id.0),
            source_id: event.source_id,
            callee_expression: event.callee_expression,
            result_expression: event.result_expression,
            owner: event.owner,
            parent: event.parent.map(|id| p::CopyInstanceId(id.0)),
            span: event.span,
            target: event.target,
            direct: event.direct,
            copy_operation: event.copy_operation.map(|mode| match mode {
                crate::sema::copy_contract::CopyMode::Mutable => p::CopyMode::Mutable,
                crate::sema::copy_contract::CopyMode::Immutable => p::CopyMode::Immutable,
            }),
            references: event
                .references
                .iter()
                .map(|id| p::CopyReferenceId(id.0))
                .collect(),
        })
        .collect();
    graph.resource_clones = facts
        .resource_clones
        .iter()
        .map(|event| resource_clone(event, &mut graph.types, &mut contracts))
        .collect();
    graph.copy_invocations = facts
        .copy_invocations
        .iter()
        .map(|record| copy_invocation(record, &mut graph.types, &mut contracts))
        .collect();
    graph.copy_template_closure =
        facts
            .copy_template_closure
            .as_ref()
            .map(|closure| p::CopyTemplateClosure {
                templates: closure
                    .templates
                    .iter()
                    .map(|(&owner, template)| p::CopyTemplate {
                        owner,
                        public: template.public,
                        escaped: template.escaped,
                        sites: template
                            .sites
                            .iter()
                            .map(|site| p::CopyCallSite {
                                owner: site.owner,
                                target: site.target,
                                span: Span {
                                    file: ril_compiler_core::source::FileId(site.source.0),
                                    start: site.source.1,
                                    end: site.source.2,
                                },
                            })
                            .collect(),
                        dependencies: template.dependencies.iter().copied().collect(),
                    })
                    .collect(),
                instances: closure
                    .certificate
                    .instances
                    .iter()
                    .map(|(&owner, ids)| {
                        (
                            owner,
                            ids.iter().map(|id| p::CopyInstanceId(id.0)).collect(),
                        )
                    })
                    .collect(),
                dependency_order: closure.certificate.dependency_order.clone(),
                discharges: closure
                    .discharges
                    .iter()
                    .map(|((instance, boundary), proof)| {
                        (
                            p::CopyInstanceId(instance.0),
                            p::CopyBoundaryId(boundary.0),
                            match proof {
                                crate::sema::resource_copy::CopyDischarge::Ordinary(id) => {
                                    p::CopyDischarge::Ordinary(p::CopyBoundaryId(id.0))
                                }
                                crate::sema::resource_copy::CopyDischarge::Sender(id) => {
                                    p::CopyDischarge::Sender(p::ResourceCloneId(id.0))
                                }
                            },
                        )
                    })
                    .collect(),
            });
    if let Some(error) = contracts.type_witness_error {
        return Err(error);
    }
    graph.callable_return_contracts = contracts.nodes;
    Ok(graph)
}
#[derive(Default)]
struct ReturnContracts {
    type_witness_error: Option<NotImplemented>,
    source_types: std::collections::BTreeMap<String, std::sync::Arc<p::SourceTypeWitness>>,
    // Copy memo only. Retain each Arc so allocation-address reuse cannot skip
    // validation of a different witness with the same canonical key.
    checked_source_types: std::collections::BTreeMap<
        *const m::SourceTypeWitness,
        std::sync::Arc<m::SourceTypeWitness>,
    >,
    nodes: Vec<p::CallableReturnBound>,
    // Copy memo only: addresses never become semantic or emitted identities.
    copied: std::collections::BTreeMap<*const m::CallableReturnBound, p::ReturnContractId>,
}
impl ReturnContracts {
    fn source_type_witness(
        &mut self,
        witness: Option<&std::sync::Arc<m::SourceTypeWitness>>,
    ) -> Option<std::sync::Arc<p::SourceTypeWitness>> {
        let witness = witness?;
        let pointer = std::sync::Arc::as_ptr(witness);
        if let std::collections::btree_map::Entry::Vacant(entry) =
            self.checked_source_types.entry(pointer)
        {
            if !witness.validate_closed() {
                self.type_witness_error.get_or_insert_with(|| {
                    NotImplemented::new(
                        ril_compiler_core::phase::Stage::Lowering,
                        "source type witness is incomplete or its canonical key is inconsistent",
                    )
                });
                return None;
            }
            entry.insert(witness.clone());
        }
        if let Some(existing) = self.source_types.get(&witness.key) {
            return Some(existing.clone());
        }
        let key = crate::static_eval::effects::argument_key(
            &witness.syntax,
            &std::collections::BTreeMap::new(),
        );
        match crate::type_identity_lower::closed_key(&key) {
            Ok(shape) => {
                let output = std::sync::Arc::new(p::SourceTypeWitness {
                    key: witness.key.clone(),
                    shape,
                });
                self.source_types
                    .insert(witness.key.clone(), output.clone());
                Some(output)
            }
            Err(error) => {
                self.type_witness_error.get_or_insert(error);
                None
            }
        }
    }
    fn intern(
        &mut self,
        types: &mut Vec<p::Type>,
        root: &std::sync::Arc<m::CallableReturnBound>,
    ) -> p::ReturnContractId {
        let mut pending = vec![(root, false)];
        while let Some((bound, expanded)) = pending.pop() {
            let pointer = std::sync::Arc::as_ptr(bound);
            if self.copied.contains_key(&pointer) {
                continue;
            }
            if !expanded {
                pending.push((bound, true));
                pending.extend(
                    bound
                        .predecessors
                        .iter()
                        .rev()
                        .map(|parent| (parent, false)),
                );
                continue;
            }
            let predecessors = bound
                .predecessors
                .iter()
                .map(|parent| self.copied[&std::sync::Arc::as_ptr(parent)])
                .collect();
            let node = p::CallableReturnBound {
                raw: bound.raw,
                predecessors,
                target: ty(types, &bound.target),
                syntax: contract(&bound.syntax),
                span: bound.span,
                callables: bound.callables.iter().map(callable).collect(),
                lexical: bound
                    .typing_environment
                    .contract_bindings
                    .iter()
                    .map(|(name, &id)| (name.clone(), id as u32))
                    .collect(),
                generic_context: bound
                    .typing_environment
                    .generic_context
                    .iter()
                    .map(|(name, value)| (name.clone(), value.clone()))
                    .collect(),
                generic_substitutions: bound
                    .typing_environment
                    .generic_substitutions
                    .iter()
                    .map(|(name, value)| (name.clone(), ty(types, value)))
                    .collect(),
                generic_type_witnesses: bound
                    .typing_environment
                    .generic_type_witnesses
                    .iter()
                    .filter_map(|(name, witness)| {
                        self.source_type_witness(Some(witness))
                            .map(|witness| (name.clone(), witness))
                    })
                    .collect(),
                bound_row_context: bound
                    .typing_environment
                    .bound_row_context
                    .iter()
                    .map(|(name, id)| (name.clone(), *id))
                    .collect(),
                bound_row_selections: bound
                    .typing_environment
                    .bound_row_selections
                    .values()
                    .map(|selection| record_bounds::selection(selection, types, self))
                    .collect(),
                static_key_arguments: bound
                    .typing_environment
                    .static_key_arguments
                    .iter()
                    .map(|(name, coordinate)| {
                        (
                            name.clone(),
                            match coordinate {
                                m::StaticCoordinate::Label(label) => {
                                    p::StaticCoordinate::Label(label.clone())
                                }
                                m::StaticCoordinate::Index(index) => {
                                    p::StaticCoordinate::Index(*index)
                                }
                            },
                        )
                    })
                    .collect(),
            };
            let id = p::ReturnContractId(self.nodes.len() as u32);
            self.nodes.push(node);
            self.copied.insert(pointer, id);
        }
        self.copied[&std::sync::Arc::as_ptr(root)]
    }
}
pub(crate) fn ty(types: &mut Vec<p::Type>, value: &m::Ty) -> TypeId {
    let converted = match value {
        m::Ty::NumericHole(_) => {
            unreachable!("uncommitted numeric hole crossed the verified boundary")
        }
        m::Ty::Unknown => p::Type::Unknown,
        m::Ty::Never => p::Type::Never,
        m::Ty::Unit => p::Type::Unit,
        m::Ty::Bool => p::Type::Bool,
        m::Ty::Int(name) => p::Type::Integer(name.clone()),
        m::Ty::Float(name) => p::Type::Float(name.clone()),
        m::Ty::Str => p::Type::String,
        m::Ty::Bytes => p::Type::Bytes,
        m::Ty::Named(name) => p::Type::Named(name.clone()),
        m::Ty::Applied {
            constructor,
            arguments,
        } => p::Type::Applied {
            constructor: constructor.clone(),
            arguments: arguments
                .iter()
                .map(|argument| match argument {
                    m::TypeArgument::Type(inner) => p::TypeArgument::Type(ty(types, inner)),
                    m::TypeArgument::CanonicalType { ty: inner, key } => {
                        p::TypeArgument::CanonicalType {
                            ty: ty(types, inner),
                            key: key.clone(),
                        }
                    }
                    m::TypeArgument::Static(key) => p::TypeArgument::Static(key.clone()),
                    m::TypeArgument::Symbolic(identity) => {
                        p::TypeArgument::Symbolic(identity.clone())
                    }
                })
                .collect(),
        },
        m::Ty::Generic(name) => p::Type::Generic(name.clone()),
        m::Ty::StaticKey(name) => p::Type::StaticKey(name.clone()),
        m::Ty::Projection { base, key } => p::Type::Projection {
            base: ty(types, base),
            key: key.clone(),
        },
        m::Ty::Immutable(inner) => p::Type::Immutable(ty(types, inner)),
        m::Ty::Optional(inner) => p::Type::Optional(ty(types, inner)),
        m::Ty::Result(ok, error) => p::Type::Result(ty(types, ok), ty(types, error)),
        m::Ty::Array(inner) => p::Type::Array(ty(types, inner)),
        m::Ty::Set(inner) => p::Type::Set(ty(types, inner)),
        m::Ty::Range(inner) => p::Type::Range(ty(types, inner)),
        m::Ty::Map(key, value) => p::Type::Map(ty(types, key), ty(types, value)),
        m::Ty::Tuple(items) => p::Type::Tuple(items.iter().map(|item| ty(types, item)).collect()),
        m::Ty::Record(fields) => p::Type::Record(
            fields
                .iter()
                .map(|(name, (mutable, value))| (name.clone(), *mutable, ty(types, value)))
                .collect(),
        ),
        m::Ty::OpenRecord { fields, row } => p::Type::OpenRecord {
            fields: fields
                .iter()
                .map(|(name, (mutable, value))| (name.clone(), *mutable, ty(types, value)))
                .collect(),
            row: p::OpenTail {
                identity: row_identity(&row.identity),
                lacks: row.lacks.iter().cloned().collect(),
            },
        },
        m::Ty::Callable(parameters, result) => p::Type::Callable(
            parameters
                .iter()
                .map(|parameter| ty(types, parameter))
                .collect(),
            ty(types, result),
        ),
    };
    let index = types
        .iter()
        .position(|ty| ty == &converted)
        .unwrap_or_else(|| {
            types.push(converted);
            types.len() - 1
        });
    TypeId(index as u32)
}
fn value(
    types: &mut Vec<p::Type>,
    contracts: &mut ReturnContracts,
    value: &m::Value,
    span: Span,
) -> p::Value {
    p::Value {
        source_type_witness: contracts.source_type_witness(value.source_type_witness.as_ref()),
        numeric: p::NumericDependencies {
            uses: value.numeric.uses.iter().copied().collect(),
            selections: value.numeric.selections.iter().copied().collect(),
        },
        condition_inspections: condition_inspections(&value.condition_inspections),
        pending_copies: value
            .pending_copies
            .iter()
            .map(|id| p::CopyBoundaryId(id.0))
            .collect(),
        span,
        ty: ty(types, &value.ty),
        origins: value.origins.nodes.iter().copied().map(origin).collect(),
        choices: value
            .origins
            .choices
            .iter()
            .map(|(branch, alternatives)| {
                (
                    *branch,
                    alternatives
                        .iter()
                        .map(|nodes| nodes.iter().copied().map(origin).collect())
                        .collect(),
                )
            })
            .collect(),
        permission: match value.permission {
            f::Permission::Read => p::Permission::Read,
            f::Permission::Write => p::Permission::Write,
        },
        publication: match value.publication {
            f::Publication::Immutable => p::Publication::Immutable,
            f::Publication::Live => p::Publication::Live,
            f::Publication::Unpublished => p::Publication::Unpublished,
        },
        participants: value
            .participants
            .iter()
            .copied()
            .map(participant)
            .collect(),
        sources: value.sources.iter().map(|id| *id as u32).collect(),
        callback_parameters: value
            .callback_parameters
            .iter()
            .map(|id| *id as u32)
            .collect(),
        results: value.results.iter().copied().collect(),
        outer_results: value.outer_results.iter().copied().collect(),
        must_results: value.must_results.iter().copied().collect(),
        must_outer_results: value.must_outer_results.iter().copied().collect(),
        scoped_bindings: value.scoped.iter().map(|&id| id as u32).collect(),
        result_payload: value
            .result_payload
            .as_ref()
            .map(|payload| Box::new(self::value(types, contracts, payload, span))),
        result_success: value
            .result_success
            .as_ref()
            .map(|payload| Box::new(self::value(types, contracts, payload, span))),
        result_error: value
            .result_error
            .as_ref()
            .map(|payload| Box::new(self::value(types, contracts, payload, span))),
        result_tag: value.result_tag,
        option_payload: value
            .option_payload
            .as_ref()
            .map(|payload| Box::new(self::value(types, contracts, payload, span))),
        option_tag: value.option_tag,
        option_identity: value.option_identity,
        variant_tag: value.variant_tag.clone(),
        variant_payload: value
            .variant_payload
            .as_ref()
            .map(|payload| Box::new(self::value(types, contracts, payload, span))),
        variant_witnesses: value
            .variant_witnesses
            .iter()
            .map(|(tag, payload)| {
                (
                    tag.clone(),
                    Box::new(self::value(types, contracts, payload, span)),
                )
            })
            .collect(),
        abnormal: value.abnormal,
        callables: value.callables.iter().map(callable).collect(),
        callable_returns: value
            .callable_returns
            .iter()
            .map(|bound| contracts.intern(types, bound))
            .collect(),
        signature: value.signature.as_ref().map(|parameters| {
            parameters
                .iter()
                .map(|parameter| p::Parameter {
                    name: if let PatternKind::Name(name) = &parameter.pattern.kind {
                        Some(name.clone())
                    } else {
                        None
                    },
                    mode: match parameter.mode {
                        ParameterMode::Read => p::Access::Read,
                        ParameterMode::Mut => p::Access::Write,
                        ParameterMode::SharedMut => p::Access::Retain,
                    },
                    type_annotation: parameter.ty.as_ref().map(|ty| ty.text.clone()),
                    default: parameter.default.as_ref().map(|value| value.span),
                })
                .collect()
        }),
        callable_bounds: value
            .callable_bounds
            .iter()
            .map(|bound| p::CallableBound {
                annotations: bound
                    .annotations
                    .iter()
                    .map(|annotation| p::Annotation {
                        kind: match annotation.kind {
                            ril_syntax::ast::AnnotationKind::Effect => p::AnnotationKind::Effect,
                            ril_syntax::ast::AnnotationKind::Capability => {
                                p::AnnotationKind::Capability
                            }
                        },
                        text: annotation.text.clone(),
                        span: annotation.span,
                    })
                    .collect(),
                lexical: bound
                    .lexical
                    .iter()
                    .map(|(name, &id)| (name.clone(), id as u32))
                    .collect(),
                span: bound.span,
            })
            .collect(),
        constant: value.constant.as_ref().map(|value| match value {
            m::Constant::Integer(value) => p::Constant::Integer(*value),
            m::Constant::Bool(value) => p::Constant::Bool(*value),
            m::Constant::Unit => p::Constant::Unit,
        }),
        static_coordinate: value
            .static_coordinate
            .as_ref()
            .map(|coordinate| match coordinate {
                m::StaticCoordinate::Label(label) => p::StaticCoordinate::Label(label.clone()),
                m::StaticCoordinate::Index(index) => p::StaticCoordinate::Index(*index),
            }),
        flags: p::ValueFlags {
            // Pending substitutions are stored separately from capability flags.
            stable: value.stable,
            marker: value.marker,
            retained_return: value.retention_result,
            through_return: value.through_return,
            construction: value.construction,
            internal_aliases: value.internal_aliases,
            mutable_environment: value.mutable_environment,
            observer_environment: value.observer_environment,
            unsuffixed_numeric: value.unsuffixed_numeric,
            temporary: value.temporary,
            readonly_spread: value.readonly_spread,
            requires_inference: value.requires_inference,
        },
        cause: value.cause,
        pending_inference: value.pending_inference.iter().cloned().collect(),
    }
}

fn condition_inspections(
    facts: &crate::sema::result_conditions::ConditionInspections,
) -> p::ConditionInspections {
    p::ConditionInspections {
        channel_when_true: channel_guard(&facts.channel_when_true),
        channel_when_false: channel_guard(&facts.channel_when_false),
        when_true: facts.when_true.iter().copied().collect(),
        when_false: facts.when_false.iter().copied().collect(),
        versions: facts
            .versions
            .iter()
            .map(|(id, version)| (*id, *version))
            .collect(),
        evaluations: facts
            .evaluations
            .iter()
            .map(|id| p::ConditionEvaluationId(id.0))
            .collect(),
    }
}

fn origin_fact(id: f::NodeId, node: &f::HeapNode) -> p::Origin {
    p::Origin {
        id: origin(id),
        multiplicity: match node.multiplicity {
            f::Multiplicity::One => p::Multiplicity::One,
            f::Multiplicity::MayMany => p::Multiplicity::MayMany,
        },
        kind: match node.kind {
            f::OriginKind::Formal(id) => p::OriginKind::Formal(id.0),
            f::OriginKind::Global => p::OriginKind::Global,
            f::OriginKind::Fresh(id) => p::OriginKind::Fresh(id.0),
            f::OriginKind::Older(id) => p::OriginKind::Older(id.0),
            f::OriginKind::Environment => p::OriginKind::Environment,
            f::OriginKind::Opaque => p::OriginKind::Opaque,
        },
        owner: node.owner.0,
        edges: node
            .fields
            .iter()
            .map(|(slot, origins)| {
                (
                    projection(slot),
                    origins.iter().copied().map(origin).collect(),
                )
            })
            .collect(),
        writable_roots: node.writable_roots.iter().map(|id| id.0).collect(),
        escaping: node.escaping,
        cause: node.cause,
    }
}

#[cfg(test)]
mod contract_graph_tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn complete_condition_metadata_preserves_operand_identity_without_inspecting_it() {
        use crate::sema::{channel_messages as c, copy_contract::CopyValueSnapshot};
        let span = Span {
            file: ril_compiler_core::source::FileId(0),
            start: 10,
            end: 30,
        };
        let cause = ril_compiler_core::diagnostic::CauseId(4);
        let mut value = m::Value::reference(
            m::Ty::Result(Box::new(m::Ty::Int("int".into())), Box::new(m::Ty::Str)),
            f::NodeId(7),
            cause,
        );
        value.permission = f::Permission::Read;
        value.construction = false;
        value.results.insert(3);
        value.outer_results.insert(3);
        let facts = SemanticFacts {
            channel_messages: vec![c::ChannelMessageFact {
                id: c::ChannelMessageId(2),
                source_event: None,
                repetition: None,
                sequence: 9,
                context: crate::sema::effect_identity::InvocationContext {
                    invocation: None,
                    owner: None,
                    closure: None,
                    closure_invocation: None,
                    budget_validation: false,
                    default_use: None,
                },
                task: None,
                activation: f::ScopeId(5),
                span,
                cause,
                allocation_epoch: 6,
                guard: c::ChannelGuard::always(),
                action: c::ChannelAction::ConditionEvaluated {
                    evaluation: crate::sema::result_conditions::ConditionEvaluationId(11),
                    subject_expression: 17,
                    subject: CopyValueSnapshot {
                        value,
                        nodes: vec![],
                        relations: vec![],
                    },
                },
            }],
            result_duties: vec![m::ResultDuty {
                id: 3,
                creation_owner: f::ScopeId(5),
                owner: f::ScopeId(5),
                span,
                cause,
                inspected: false,
                returned: false,
                abnormal: false,
                covered: false,
            }],
            ..Default::default()
        };
        // This tests metadata conversion, never Source authorization or normal
        // Core lowering. Only a verified program can take the latter path.
        let graph = lower(&facts).unwrap();
        let event = &graph.channel_messages[0];
        let p::ChannelAction::ConditionEvaluated {
            evaluation,
            subject_expression,
            subject,
        } = &event.action
        else {
            panic!("complete evaluation kind was erased");
        };
        assert_eq!(*evaluation, p::ConditionEvaluationId(11));
        assert_eq!(*subject_expression, 17);
        assert_eq!(event.sequence, 9);
        assert_eq!(event.allocation_epoch, 6);
        assert_eq!(event.cause, cause);
        assert_eq!(subject.value.origins, [OriginId(7)]);
        assert_eq!(subject.value.results, [3]);
        assert_eq!(subject.value.outer_results, [3]);
        assert!(matches!(subject.value.permission, p::Permission::Read));
        assert!(!subject.value.flags.construction);
        assert!(!graph.result_duties[0].inspected);
        assert!(!graph.result_duties[0].returned);
    }

    #[test]
    fn message_evidence_keeps_guard_uncertainty_and_snapshot_permissions() {
        use crate::sema::{
            channel_messages as c, copy_contract::CopyValueSnapshot,
            effect_identity::InvocationContext,
        };
        let span = Span {
            file: ril_compiler_core::source::FileId(0),
            start: 0,
            end: 1,
        };
        let guard = c::ChannelGuard {
            terms: [[c::GuardLiteral::Transport {
                event: c::ChannelMessageId(0),
                producer: 3,
                version: 8,
                success: false,
            }]
            .into()]
            .into(),
            incomplete: true,
        };
        let mut input = m::Value::reference(
            m::Ty::Array(Box::new(m::Ty::Int("int".into()))),
            f::NodeId(7),
            ril_compiler_core::diagnostic::CauseId(0),
        );
        input.permission = f::Permission::Read;
        input.publication = f::Publication::Immutable;
        input.construction = false;
        input.condition_inspections.channel_when_true = guard.clone();
        let snapshot = CopyValueSnapshot {
            value: input,
            nodes: vec![],
            relations: vec![],
        };
        let context = InvocationContext {
            invocation: None,
            owner: None,
            closure: None,
            closure_invocation: None,
            budget_validation: false,
            default_use: None,
        };
        let facts = SemanticFacts {
            channel_message_sequence: 2,
            channel_repetitions: vec![c::ChannelRepetition {
                id: c::ChannelRepetitionId(0),
                parent: None,
                context,
                activation: f::ScopeId(12),
                call: Some(crate::sema::copy_contract::CopyCallEventId(7)),
                start_sequence: 0,
                end_sequence: Some(2),
            }],
            channel_messages: vec![c::ChannelMessageFact {
                id: c::ChannelMessageId(0),
                source_event: Some(crate::sema::copy_contract::CopyCallEventId(7)),
                repetition: Some(c::ChannelRepetitionId(0)),
                sequence: 0,
                context,
                task: Some(f::NodeId(6)),
                activation: f::ScopeId(12),
                span,
                cause: ril_compiler_core::diagnostic::CauseId(0),
                allocation_epoch: 42,
                guard: guard.clone(),
                action: c::ChannelAction::Send {
                    endpoint: snapshot.clone(),
                    anchor: c::ChannelAnchor::Formal {
                        endpoint: f::NodeId(7),
                        scope: f::NodeId(4),
                    },
                    payload: snapshot.clone(),
                    transport: snapshot.clone(),
                    producer_versions: [(3, 8)].into(),
                    original_owners: [(3, f::ScopeId(12))].into(),
                    dependencies: [c::ChannelBindingPath {
                        binding: 9,
                        projection: vec![f::Slot::Field("item".into())],
                    }]
                    .into(),
                },
            }],
            channel_exits: vec![c::ChannelExitFact {
                sequence: 1,
                context,
                activation: f::ScopeId(12),
                span,
                cause: ril_compiler_core::diagnostic::CauseId(0),
                allocation_epoch: 42,
                guard,
                kind: c::ChannelExitKind::Callable,
                anchor: None,
                returned: snapshot,
            }],
            ..Default::default()
        };
        let graph = lower(&facts).unwrap();
        assert_eq!(graph.channel_message_sequence, 2);
        assert_eq!(
            graph.channel_messages[0].source_event,
            Some(p::CopyCallEventId(7))
        );
        assert_eq!(graph.channel_repetitions.len(), 1);
        assert_eq!(graph.channel_repetitions[0].activation, 12);
        assert_eq!(
            graph.channel_repetitions[0].call,
            Some(p::CopyCallEventId(7))
        );
        assert_eq!(graph.channel_repetitions[0].start_sequence, 0);
        assert_eq!(graph.channel_repetitions[0].end_sequence, Some(2));
        assert_eq!(
            graph.channel_messages[0].repetition,
            Some(p::ChannelRepetitionId(0))
        );
        assert_eq!(graph.channel_messages[0].activation, 12);
        assert_eq!(graph.channel_messages[0].task, Some(OriginId(6)));
        assert_eq!(graph.channel_messages[0].allocation_epoch, 42);
        assert!(graph.channel_messages[0].guard.incomplete);
        assert!(matches!(
            graph.channel_messages[0].guard.terms[0][0],
            p::ChannelGuardLiteral::Transport {
                event: p::ChannelMessageId(0),
                producer: 3,
                version: 8,
                success: false
            }
        ));
        let p::ChannelAction::Send {
            payload,
            original_owners,
            dependencies,
            ..
        } = &graph.channel_messages[0].action
        else {
            panic!("send kind erased")
        };
        assert!(matches!(payload.value.permission, p::Permission::Read));
        assert!(matches!(
            payload.value.publication,
            p::Publication::Immutable
        ));
        assert!(!payload.value.flags.construction);
        assert_eq!(payload.value.origins, [OriginId(7)]);
        assert!(
            payload
                .value
                .condition_inspections
                .channel_when_true
                .incomplete
        );
        assert_eq!(*original_owners, [(3, 12)]);
        assert_eq!(dependencies[0].binding, 9);
        assert!(matches!(
            graph.channel_exits[0].kind,
            p::ChannelExitKind::Callable
        ));
        assert!(graph.channel_exits[0].guard.incomplete);
    }

    #[test]
    fn result_presence_guard_projection_preserves_the_physical_generation() {
        use crate::sema::channel_messages::{ChannelGuard, GuardLiteral};
        let guard = ChannelGuard::literal(GuardLiteral::Result {
            producer: 17,
            version: 4,
            success: false,
        });
        let projected = channel_guard(&guard);
        assert!(!projected.incomplete);
        assert_eq!(projected.terms.len(), 1);
        assert_eq!(projected.terms[0].len(), 1);
        assert_eq!(
            projected.terms[0][0],
            p::ChannelGuardLiteral::Result {
                producer: 17,
                version: 4,
                success: false,
            }
        );
    }

    #[test]
    fn optional_presence_and_value_projection_keep_the_same_tag_identity() {
        use crate::sema::channel_messages::{ChannelGuard, GuardLiteral};
        let identity = ril_compiler_core::ids::OptionalTagId(17);
        let guard = ChannelGuard::literal(GuardLiteral::Optional {
            identity,
            present: false,
        });
        let projected = channel_guard(&guard);
        assert!(!projected.incomplete);
        assert_eq!(
            projected.terms,
            [vec![p::ChannelGuardLiteral::Optional {
                identity,
                present: false
            }]]
        );
        let inner = m::Ty::Int("int".into());
        let mut input = m::Value::scalar(
            m::Ty::Optional(Box::new(inner.clone())),
            None,
            ril_compiler_core::diagnostic::CauseId(0),
        );
        input.option_identity = Some(identity);
        input.option_payload = Some(Box::new(m::Value::scalar(inner, None, input.cause)));
        let mut types = vec![];
        let mut context = ReturnContracts::default();
        let output = value(
            &mut types,
            &mut context,
            &input,
            ril_compiler_core::source::Span {
                file: ril_compiler_core::source::FileId(0),
                start: 0,
                end: 0,
            },
        );
        assert_eq!(output.option_identity, Some(identity));
        assert!(matches!(output.permission, p::Permission::Read));
        assert!(output.results.is_empty());
        assert!(output.must_results.is_empty());
    }

    #[test]
    fn optional_tag_arena_projection_keeps_owner_cause_and_payload_type() {
        let mut facts = SemanticFacts::default();
        facts
            .optional_tags
            .push(crate::sema::optional_tags::OptionalTagFact {
                id: ril_compiler_core::ids::OptionalTagId(0),
                creation_owner: f::ScopeId(u32::MAX),
                cause: ril_compiler_core::diagnostic::CauseId(7),
                payload_type: m::Ty::Int("int".into()),
            });
        // This tests presentation only; a hand-built graph is not a verified
        // program or an authorization to lower source code.
        let projected = lower(&facts).unwrap();
        let [tag] = projected.optional_tags.as_slice() else {
            panic!("tag arena was erased")
        };
        assert_eq!(tag.id, ril_compiler_core::ids::OptionalTagId(0));
        assert_eq!(tag.creation_owner, u32::MAX);
        assert_eq!(tag.cause, ril_compiler_core::diagnostic::CauseId(7));
        assert!(
            matches!(&projected.types[tag.payload_type.0 as usize], p::Type::Integer(name) if name == "int")
        );
    }

    #[test]
    fn full_source_identity_is_exported_without_recovering_writes_or_freshness() {
        let parsed = ril_syntax::parse("type Shape=[0][2]int");
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let ril_syntax::ast::StmtKind::Type(declaration) = &parsed.program.statements[0].kind
        else {
            panic!("type declaration")
        };
        let syntax = declaration.value.clone().unwrap();
        let key = crate::static_eval::normalized_argument_key(&syntax);
        let mut input = m::Value::reference(
            m::Ty::Array(Box::new(m::Ty::Array(Box::new(m::Ty::Int("int".into()))))),
            f::NodeId(7),
            ril_compiler_core::diagnostic::CauseId(0),
        );
        input.permission = f::Permission::Read;
        input.publication = f::Publication::Immutable;
        input.construction = false;
        input.source_type_witness = Some(Arc::new(m::SourceTypeWitness {
            syntax,
            key: key.clone(),
        }));
        let mut types = vec![];
        let mut context = ReturnContracts::default();
        let output = value(&mut types, &mut context, &input, declaration.span);
        assert!(context.type_witness_error.is_none());
        let witness = output.source_type_witness.unwrap();
        assert_eq!(witness.key, key);
        let ril_ir::specialization::ArgumentKey::Array {
            length: Some(outer),
            element,
        } = &witness.shape
        else {
            panic!("outer dimension erased")
        };
        let ril_ir::specialization::ArgumentKey::Array {
            length: Some(inner),
            ..
        } = element.as_ref()
        else {
            panic!("empty outer array erased inner dimension")
        };
        assert_ne!(outer, inner);
        for _ in 0..10_000 {
            let repeated = value(&mut types, &mut context, &input, declaration.span);
            assert!(Arc::ptr_eq(
                &witness,
                repeated.source_type_witness.as_ref().unwrap()
            ));
        }
        assert_eq!(context.source_types.len(), 1);
        let mut bound = m::CallableReturnBound::raw(m::Callable::Closure(1), declaration.span);
        bound.raw = false;
        bound.target = input.ty.clone();
        let mut environment = bound.typing_environment.thaw();
        environment.generic_type_witnesses.insert(
            "creator:T".into(),
            input.source_type_witness.as_ref().unwrap().clone(),
        );
        bound.typing_environment = environment.freeze();
        let bound_id = context.intern(&mut types, &Arc::new(bound));
        let captured = &context.nodes[bound_id.0 as usize].generic_type_witnesses;
        assert_eq!(captured[0].0, "creator:T");
        assert!(Arc::ptr_eq(&witness, &captured[0].1));
        assert_eq!(output.origins, [OriginId(7)]);
        assert!(matches!(output.permission, p::Permission::Read));
        assert!(matches!(output.publication, p::Publication::Immutable));
        assert!(!output.flags.construction);
    }

    #[test]
    fn an_inconsistent_second_schema_cannot_hide_behind_an_interned_key() {
        let parsed = ril_syntax::parse("type Shape=[0][2]int");
        let ril_syntax::ast::StmtKind::Type(declaration) = &parsed.program.statements[0].kind
        else {
            panic!("type declaration")
        };
        let syntax = declaration.value.clone().unwrap();
        let key = crate::static_eval::normalized_argument_key(&syntax);
        let original = Arc::new(m::SourceTypeWitness {
            syntax: syntax.clone(),
            key: key.clone(),
        });
        let mut context = ReturnContracts::default();
        assert!(context.source_type_witness(Some(&original)).is_some());
        let mut tampered = syntax;
        tampered.kind = ril_syntax::ast::TypeKind::Tuple(vec![]);
        let tampered = Arc::new(m::SourceTypeWitness {
            syntax: tampered,
            key,
        });
        assert!(context.source_type_witness(Some(&tampered)).is_none());
        assert!(context.type_witness_error.is_some());
        let mut input =
            m::Value::scalar(m::Ty::Unit, None, ril_compiler_core::diagnostic::CauseId(0));
        input.source_type_witness = Some(tampered);
        let facts = SemanticFacts {
            expressions: vec![crate::sema::ExpressionFact {
                source_id: None,
                span: declaration.span,
                value: input,
            }],
            ..Default::default()
        };
        assert!(
            lower(&facts).is_err(),
            "malformed identity reached an ordinary Core graph"
        );
    }

    #[test]
    fn core_contract_arena_keeps_shared_diamonds_linear_and_raw_paths_explicit() {
        let span = Span {
            file: ril_compiler_core::source::FileId(0),
            start: 0,
            end: 1,
        };
        let mut heads = vec![Arc::new(m::CallableReturnBound::raw(
            m::Callable::Closure(1),
            span,
        ))];
        for level in 0..64 {
            let mut left = (*heads[0]).clone();
            left.raw = false;
            left.target = m::Ty::Int("int".into());
            left.predecessors = heads;
            left.span.start = level * 2;
            let mut right = left.clone();
            right.span.start += 1;
            heads = vec![Arc::new(left), Arc::new(right)];
        }
        let mut types = vec![];
        let mut arena = ReturnContracts::default();
        let ids: Vec<_> = heads
            .iter()
            .map(|head| arena.intern(&mut types, head))
            .collect();
        assert_eq!(
            arena.nodes.len(),
            129,
            "Core expanded the set of possible proof paths"
        );
        assert!(arena.nodes[0].raw);
        for (index, node) in arena.nodes.iter().enumerate() {
            assert!(
                node.predecessors
                    .iter()
                    .all(|parent| (parent.0 as usize) < index)
            );
        }
        let copied_again: Vec<_> = heads
            .iter()
            .map(|head| arena.intern(&mut types, head))
            .collect();
        assert_eq!(ids, copied_again);
        assert_eq!(arena.nodes.len(), 129);
    }
    #[test]
    fn original_builtin_headers_and_rows_survive_presentation_conversion() {
        use crate::sema::{builtin_sources::BuiltinSourceObservation, effect_identity as e};
        let parsed = ril_syntax::parse(
            "fn original(mut file:File::Handle,data:bytes)->Io::WriteProgress @Fiber &mut{}",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let ril_syntax::ast::StmtKind::Function(function) = &parsed.program.statements[0].kind
        else {
            unreachable!()
        };
        let facts = SemanticFacts {
            builtin_source_observations: vec![BuiltinSourceObservation {
                expression: 4,
                context: e::InvocationContext {
                    invocation: None,
                    owner: Some(ril_compiler_core::ids::CallableOwner::Function(
                        DefinitionId(3),
                    )),
                    closure: None,
                    closure_invocation: None,
                    budget_validation: false,
                    default_use: None,
                },
                identity: "File::write".into(),
                full_header: ril_syntax::ast::TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span: function.span,
                    kind: ril_syntax::ast::TypeKind::Callable {
                        parameters: function.parameters.clone(),
                        result: function.return_type.clone().map(Box::new),
                        annotations: function.annotations.clone(),
                    },
                },
                concrete_effects: ["Fiber".into()].into(),
                written_formals: [0].into(),
                captures: Default::default(),
                cause: ril_compiler_core::diagnostic::CauseId(17),
            }],
            ..Default::default()
        };
        // Presentation alone cannot certify these deliberately incomplete
        // facts. Conversion preserves the original contract without a Ty
        // reconstruction or loss of the qualifier annotations.
        let graph = lower(&facts).unwrap();
        let observation = &graph.builtin_source_observations[0];
        assert_eq!(observation.expression, 4);
        assert_eq!(observation.identity, "File::write");
        assert_eq!(observation.concrete_effects, ["Fiber".into()].into());
        assert_eq!(observation.written_formals, [0].into());
        assert!(observation.captures.is_empty());
        assert_eq!(observation.cause.0, 17);
        let p::ContractKind::Callable {
            parameters,
            result,
            annotations,
        } = &observation.full_header.kind
        else {
            unreachable!()
        };
        assert_eq!(parameters[0].mode, p::Access::Write);
        assert_eq!(parameters[1].mode, p::Access::Read);
        assert!(matches!(&result.as_ref().unwrap().kind,
            p::ContractKind::Name { path, .. } if path == &["Io", "WriteProgress"]));
        assert_eq!(
            annotations
                .iter()
                .map(|annotation| annotation.text.as_str())
                .collect::<Vec<_>>(),
            ["@Fiber", "&mut"]
        );
    }

    #[test]
    fn original_argument_and_default_epochs_survive_metadata_conversion() {
        use crate::sema::{copy_contract as c, default_uses as d, effect_identity as e};
        let span = Span {
            file: ril_compiler_core::source::FileId(0),
            start: 10,
            end: 14,
        };
        let input = m::Value::scalar(
            m::Ty::Int("int".into()),
            Some(m::Constant::Integer(7)),
            ril_compiler_core::diagnostic::CauseId(0),
        );
        let facts = SemanticFacts {
            invocation_expressions: vec![e::InvocationExpression {
                context: e::InvocationContext {
                    invocation: Some(crate::sema::copy_templates::InstanceId(4)),
                    owner: Some(ril_compiler_core::ids::CallableOwner::Function(
                        DefinitionId(3),
                    )),
                    closure: None,
                    closure_invocation: None,
                    budget_validation: false,
                    default_use: None,
                },
                expression: 0,
                argument_of: Some((c::CopyCallEventId(8), 0)),
            }],
            expressions: vec![crate::sema::ExpressionFact {
                source_id: None,
                span,
                value: input.clone(),
            }],
            call_arguments: vec![d::CallArguments {
                source_event: c::CopyCallEventId(8),
                target: Some(DefinitionId(7)),
                slots: vec![
                    d::ArgumentSource::Supplied,
                    d::ArgumentSource::Default(d::DefaultUseId(0)),
                ],
                supplied: [(
                    0,
                    d::SuppliedArgument {
                        expression: 0,
                        allocation_epoch: 2,
                    },
                )]
                .into(),
                evaluation_complete: false,
            }],
            default_uses: vec![d::DefaultUse {
                id: d::DefaultUseId(0),
                origin: d::DefaultOrigin::Call(c::CopyCallEventId(8)),
                target: Some(DefinitionId(7)),
                parameter: 1,
                caller: e::InvocationContext {
                    invocation: Some(crate::sema::copy_templates::InstanceId(4)),
                    owner: Some(ril_compiler_core::ids::CallableOwner::Function(
                        DefinitionId(3),
                    )),
                    closure: None,
                    closure_invocation: None,
                    budget_validation: false,
                    default_use: None,
                },
                owner: Some(ril_compiler_core::ids::CallableOwner::Function(
                    DefinitionId(7),
                )),
                span,
                arguments: vec![],
                captured_arguments: vec![],
                unresolved_captured_binders: Default::default(),
                evaluation_complete: false,
                status: c::CopyInvocationStatus::Unsupported,
                entered: vec![],
                result: Some(c::CopyValueSnapshot {
                    value: input,
                    nodes: vec![],
                    relations: vec![],
                }),
                result_allocation_epoch: Some(5),
                result_expression: None,
            }],
            ..Default::default()
        };
        // Conversion only: incomplete records do not establish Source entry.
        let graph = lower(&facts).unwrap();
        assert_eq!(graph.invocation_expressions[0].expression, 0);
        assert_eq!(
            graph.invocation_expressions[0].argument_of,
            Some((p::CopyCallEventId(8), 0))
        );
        assert_eq!(
            graph.invocation_expressions[0].context.owner,
            Some(ril_compiler_core::ids::CallableOwner::Function(
                DefinitionId(3)
            ))
        );
        let call = &graph.call_arguments[0];
        assert_eq!(call.source_event, p::CopyCallEventId(8));
        assert_eq!(call.supplied[&0].expression, 0);
        assert_eq!(call.supplied[&0].allocation_epoch, 2);
        assert_eq!(
            call.slots[1],
            p::ArgumentSource::Default(ril_ir::specialization::DefaultUseId(0))
        );
        assert!(!call.evaluation_complete);
        let default = &graph.default_uses[0];
        assert_eq!(default.result_allocation_epoch, Some(5));
        assert_eq!(default.result_expression, None);
        assert!(!default.evaluation_complete);
        assert!(matches!(
            default.status,
            p::CopyInvocationStatus::Unsupported
        ));
        assert!(default.entered.is_empty());
        assert!(matches!(
            default.result.as_ref().unwrap().value.permission,
            p::Permission::Read
        ));
        assert!(!default.result.as_ref().unwrap().value.flags.construction);
    }
}
