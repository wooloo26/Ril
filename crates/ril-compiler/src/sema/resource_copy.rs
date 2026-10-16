//! Resource copying is a separate contract, never ordinary graph isolation.
use super::{ConcurrentBoundary, copy_contract::*, copy_templates::InstanceId, facts::NodeId};
use ril_compiler_core::{
    ids::{CallableOwner, DefinitionId},
    source::Span,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ResourceCloneId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResourceCloneContract {
    Sender,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResourceCloneEffect {
    Fiber,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResourceChannel {
    Known(NodeId),
    /// An explicit formal Sender contract preserves its unknown channel.
    FromSourceDescriptor(NodeId),
}

#[derive(Debug, Clone)]
pub struct ResourceDescriptor {
    pub origin: NodeId,
    pub scope: NodeId,
    pub task: Option<NodeId>,
    pub channel: Option<NodeId>,
    pub formal: bool,
}

#[derive(Debug, Clone)]
pub struct ResourceCloneEvent {
    pub id: ResourceCloneId,
    pub owner: Option<DefinitionId>,
    pub lexical_owner: Option<CallableOwner>,
    pub invocation: Option<InstanceId>,
    pub source_event: Option<CopyCallEventId>,
    pub span: Span,
    pub contract: ResourceCloneContract,
    pub required_effect: ResourceCloneEffect,
    pub effect_registered: bool,
    pub source: CopyValueSnapshot,
    pub source_descriptor: Option<ResourceDescriptor>,
    pub output: CopyValueSnapshot,
    pub output_descriptor: Option<ResourceDescriptor>,
    pub channel: Option<ResourceChannel>,
    /// Frozen proof produced by the existing checked resource operation.
    pub boundary: Option<ConcurrentBoundary>,
    /// Scope/task/channel identities are outside the ordinary reachable graph.
    /// Freeze their facts too, so later recency cannot reinterpret the event.
    pub anchors: Vec<CopyNode>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CopyDischarge {
    Ordinary(CopyBoundaryId),
    Sender(ResourceCloneId),
}

/// Validate the frozen intrinsic contract. Source task and current task may
/// differ: the existing concurrency checker admits ancestor clone-source loans.
pub fn sender_contract(
    event: &ResourceCloneEvent,
    call: &CopyInvocation,
    syntax: &CopyCallEvent,
) -> bool {
    call.status == CopyInvocationStatus::Completed
        && event.invocation == Some(call.id)
        && event.owner == Some(call.target)
        && event.source_event == Some(syntax.id)
        && syntax.parent == Some(call.id)
        && syntax.owner == event.lexical_owner
        && syntax.span == event.span
        && syntax.copy_operation == Some(CopyMode::Mutable)
        && call.resource_copies.contains(&event.id)
        && intrinsic_shape(event)
}

fn intrinsic_shape(event: &ResourceCloneEvent) -> bool {
    use super::{
        ConcurrentBoundaryKind,
        facts::{Multiplicity, Permission},
    };
    let (Some(source), Some(output), Some(boundary)) = (
        &event.source_descriptor,
        &event.output_descriptor,
        &event.boundary,
    ) else {
        return false;
    };
    let singleton = |snapshot: &CopyValueSnapshot, node: NodeId| {
        snapshot.value.origins.nodes == [node].into()
            && snapshot
                .nodes
                .iter()
                .any(|fact| fact.origin == node && fact.fact.multiplicity == Multiplicity::One)
            && snapshot.value.nested_copy_dependencies().is_empty()
    };
    let anchors: std::collections::BTreeSet<_> = std::iter::once(source.scope)
        .chain(source.task)
        .chain(source.channel)
        .chain(output.task)
        .collect();
    event.contract == ResourceCloneContract::Sender
        && event.required_effect == ResourceCloneEffect::Fiber
        && event.effect_registered
        && boundary.kind == ConcurrentBoundaryKind::CloneSender
        && boundary.span == event.span
        && source.scope == boundary.scope
        && output.scope == source.scope
        && output.task == boundary.task
        && source.origin != output.origin
        && singleton(&event.source, source.origin)
        && singleton(&event.output, output.origin)
        && event.output.value.permission == Permission::Write
        && anchors.iter().all(|node| {
            event
                .anchors
                .iter()
                .any(|fact| fact.origin == *node && fact.fact.multiplicity == Multiplicity::One)
        })
        && match event.channel {
            Some(ResourceChannel::Known(channel)) => {
                source.channel == Some(channel) && output.channel == Some(channel)
            }
            Some(ResourceChannel::FromSourceDescriptor(origin)) => {
                origin == source.origin
                    && source.formal
                    && output.formal
                    && source.channel.is_none()
                    && output.channel.is_none()
            }
            None => false,
        }
}
