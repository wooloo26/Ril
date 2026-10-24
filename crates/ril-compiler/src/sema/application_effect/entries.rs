//! Immutable callable inputs. Generated calls retain their actual value
//! derivations instead of borrowing an enclosing written application's slots.
use crate::sema::{
    copy_contract::{CopyBoundaryId, CopyCallEventId, CopyHeapSnapshot, CopyValueView},
    evaluated::EvaluatedValue,
    model::Value,
    source_types::{SourceTypesError, WorkLimit},
};
use ril_compiler_core::{
    ids::{ActivationEpochId, EvaluationOccurrenceId},
    source::Span,
};
use ril_syntax::ast::ParameterMode;
use std::sync::Arc;
#[path = "entry_packets.rs"]
mod packets;

#[derive(Debug, Clone)]
pub struct EntryArgument {
    pub mode: ParameterMode,
    pub packet: Arc<EvaluatedValue>,
    pub span: Span,
    pub heap: Option<Arc<CopyHeapSnapshot>>,
}

impl EntryArgument {
    pub fn value(&self) -> &Value {
        self.packet.value()
    }

    pub(crate) fn snapshot_view(
        &self,
        work: &mut WorkLimit,
    ) -> Result<CopyValueView<'_>, SourceTypesError> {
        work.charge(1)?;
        let heap = self.heap.as_deref().ok_or(SourceTypesError::MissingNode)?;
        if self.packet.current_epoch() != heap.allocation_epoch {
            return Err(SourceTypesError::Unresolved);
        }
        Ok(CopyValueView {
            value: self.packet.value(),
            nodes: &heap.nodes,
            relations: &heap.relations,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InputOrigin {
    Scope(u32),
    Observed(EvaluationOccurrenceId),
    Widened(EvaluationOccurrenceId),
    Scalar(ScalarInput),
    Copied {
        observation: EvaluationOccurrenceId,
        boundary: CopyBoundaryId,
    },
}

/// Historical coordinates of the scope token created by one physical
/// Concurrent::scope application. Recency transport never rewrites this birth.
#[derive(Debug, Clone)]
pub struct ScopeInput {
    pub application: CopyCallEventId,
    pub anchor: ActivationEpochId,
    pub node: crate::sema::facts::NodeId,
    pub cause: ril_compiler_core::diagnostic::CauseId,
    pub allocation_epoch: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarInput {
    PositiveInt,
    ByteSuffix(EvaluationOccurrenceId),
    BufferedBytes(EvaluationOccurrenceId),
}

pub(crate) struct RecordCallback {
    pub receiver: u32,
    pub operations: u32,
    pub field: &'static str,
    pub scalar_source: ScalarSource,
}
pub(crate) enum ScalarSource {
    PositiveInt,
    ByteSuffix(u32),
    BufferedBytes(u32),
}
pub(crate) fn record_callback(name: &str) -> Option<RecordCallback> {
    Some(match name {
        "Io::read_all" => RecordCallback {
            receiver: 0,
            operations: 1,
            field: "read",
            scalar_source: ScalarSource::PositiveInt,
        },
        "Io::write_all" => RecordCallback {
            receiver: 0,
            operations: 2,
            field: "write",
            scalar_source: ScalarSource::ByteSuffix(1),
        },
        "Io::read_buffered" => RecordCallback {
            receiver: 1,
            operations: 2,
            field: "read",
            scalar_source: ScalarSource::PositiveInt,
        },
        "Io::write_buffered" | "Io::flush" | "Io::close_write_buffer" => RecordCallback {
            receiver: 1,
            operations: 2,
            field: "write",
            scalar_source: ScalarSource::BufferedBytes(0),
        },
        _ => return None,
    })
}

/// A physical field operand of a record construction, without synthesizing
/// another evaluation of that construction or guessing by source position.
pub(crate) fn record_field_source(
    hir: &crate::hir::nodes::HirProgram,
    root: ril_compiler_core::ids::ExprId,
    field: &str,
    work: &mut usize,
) -> Option<ril_compiler_core::ids::ExprId> {
    use crate::hir::nodes::{ExprKind, RecordMember};
    let ExprKind::Record { members, .. } = &hir.expression(root)?.kind else {
        return None;
    };
    *work = work.checked_sub(members.len())?;
    let mut found = None;
    for member in members {
        let RecordMember::Field { name, value, .. } = member else {
            return None;
        };
        *work = work.checked_sub(name.len().max(field.len()).div_ceil(32))?;
        if name == field && found.replace(*value).is_some() {
            return None;
        }
    }
    found
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EntryOrigin {
    Application(CopyCallEventId),
    Generated {
        anchor: ActivationEpochId,
        callee: EvaluationOccurrenceId,
        inputs: Vec<InputOrigin>,
    },
    DeclarationProbe,
    SignatureProbe(Arc<super::SignatureProbeSource>),
    /// An unmigrated generated entry retains an explicit source obligation.
    Unresolved,
}

#[derive(Debug, Clone)]
pub struct CallableEntry {
    pub parent: Option<ActivationEpochId>,
    pub caller_context: super::InvocationContext,
    pub origin: EntryOrigin,
    pub allocation_epoch: usize,
    pub callee: Option<Arc<EvaluatedValue>>,
    /// The original argument vector is moved into shared immutable storage;
    /// entry recording never recursively clones the values or their syntax.
    pub arguments: Arc<Vec<EntryArgument>>,
}

impl super::ApplicationEffectDomain {
    pub(crate) fn snapshot_origin(&mut self, origin: &EntryOrigin) -> Option<EntryOrigin> {
        let cost = match origin {
            EntryOrigin::Generated { inputs, .. } => inputs.len() + 1,
            EntryOrigin::SignatureProbe(_) => 1,
            _ => 0,
        };
        self.admit(cost).then(|| origin.clone())
    }
}

pub(super) fn validate(facts: &super::SemanticFacts) -> Result<(), String> {
    use crate::sema::{copy_contract::CopyInvocationStatus, model::Callable};
    use std::collections::{BTreeMap, BTreeSet};
    if facts.closure_invocations.len() > 1_000_000 || facts.copy_invocations.len() > 1_000_000 {
        return Err("callable entry arena exceeds its work bound".into());
    }
    let mut covered = BTreeSet::new();
    let mut generated = BTreeSet::new();
    let mut covered_named = BTreeSet::new();
    let mut generated_named = BTreeSet::new();
    let mut work = 4_000_000usize;
    let mut packets = packets::Replay::new(facts, &mut work)?;
    packets.physical_sources(&mut work)?;
    packets.pattern_windows(&mut work)?;
    work = work
        .checked_sub(facts.activations.len())
        .ok_or("callable body coverage exceeds its work bound")?;
    let mut bodies = BTreeMap::new();
    let mut named_roots = BTreeMap::<_, Vec<_>>::new();
    let mut children = BTreeMap::<_, Vec<_>>::new();
    for activation in &facts.activations {
        if activation.kind == super::ActivationKind::Expression
            && let Some(invocation) = activation.context.invocation
            && activation
                .parent
                .and_then(|id| facts.activations.get(id.0 as usize))
                .is_none_or(|parent| parent.context.invocation != Some(invocation))
        {
            named_roots.entry(invocation).or_default().push(activation);
        }
        if activation.kind == super::ActivationKind::Expression
            && let (Some(parent), Some(source)) = (activation.parent, activation.source)
        {
            children
                .entry((parent, source))
                .or_default()
                .push(activation);
        }
        let Some(id) = activation.context.closure_invocation else {
            continue;
        };
        let Some(call) = facts.closure_invocations.get(id.0 as usize) else {
            continue;
        };
        let Some(closure) = facts.closures.get(call.closure) else {
            continue;
        };
        if activation.kind == super::ActivationKind::Expression
            && activation.source.is_some()
            && activation.source == closure.body.hir_id
            && Some(activation.scope) == call.activation
            && bodies.insert(id, activation).is_some()
        {
            return Err("one callable entry claimed multiple original body roots".into());
        }
    }
    for proof in &facts.copy_boundaries {
        work = work
            .checked_sub(1)
            .ok_or("copy epoch coverage exceeds its work bound")?;
        if proof.input_allocation_epoch > facts.allocation_history.len()
            || proof.output.is_some() != proof.output_allocation_epoch.is_some()
            || proof.output_allocation_epoch.is_some_and(|epoch| {
                epoch < proof.input_allocation_epoch || epoch > facts.allocation_history.len()
            })
        {
            return Err("copy derivation changed its original input/output epochs".into());
        }
    }
    for (ordinal, call) in facts.closure_invocations.iter().enumerate() {
        let entry = &call.entry;
        packets.entry(
            entry,
            super::generated_entries::GeneratedEntryKey::Closure(call.id),
            &mut work,
        )?;
        work = work
            .checked_sub(1 + entry.arguments.len())
            .ok_or("callable input coverage exceeds its work bound")?;
        let closure = facts
            .closures
            .get(call.closure)
            .ok_or("callable entry has no original closure")?;
        if call.status == CopyInvocationStatus::Completed {
            let body = bodies
                .get(&call.id)
                .ok_or("callable entry lost its actual body activation")?;
            let epoch = body
                .result
                .and_then(|id| facts.evaluations.get(id.0 as usize))
                .map(|record| record.allocation_epoch);
            if body.parent != entry.parent
                || epoch.is_none_or(|epoch| epoch < entry.allocation_epoch)
            {
                return Err("callable entry borrowed another body's parent or birth epoch".into());
            }
        }
        if call.id.0 as usize != ordinal
            || entry.allocation_epoch > facts.allocation_history.len()
            || entry.caller_context.owner != call.caller_owner
            || entry.caller_context.invocation != call.parent_named
            || entry.caller_context.closure_invocation != call.parent_closure
            || (call.status == CopyInvocationStatus::Completed
                && (entry.arguments.len() != closure.parameters.len()
                    || entry
                        .arguments
                        .iter()
                        .zip(&closure.parameters)
                        .any(|(argument, parameter)| argument.mode != parameter.mode)))
        {
            return Err(
                "callable entry changed its original inputs, modes or caller context".into(),
            );
        }
        let mut source_work = crate::sema::source_types::WorkLimit::new(work);
        if let EntryOrigin::SignatureProbe(source) = &entry.origin {
            if !call.probe
                || call.source_event.is_some()
                || entry.arguments.len() != source.formals.len()
            {
                return Err("signature closure entry changed its original role or arity".into());
            }
            source
                .validate(
                    facts
                        .semantic_hir
                        .as_deref()
                        .ok_or("signature entry lost its original HIR")?,
                    &mut source_work,
                )
                .map_err(|error| format!("signature closure header failed: {error}"))?;
        }
        for (slot, entry_argument) in entry.arguments.iter().enumerate() {
            let argument = entry_argument.value();
            let mode = entry_argument.mode;
            if let EntryOrigin::SignatureProbe(source) = &entry.origin {
                source
                    .authenticate(
                        slot,
                        super::signature_inputs::SignatureInput {
                            value: argument,
                            mode,
                            scope: Some(call.caller_activation),
                            context: entry.caller_context,
                        },
                        facts
                            .semantic_hir
                            .as_deref()
                            .ok_or("signature entry lost its original HIR")?,
                        &facts.bindings,
                        &mut source_work,
                    )
                    .map_err(|error| {
                        format!("signature closure input lost its original header: {error}")
                    })?;
            } else if super::signature_inputs::requires_signature_origin(
                argument,
                Some(call.caller_activation),
                entry.caller_context,
                &facts.bindings,
                &mut source_work,
            )
            .map_err(|error| format!("signature closure input role failed: {error}"))?
            {
                return Err("universal closure input lost its signature entry source".into());
            }
        }
        work = source_work.remaining();
        match &entry.origin {
            EntryOrigin::Application(event) => {
                let event = facts
                    .copy_call_events
                    .get(event.0 as usize)
                    .filter(|actual| actual.id == *event)
                    .ok_or("callable entry has no original application")?;
                let parent = entry
                    .parent
                    .and_then(|id| facts.activations.get(id.0 as usize))
                    .ok_or("application entry has no owning evaluation activation")?;
                let callee = event
                    .callee_expression
                    .and_then(|id| facts.expressions.get(id).zip(facts.evaluations.get(id)))
                    .ok_or("application entry has no original callee")?;
                if parent.kind != super::ActivationKind::Expression
                    || parent.source != event.source_id
                    || parent.scope != call.caller_activation
                    || parent.context != entry.caller_context
                    || event.result_expression != parent.result.map(|id| id.0 as usize)
                    || !callee
                        .0
                        .value
                        .callables
                        .contains(&Callable::Closure(call.closure))
                    || callee.1.context != entry.caller_context
                {
                    return Err(
                        "application entry borrowed another callee, scope or activation".into(),
                    );
                }
                covered.insert((event.id, call.closure));
            }
            EntryOrigin::Generated { anchor, .. } => {
                let parent = facts
                    .activations
                    .get(anchor.0 as usize)
                    .ok_or("generated entry anchor is absent")?;
                if entry.parent != Some(*anchor)
                    || parent.kind != super::ActivationKind::Expression
                    || parent.scope != call.caller_activation
                    || parent.context != entry.caller_context
                {
                    return Err("generated entry borrowed another evaluation activation".into());
                }
                generated.insert((*anchor, call.closure));
            }
            EntryOrigin::DeclarationProbe | EntryOrigin::SignatureProbe(_) => {
                if !call.probe {
                    return Err("declaration entry claimed an actual invocation".into());
                }
            }
            EntryOrigin::Unresolved => {}
        }
    }
    work = work
        .checked_sub(facts.functions.len() + facts.invocation_calls.len() + facts.invocations.len())
        .ok_or("named callable coverage exceeds its work bound")?;
    let functions: BTreeMap<_, _> = facts
        .functions
        .iter()
        .map(|function| (function.definition, function))
        .collect();
    let mut callers = BTreeMap::new();
    for row in &facts.invocation_calls {
        if callers.insert(row.invocation, row).is_some() {
            return Err("named callable entry has duplicate original callers".into());
        }
    }
    crate::sema::summary::validate(facts, &mut work)?;
    for (ordinal, call) in facts.copy_invocations.iter().enumerate() {
        let entry = &call.entry;
        packets.entry(
            entry,
            super::generated_entries::GeneratedEntryKey::Named(call.id),
            &mut work,
        )?;
        work = work
            .checked_sub(1 + entry.arguments.len())
            .ok_or("named callable inputs exceed their work bound")?;
        let function = functions
            .get(&call.target)
            .ok_or("named callable entry has no original declaration")?;
        let row = callers
            .get(&call.id)
            .ok_or("named callable entry lost its original caller")?;
        if call.id.0 as usize != ordinal
            || entry.allocation_epoch > facts.allocation_history.len()
            || entry.caller_context.owner != call.caller_owner
            || entry.caller_context.invocation != call.parent
            || row.caller_owner != entry.caller_context.owner
            || row.caller_closure != entry.caller_context.closure
            || row.caller_closure_invocation != entry.caller_context.closure_invocation
            || row.default_use != entry.caller_context.default_use
            || (call.status == CopyInvocationStatus::Completed
                && matches!(
                    entry.origin,
                    EntryOrigin::Application(_) | EntryOrigin::Generated { .. }
                )
                && entry.arguments.len() != function.syntax.parameters.len())
            || (call.status == CopyInvocationStatus::Completed
                && entry.arguments.len() == function.syntax.parameters.len()
                && entry
                    .arguments
                    .iter()
                    .zip(&function.syntax.parameters)
                    .any(|(argument, parameter)| argument.mode != parameter.mode))
        {
            return Err(
                "named callable entry changed its original input modes or caller context".into(),
            );
        }
        let mut source_work = crate::sema::source_types::WorkLimit::new(work);
        if let EntryOrigin::SignatureProbe(source) = &entry.origin {
            if call.source_event.is_some()
                || call.declaration_probe
                || call.caller_owner.is_some()
                || entry.arguments.len() != source.formals.len()
            {
                return Err("signature named entry changed its original role or arity".into());
            }
            source
                .validate(
                    facts
                        .semantic_hir
                        .as_deref()
                        .ok_or("signature entry lost its original HIR")?,
                    &mut source_work,
                )
                .map_err(|error| format!("signature named header failed: {error}"))?;
        }
        for (slot, argument) in entry.arguments.iter().enumerate() {
            if matches!(entry.origin, EntryOrigin::SignatureProbe(_)) {
                super::signature_assumption(
                    call,
                    slot,
                    facts
                        .semantic_hir
                        .as_deref()
                        .ok_or("signature entry lost its original HIR")?,
                    &facts.bindings,
                    facts.allocation_history.len(),
                    &mut source_work,
                )
                .map_err(|error| {
                    format!("signature named input lost its original header: {error}")
                })?;
            } else if super::signature_inputs::requires_signature_origin(
                argument.value(),
                call.caller_activation,
                entry.caller_context,
                &facts.bindings,
                &mut source_work,
            )
            .map_err(|error| format!("signature named input role failed: {error}"))?
            {
                return Err("universal named input lost its signature entry source".into());
            }
        }
        work = source_work.remaining();
        match entry.origin {
            EntryOrigin::Application(id) => {
                let event = facts
                    .copy_call_events
                    .get(id.0 as usize)
                    .filter(|event| event.id == id)
                    .ok_or("named callable entry lost its original application")?;
                let parent = entry
                    .parent
                    .and_then(|id| facts.activations.get(id.0 as usize))
                    .ok_or("named callable application lost its owning activation")?;
                let callee = event
                    .callee_expression
                    .and_then(|id| facts.expressions.get(id))
                    .ok_or("named callable application lost its physical callee")?;
                if call.source_event != Some(id)
                    || parent.kind != super::ActivationKind::Expression
                    || parent.source != event.source_id
                    || Some(parent.scope) != call.caller_activation
                    || parent.context != entry.caller_context
                    || event.result_expression != parent.result.map(|id| id.0 as usize)
                    || !callee.value.callables.iter().any(|target| matches!(target,
                        Callable::Named(index) if facts.functions.get(*index).is_some_and(|function| function.definition == call.target)))
                {
                    return Err(
                        "named callable entry borrowed another application or target".into(),
                    );
                }
                covered_named.insert((id, call.target));
            }
            EntryOrigin::Generated { anchor, .. } => {
                let parent = facts
                    .activations
                    .get(anchor.0 as usize)
                    .ok_or("generated named callable lost its actual anchor")?;
                let summary = call
                    .summary
                    .and_then(|id| facts.invocations.get(id.0 as usize))
                    .ok_or("generated named callable lost its actual body scope")?;
                if call.source_event.is_some()
                    || call.declaration_probe
                    || entry.parent != Some(anchor)
                    || parent.kind != super::ActivationKind::Expression
                    || Some(parent.scope) != call.caller_activation
                    || parent.context != entry.caller_context
                    || summary.activation.is_none()
                    || summary.context.is_none_or(|context| {
                        context.owner
                            != Some(ril_compiler_core::ids::CallableOwner::Function(call.target))
                    })
                {
                    return Err(
                        "generated named callable borrowed another activation or body".into(),
                    );
                }
                for root in named_roots.get(&call.id).map_or(&[][..], Vec::as_slice) {
                    work = work
                        .checked_sub(1)
                        .ok_or("named body roots exceed their work bound")?;
                    if root.context.default_use != entry.caller_context.default_use {
                        continue;
                    }
                    if root.parent != entry.parent
                        || Some(root.scope) != summary.activation
                        || Some(root.context) != summary.context
                    {
                        return Err("generated named callable changed its actual body root".into());
                    }
                }
                generated_named.insert((anchor, call.target));
            }
            EntryOrigin::DeclarationProbe if !call.declaration_probe => {
                return Err("named declaration probe claimed an actual invocation".into());
            }
            EntryOrigin::DeclarationProbe
            | EntryOrigin::SignatureProbe(_)
            | EntryOrigin::Unresolved => {}
        }
    }
    for activation in &facts.activations {
        work = work
            .checked_sub(1)
            .ok_or("generated entry coverage exceeds its work bound")?;
        if activation.kind != super::ActivationKind::Expression {
            continue;
        }
        let Some(hir) = facts.semantic_hir.as_deref() else {
            continue;
        };
        let Some(crate::hir::nodes::Expr {
            kind:
                crate::hir::nodes::ExprKind::Binary {
                    operator,
                    left,
                    right,
                },
            ..
        }) = activation.source.and_then(|id| hir.expression(id))
        else {
            continue;
        };
        if !matches!(operator.as_str(), "|>" | "!>") {
            continue;
        }
        let Some(crate::hir::nodes::Expr {
            kind: crate::hir::nodes::ExprKind::Derive { base: None, recipe },
            ..
        }) = hir.expression(*right)
        else {
            continue;
        };
        let [input] = children
            .get(&(activation.id, *left))
            .map_or(&[][..], Vec::as_slice)
        else {
            return Err("generated invocation lost its unique evaluated input root".into());
        };
        if input
            .result
            .and_then(|id| facts.expressions.get(id.0 as usize))
            .is_some_and(|fact| fact.value.ty == crate::sema::model::Ty::Never)
        {
            continue;
        }
        let [callee] = children
            .get(&(activation.id, *recipe))
            .map_or(&[][..], Vec::as_slice)
        else {
            return Err("generated invocation lost its unique evaluated callee root".into());
        };
        let callee = callee
            .result
            .and_then(|id| facts.expressions.get(id.0 as usize))
            .ok_or("generated invocation callee is absent")?;
        work = work
            .checked_sub(callee.value.callables.len())
            .ok_or("generated target coverage exceeds its work bound")?;
        for target in &callee.value.callables {
            if let Callable::Closure(closure) = target
                && !generated.contains(&(activation.id, *closure))
            {
                return Err(
                    "generated invocation lost its original callable input derivation".into(),
                );
            }
            if let Callable::Named(target) = target
                && !facts.functions.get(*target).is_some_and(|function| {
                    generated_named.contains(&(activation.id, function.definition))
                })
            {
                return Err("generated named invocation lost its original input derivation".into());
            }
        }
    }
    work = work
        .checked_sub(facts.call_arguments.len())
        .ok_or("callable preparation coverage exceeds its work bound")?;
    let preparations: BTreeMap<_, _> = facts
        .call_arguments
        .iter()
        .map(|row| (row.source_event, row))
        .collect();
    for event in &facts.copy_call_events {
        work = work
            .checked_sub(1)
            .ok_or("callable application coverage exceeds its work bound")?;
        if !preparations
            .get(&event.id)
            .is_some_and(|row| row.evaluation_complete)
        {
            continue;
        }
        let Some(callee) = event
            .callee_expression
            .and_then(|id| facts.expressions.get(id))
        else {
            continue;
        };
        if let [Callable::Builtin(name)] = callee.value.callables.as_slice()
            && matches!(name.as_str(), "Io::read_all" | "Io::write_all")
        {
            let read = name == "Io::read_all";
            let row = preparations[&event.id];
            let projection = (|| {
                let ops = row.supplied.get(&(if read { 1 } else { 2 }))?.expression;
                let ops_fact = facts.expressions.get(ops)?;
                let parent = facts.evaluations.get(ops)?.identity?.activation;
                let field = record_field_source(
                    facts.semantic_hir.as_deref()?,
                    ops_fact.source_id?,
                    if read { "read" } else { "write" },
                    &mut work,
                )?;
                let [callee] = children.get(&(parent, field))?.as_slice() else {
                    return None;
                };
                let callee = facts.expressions.get(callee.result?.0 as usize)?;
                let anchor = facts
                    .evaluations
                    .get(event.result_expression?)?
                    .identity?
                    .activation;
                Some((anchor, callee))
            })();
            if let Some((anchor, callee)) = projection {
                work = work
                    .checked_sub(callee.value.callables.len())
                    .ok_or("record callback coverage exceeds its work bound")?;
                for target in &callee.value.callables {
                    match target {
                        Callable::Closure(target) if !generated.contains(&(anchor, *target)) => {
                            return Err(
                                "record callback lost its original closure input derivation".into(),
                            );
                        }
                        Callable::Named(target)
                            if !facts.functions.get(*target).is_some_and(|function| {
                                generated_named.contains(&(anchor, function.definition))
                            }) =>
                        {
                            return Err(
                                "record callback lost its original named input derivation".into()
                            );
                        }
                        _ => {}
                    }
                }
            }
        }
        work = work
            .checked_sub(callee.value.callables.len())
            .ok_or("callable target coverage exceeds its work bound")?;
        for target in &callee.value.callables {
            if let Callable::Closure(closure) = target
                && !covered.contains(&(event.id, *closure))
            {
                return Err(
                    "an entered lambda application lost its original callable inputs".into(),
                );
            }
            if let Callable::Named(target) = target
                && !facts.functions.get(*target).is_some_and(|function| {
                    covered_named.contains(&(event.id, function.definition))
                })
            {
                return Err(
                    "an entered named application lost its original callable inputs".into(),
                );
            }
        }
    }
    Ok(())
}
