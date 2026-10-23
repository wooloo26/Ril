//! Pattern windows are generated values, not fabricated slice expressions.
//! The type domain separately projects the declared Source through the same
//! original PatternId plan; this domain retains storage and capability inputs.
use super::{
    WindowInfo,
    copy_contract::CopyHeapSnapshot,
    effect_identity::InvocationContext,
    evaluated::EvaluatedValue,
    facts::{NodeId, Permission, Publication, ScopeId, Slot},
    model::{Origins, Ty, Value},
    source_types::SourceTypesError as Error,
};
use crate::hir::nodes::PatternValueProjection as Step;
use ril_compiler_core::{
    diagnostic::CauseId,
    ids::{ActivationEpochId, PatternId},
};
use std::sync::Arc;

#[derive(Debug, Clone, Copy)]
pub enum PatternWindowOrigin {
    Pattern(usize),
    Constant(ril_compiler_core::ids::ConstRef),
}

#[derive(Debug, Clone)]
pub struct PatternWindowInput {
    pub node: NodeId,
    pub origin: PatternWindowOrigin,
    pub info: WindowInfo,
}

#[derive(Debug, Clone)]
pub struct PatternWindowCreation {
    pub allocation: super::allocation::AllocationEventId,
    pub root: PatternId,
    pub rest: PatternId,
    pub anchor: Option<ActivationEpochId>,
    pub context: InvocationContext,
    pub owner: ScopeId,
    pub input: Arc<EvaluatedValue>,
    pub heap: Arc<CopyHeapSnapshot>,
    pub parents: Vec<PatternWindowInput>,
    pub prefix: u32,
    pub suffix: u32,
    pub output: Arc<EvaluatedValue>,
    pub output_node: super::copy_contract::CopyNode,
    pub info: WindowInfo,
}

fn charge(work: &mut usize, amount: usize) -> Result<(), Error> {
    *work = work.checked_sub(amount).ok_or(Error::BudgetExceeded)?;
    Ok(())
}

pub(crate) fn charge_info(info: &WindowInfo, work: &mut usize) -> Result<(), Error> {
    charge(
        work,
        5 + info.backing.nodes.len() + info.backing.choices.len(),
    )?;
    for branches in info.backing.choices.values() {
        charge(work, branches.len())?;
        for nodes in branches {
            charge(work, nodes.len())?;
        }
    }
    Ok(())
}

pub(crate) fn selection(
    hir: &crate::hir::nodes::HirProgram,
    root: PatternId,
    rest: PatternId,
    prefix: u32,
    suffix: u32,
    work: &mut usize,
) -> Result<Vec<Step>, Error> {
    let plan = hir
        .pattern_bindings(root, work)
        .map_err(|_| Error::Unresolved)?;
    charge(work, plan.len())?;
    let mut selected = None;
    for binding in plan {
        if binding.pattern == rest {
            selected = binding.selection;
        }
        for alternative in binding.alternatives {
            if alternative.pattern == rest {
                if selected.is_some() {
                    return Err(Error::Unresolved);
                }
                selected = alternative.selection;
            }
        }
    }
    let mut selected = selected.ok_or(Error::MissingProjection)?;
    if selected.pop() != Some(Step::ArrayRemainder { prefix, suffix }) {
        return Err(Error::MissingProjection);
    }
    Ok(selected)
}

fn node<'a>(
    heap: &'a CopyHeapSnapshot,
    id: NodeId,
    work: &mut usize,
) -> Result<&'a super::copy_contract::CopyNode, Error> {
    charge(work, heap.nodes.len())?;
    heap.nodes
        .iter()
        .find(|node| node.origin == id)
        .ok_or(Error::MissingNode)
}

pub(crate) fn length(
    value: &Value,
    heap: &CopyHeapSnapshot,
    parents: &[PatternWindowInput],
    work: &mut usize,
) -> Result<Option<u64>, Error> {
    charge(work, value.origins.nodes.len())?;
    let mut common = None;
    for id in &value.origins.nodes {
        charge(work, parents.len())?;
        let size = if let Some(parent) = parents.iter().find(|p| p.node == *id) {
            parent.info.length
        } else {
            node(heap, *id, work)?.length.flatten()
        };
        let Some(size) = size else { return Ok(None) };
        if common.is_some_and(|previous| previous != size) {
            return Ok(None);
        }
        common = Some(size);
    }
    Ok(common)
}

/// Stored descendants preserve their identities. Restrictions compose along
/// the real path; a type-only Element step never chooses an array position.
pub(crate) fn select_layer(
    hir: &crate::hir::nodes::HirProgram,
    root: &Value,
    heap: &CopyHeapSnapshot,
    parents: &[PatternWindowInput],
    path: &[Step],
    work: &mut usize,
) -> Result<Value, Error> {
    let mut current = super::evaluated::transport_value_at(root, &[], 0, 0, work)?;
    for step in path {
        charge(work, 2 + current.origins.nodes.len())?;
        super::evaluated::charge_value_export(&current, work)?;
        if let Step::Constructor(pattern) = step {
            let crate::hir::nodes::PatternKind::Constructor { path, .. } =
                &hir.pattern(*pattern).ok_or(Error::MissingNode)?.kind
            else {
                return Err(Error::MissingProjection);
            };
            charge(work, path.len())?;
            let name = path.last().ok_or(Error::MissingProjection)?;
            let witness = match name.as_str() {
                "Some" => current.option_payload.as_deref(),
                "Ok" => current.result_success.as_deref().or_else(|| {
                    (current.result_tag == Some(true))
                        .then_some(current.result_payload.as_deref())
                        .flatten()
                }),
                "Err" => current.result_error.as_deref().or_else(|| {
                    (current.result_tag == Some(false))
                        .then_some(current.result_payload.as_deref())
                        .flatten()
                }),
                _ => current
                    .variant_tag
                    .as_ref()
                    .filter(|tag| tag.rsplit("::").next() == Some(name.as_str()))
                    .and(current.variant_payload.as_deref()),
            }
            .ok_or(Error::Unresolved)?;
            let mut child = super::evaluated::transport_value_at(witness, &[], 0, 0, work)?;
            restrict(&mut child, &current);
            current = child;
            continue;
        }
        let slot = match step {
            Step::Field(name) => {
                charge(work, name.len().div_ceil(32))?;
                Slot::Field(name.clone())
            }
            Step::Tuple(index) => Slot::Tuple(*index),
            Step::TupleFromEnd(offset) => {
                let mut ty = &current.ty;
                while let Ty::Immutable(inner) = ty {
                    ty = inner;
                }
                let Ty::Tuple(items) = ty else {
                    return Err(Error::MissingProjection);
                };
                Slot::Tuple(
                    u32::try_from(
                        items
                            .len()
                            .checked_sub(*offset as usize)
                            .and_then(|n| n.checked_sub(1))
                            .ok_or(Error::MissingProjection)?,
                    )
                    .map_err(|_| Error::IdentityExhausted)?,
                )
            }
            Step::ArrayFront(index) => Slot::Index(i64::from(*index)),
            Step::ArrayBack(offset) => length(&current, heap, parents, work)?
                .and_then(|n| n.checked_sub(u64::from(*offset) + 1))
                .and_then(|n| i64::try_from(n).ok())
                .map(Slot::Index)
                .unwrap_or(Slot::AnyIndex),
            _ => return Err(Error::MissingProjection),
        };
        let mut values = Vec::new();
        for id in &current.origins.nodes {
            let mut origin = *id;
            let mut selected_slot = slot.clone();
            charge(work, parents.len())?;
            if let Some(parent) = parents.iter().find(|p| p.node == origin) {
                if parent.info.backing.nodes.len() != 1 {
                    return Err(Error::Unresolved);
                }
                origin = *parent
                    .info
                    .backing
                    .nodes
                    .first()
                    .ok_or(Error::MissingNode)?;
                selected_slot = match (&selected_slot, parent.info.lower) {
                    (Slot::Index(index), Some(lower)) => i64::try_from(lower)
                        .ok()
                        .and_then(|lower| lower.checked_add(*index))
                        .map(Slot::Index)
                        .unwrap_or(Slot::AnyIndex),
                    (Slot::Index(_), None) => Slot::AnyIndex,
                    _ => selected_slot,
                };
            }
            let stored = node(heap, origin, work)?;
            charge(work, stored.fields.len())?;
            if let Some((_, child)) = stored
                .fields
                .iter()
                .find(|(field, _)| *field == selected_slot)
            {
                values.push(super::evaluated::transport_value_at(
                    child,
                    &[],
                    0,
                    0,
                    work,
                )?);
            } else if matches!(selected_slot, Slot::Index(_) | Slot::AnyIndex) {
                for (_, child) in stored
                    .fields
                    .iter()
                    .filter(|(field, _)| matches!(field, Slot::Index(_) | Slot::AnyIndex))
                {
                    values.push(super::evaluated::transport_value_at(
                        child,
                        &[],
                        0,
                        0,
                        work,
                    )?);
                }
            }
        }
        let mut values = values.into_iter();
        let mut child = values.next().ok_or(Error::Unresolved)?;
        for other in values {
            super::evaluated::charge_value_export(&other, work)?;
            super::evaluated::charge_value_export(&child, work)?;
            child = child.join(&other, u32::MAX, current.cause);
            super::evaluated::charge_value_export(&child, work)?;
            super::model::forget_choices(&mut child);
        }
        restrict(&mut child, &current);
        current = child;
    }
    Ok(current)
}

fn restrict(child: &mut Value, current: &Value) {
    child.inherit_copy_dependencies(&current.nested_copy_dependencies());
    child.permission = child.permission.meet(current.permission);
    child.construction &= current.construction;
    child.publication = if child.publication == Publication::Immutable
        || current.publication == Publication::Immutable
    {
        Publication::Immutable
    } else if current.publication == Publication::Live {
        Publication::Live
    } else {
        child.publication
    };
    child.stable &= current.stable;
    child.sources = current.sources.clone();
    child.participants = current.participants.clone();
    child.scoped.extend(&current.scoped);
    child
        .callback_parameters
        .extend(&current.callback_parameters);
    child.temporary |= current.temporary;
    child.through_return |= current.through_return;
    child.marker = current.marker || current.construction && child.marker;
    child.retention_result =
        current.retention_result || current.construction && child.retention_result;
    if child.ty.scalar() {
        child.participants.clear();
        child.scoped.clear();
        child.temporary = false;
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn construct(
    source: &Value,
    heap: &CopyHeapSnapshot,
    parents: &[PatternWindowInput],
    node_id: NodeId,
    cause: CauseId,
    prefix: u32,
    suffix: u32,
    work: &mut usize,
) -> Result<(Value, Origins, Option<u64>, Option<u64>), Error> {
    charge(work, 4 + parents.len())?;
    super::evaluated::charge_value_export(source, work)?;
    let mut ty = &source.ty;
    while let Ty::Immutable(inner) = ty {
        ty = inner;
    }
    let Ty::Array(element) = ty else {
        return Err(Error::MissingProjection);
    };
    let source_length = length(source, heap, parents, work)?;
    let removed = u64::from(prefix) + u64::from(suffix);
    let remaining = source_length
        .map(|n| n.checked_sub(removed).ok_or(Error::MissingProjection))
        .transpose()?;
    let mut backing = source.origins.clone();
    let mut offset = Some(u64::from(prefix));
    if source.origins.nodes.len() > 1
        && source
            .origins
            .nodes
            .iter()
            .any(|id| parents.iter().any(|p| p.node == *id))
    {
        return Err(Error::Unresolved);
    }
    if let Some(parent) = source
        .origins
        .nodes
        .first()
        .and_then(|id| parents.iter().find(|p| p.node == *id))
    {
        if source.origins.nodes.len() != 1 {
            return Err(Error::Unresolved);
        }
        backing = parent.info.backing.clone();
        offset = parent
            .info
            .lower
            .and_then(|n| n.checked_add(u64::from(prefix)));
    }
    let mut value = Value::reference(Ty::Array(element.clone()), node_id, cause);
    value.permission = Permission::Read;
    value.publication = source.publication;
    value.construction = false;
    value.stable = source.stable || source.publication == Publication::Immutable;
    value.sources = source.sources.clone();
    value.participants = source.participants.clone();
    value.scoped = source.scoped.clone();
    value.temporary = source.temporary;
    value.callback_parameters = source.callback_parameters.clone();
    value.numeric = source.numeric.clone();
    value.pending_copies = source.nested_copy_dependencies();
    value.retention_result = source.retention_result;
    value.through_return = source.through_return;
    value.requires_inference = source.requires_inference;
    value.pending_inference = source.pending_inference.clone();
    value.internal_aliases = source.internal_aliases;
    value.mutable_environment = source.mutable_environment;
    value.observer_environment = source.observer_environment;
    // A finite exact slot domain can select its nested duties. A quantified
    // family needs a separate partition proof, never an assumed full traversal.
    if !source.results.is_empty() {
        if backing.nodes.len() != 1 {
            return Err(Error::Unresolved);
        }
        let lower = offset.ok_or(Error::Unresolved)?;
        let end = lower
            .checked_add(remaining.ok_or(Error::Unresolved)?)
            .ok_or(Error::Unresolved)?;
        for origin in &backing.nodes {
            let stored = node(heap, *origin, work)?;
            if stored.fact.multiplicity != super::facts::Multiplicity::One {
                return Err(Error::Unresolved);
            }
            charge(work, stored.fields.len())?;
            if stored
                .fields
                .iter()
                .any(|(slot, _)| matches!(slot, Slot::AnyIndex))
            {
                return Err(Error::Unresolved);
            }
            for (slot, child) in &stored.fields {
                if let Slot::Index(index) = slot
                    && u64::try_from(*index)
                        .ok()
                        .is_some_and(|index| index >= lower && index < end)
                {
                    value.results.extend(&child.results);
                    value.must_results.extend(&child.must_results);
                }
            }
        }
    }
    Ok((value, backing, offset, remaining))
}

/// Index entries are a cache of the selected backing slots, not independent
/// storage. Both normal windows and pattern windows use this same projection.
pub(crate) fn selected_fields<'a>(
    fields: impl IntoIterator<Item = (&'a Slot, &'a Value)>,
    lower: Option<u64>,
    length: Option<u64>,
    publication: Publication,
    cause: CauseId,
    work: &mut usize,
) -> Result<std::collections::BTreeMap<Slot, Value>, Error> {
    let mut selected = std::collections::BTreeMap::<Slot, Value>::new();
    for (slot, child) in fields {
        charge(
            work,
            2 + selected.len().checked_ilog2().unwrap_or(0) as usize,
        )?;
        let relative = match (slot, lower, length) {
            (Slot::Index(index), Some(lower), Some(length)) => {
                let Ok(index) = u64::try_from(*index) else {
                    continue;
                };
                if index < lower || index - lower >= length {
                    continue;
                }
                i64::try_from(index - lower)
                    .ok()
                    .map(Slot::Index)
                    .unwrap_or(Slot::AnyIndex)
            }
            (Slot::Index(_) | Slot::AnyIndex, _, _) => Slot::AnyIndex,
            _ => continue,
        };
        let mut value = super::evaluated::transport_value_at(child, &[], 0, 0, work)?;
        value.permission = Permission::Read;
        value.construction = false;
        value.marker = false;
        value.retention_result = false;
        if publication == Publication::Immutable || value.publication != Publication::Immutable {
            value.publication = publication;
        }
        if let Some(previous) = selected.remove(&relative) {
            super::evaluated::charge_value_export(&previous, work)?;
            super::evaluated::charge_value_export(&value, work)?;
            value = previous.join(&value, u32::MAX, cause);
            super::evaluated::charge_value_export(&value, work)?;
            super::model::forget_choices(&mut value);
        }
        selected.insert(relative, value);
    }
    Ok(selected)
}

fn require(condition: bool, message: &str) -> Result<(), String> {
    condition.then_some(()).ok_or_else(|| message.into())
}

pub(crate) fn info_at(
    info: &WindowInfo,
    history: &[(NodeId, NodeId)],
    from: usize,
    to: usize,
    work: &mut usize,
) -> Result<WindowInfo, String> {
    charge_info(info, work).map_err(|e| e.to_string())?;
    let mut info = info.clone();
    let moves = history
        .get(from..to)
        .ok_or("window history has invalid epochs")?;
    charge(work, moves.len()).map_err(|e| e.to_string())?;
    for &(recent, older) in moves {
        charge_info(&info, work).map_err(|e| e.to_string())?;
        info.backing.remap(recent, older);
    }
    Ok(info)
}

pub(crate) fn same_info(left: &WindowInfo, right: &WindowInfo) -> bool {
    left.pattern == right.pattern
        && left.constant == right.constant
        && left.backing == right.backing
        && left.lower == right.lower
        && left.length == right.length
        && left.cause == right.cause
}

/// Return the original entry for a destructured parameter, not an arbitrary
/// equal value elsewhere in the caller. Observed subjects are checked by the
/// shared physical-packet replay instead.
pub(crate) fn parameter_input<'a>(
    facts: &'a super::SemanticFacts,
    creation: &PatternWindowCreation,
    work: &mut usize,
) -> Result<Option<&'a super::application_effect::EntryArgument>, String> {
    use super::scopes::ScopeOrigin;
    charge(work, 3).map_err(|e| e.to_string())?;
    if creation.input.birth_coordinates().observation.is_some() {
        return Ok(None);
    }
    let scope = facts
        .scopes
        .get(&creation.owner)
        .ok_or("window parameter has no actual frame")?;
    let (parameters, entry) = match scope.origin {
        ScopeOrigin::Named(id) => {
            let call = facts
                .copy_invocations
                .get(id.0 as usize)
                .ok_or("window parameter lost its named entry")?;
            require(
                creation.context.invocation == Some(id),
                "window parameter borrowed another invocation",
            )?;
            charge(work, facts.functions.len()).map_err(|e| e.to_string())?;
            let function = facts
                .functions
                .iter()
                .find(|f| f.definition == call.target)
                .ok_or("window parameter lost its declaration")?;
            (&function.syntax.parameters, &call.entry)
        }
        ScopeOrigin::Closure(id) => {
            let call = facts
                .closure_invocations
                .get(id.0 as usize)
                .ok_or("window parameter lost its closure entry")?;
            require(
                creation.context.closure_invocation == Some(id),
                "window parameter borrowed another closure activation",
            )?;
            let closure = facts
                .closures
                .get(call.closure)
                .ok_or("window parameter lost its closure")?;
            (&closure.parameters, &call.entry)
        }
        _ => return Err("unobserved window subject has no original parameter entry".into()),
    };
    charge(work, parameters.len()).map_err(|e| e.to_string())?;
    let slot = parameters
        .iter()
        .position(|parameter| parameter.pattern.hir_id == Some(creation.root))
        .ok_or("window subject is not the original root parameter pattern")?;
    let argument = entry
        .arguments
        .get(slot)
        .ok_or("window root parameter has no actual input")?;
    require(
        argument.packet.shares_birth(&creation.input),
        "window parameter replaced its input packet birth",
    )?;
    Ok(Some(argument))
}

pub(crate) fn validate_creation(
    facts: &super::SemanticFacts,
    ordinal: usize,
    work: &mut usize,
) -> Result<(), String> {
    use super::facts::{CauseKind, Multiplicity, OriginKind};
    let creation = facts
        .pattern_windows
        .get(ordinal)
        .ok_or("window creation is absent")?;
    super::allocation::window_event(facts, creation, work)?;
    charge(work, 12 + creation.parents.len()).map_err(|e| e.to_string())?;
    let epoch = creation.heap.allocation_epoch;
    require(
        creation.input.current_epoch() == epoch
            && creation.output.current_epoch() == epoch
            && epoch <= facts.allocation_history.len(),
        "window input/output changed its construction epoch",
    )?;
    let hir = facts
        .semantic_hir
        .as_deref()
        .ok_or("window construction has no original HIR")?;
    let path = selection(
        hir,
        creation.root,
        creation.rest,
        creation.prefix,
        creation.suffix,
        work,
    )
    .map_err(|e| e.to_string())?;
    if let Some(anchor) = creation.anchor {
        let actual = facts
            .activations
            .get(anchor.0 as usize)
            .ok_or("window construction lost its owning activation")?;
        require(
            actual.id == anchor && actual.context == creation.context,
            "window construction borrowed another activation/context",
        )?;
    }
    let mut parent_nodes = std::collections::BTreeSet::new();
    for parent in &creation.parents {
        charge(
            work,
            1 + parent_nodes.len().checked_ilog2().unwrap_or(0) as usize,
        )
        .map_err(|error| error.to_string())?;
        require(
            parent_nodes.insert(parent.node),
            "window input repeats a parent identity",
        )?;
        match parent.origin {
            PatternWindowOrigin::Pattern(index) => {
                require(
                    index < ordinal,
                    "window creation borrowed a future or cyclic parent",
                )?;
                let original = &facts.pattern_windows[index];
                let expected = info_at(
                    &original.info,
                    &facts.allocation_history,
                    original.output.current_epoch(),
                    epoch,
                    work,
                )?;
                let output = super::evaluated::transport_value_at(
                    original.output.value(),
                    &facts.allocation_history,
                    original.output.current_epoch(),
                    epoch,
                    work,
                )
                .map_err(|e| e.to_string())?;
                require(
                    output.origins.nodes.contains(&parent.node)
                        && same_info(&expected, &parent.info),
                    "window parent changed its historical identity or selected interval",
                )?;
            }
            PatternWindowOrigin::Constant(reference) => {
                let original = facts
                    .constant_values
                    .get(reference.node.0 as usize)
                    .filter(|value| value.reference == reference)
                    .ok_or("window parent has no original constant")?;
                let constant = facts
                    .constant_pool
                    .nodes
                    .get(reference.node.0 as usize)
                    .ok_or("window constant is absent")?;
                let ril_ir::constants::ConstNodeKind::ArrayWindow {
                    backing,
                    start,
                    len,
                } = constant.kind
                else {
                    return Err("window parent is not an original constant window".into());
                };
                let backing_value = facts
                    .constant_values
                    .get(backing.node.0 as usize)
                    .filter(|v| v.reference == backing)
                    .ok_or("constant window backing is absent")?;
                let output = super::evaluated::transport_value_at(
                    &original.value,
                    &facts.allocation_history,
                    0,
                    epoch,
                    work,
                )
                .map_err(|e| e.to_string())?;
                let backing_value = super::evaluated::transport_value_at(
                    &backing_value.value,
                    &facts.allocation_history,
                    0,
                    epoch,
                    work,
                )
                .map_err(|e| e.to_string())?;
                require(
                    output.origins.nodes.contains(&parent.node)
                        && parent.info.constant == Some(reference)
                        && parent.info.pattern.is_none()
                        && parent.info.backing == backing_value.origins
                        && parent.info.lower == Some(start)
                        && parent.info.length == Some(len),
                    "constant window input changed its actual backing or interval",
                )?;
            }
        }
    }
    let input = super::copy_contract::CopyValueView {
        value: creation.input.value(),
        nodes: &creation.heap.nodes,
        relations: &creation.heap.relations,
    };
    super::heap_snapshot_validation::validate(facts, input, work)?;
    let layer = select_layer(
        hir,
        creation.input.value(),
        &creation.heap,
        &creation.parents,
        &path,
        work,
    )
    .map_err(|e| e.to_string())?;
    let output_node = &creation.output_node;
    let registered = facts
        .heap
        .nodes
        .get(output_node.origin.0 as usize)
        .ok_or("window header has no registered allocation identity")?;
    require(
        matches!(output_node.fact.kind, OriginKind::Fresh(_))
            && registered.kind == output_node.fact.kind
            && output_node.fact.multiplicity == Multiplicity::One
            && output_node.fact.owner == creation.owner
            && output_node.fact.writable_roots.is_empty()
            && !creation
                .heap
                .nodes
                .iter()
                .any(|node| node.origin == output_node.origin),
        "window header is not its own fresh read-only allocation",
    )?;
    let allocation = facts
        .explanations
        .causes
        .get(output_node.fact.cause.0 as usize)
        .ok_or("window header lost its original allocation cause")?;
    require(
        facts
            .explanations
            .kinds
            .get(output_node.fact.cause.0 as usize)
            == Some(&CauseKind::Allocation)
            && allocation.parents.is_empty()
            && output_node.fact.cause.0 < creation.info.cause.0,
        "window header borrowed a non-allocation cause",
    )?;
    let moves = facts
        .allocation_history
        .get(epoch..)
        .ok_or("window header lost its allocation cursor")?;
    charge(work, moves.len()).map_err(|error| error.to_string())?;
    if !moves
        .iter()
        .any(|(recent, _)| *recent == output_node.origin)
    {
        require(
            registered.cause == output_node.fact.cause,
            "window header changed its unreused allocation cause",
        )?;
    }
    let cause = facts
        .explanations
        .causes
        .get(creation.info.cause.0 as usize)
        .ok_or("window projection cause is absent")?;
    require(
        facts.explanations.kinds.get(creation.info.cause.0 as usize)
            == Some(&CauseKind::Projection)
            && cause.parents == [layer.cause],
        "window cause borrowed another storage selection",
    )?;
    let (expected, backing, lower, length) = construct(
        &layer,
        &creation.heap,
        &creation.parents,
        output_node.origin,
        creation.info.cause,
        creation.prefix,
        creation.suffix,
        work,
    )
    .map_err(|e| e.to_string())?;
    require(
        creation.info.pattern == Some(creation.rest)
            && creation.info.constant.is_none()
            && creation.info.backing == backing
            && creation.info.lower == lower
            && creation.info.length == length
            && output_node.length == Some(length)
            && !output_node.fixed,
        "window changed its original interval, declared role or backing",
    )?;
    require(
        super::evaluated::same_birth_value(&expected, creation.output.value(), work)
            .map_err(|e| e.to_string())?,
        "window changed its complete value, authority or duties",
    )?;
    let mut retained = layer;
    retained.origins = backing;
    retained.permission = Permission::Read;
    retained.construction = false;
    retained.marker = false;
    retained.retention_result = false;
    charge(work, creation.heap.nodes.len()).map_err(|e| e.to_string())?;
    let mut expected_fields = selected_fields(
        creation
            .heap
            .nodes
            .iter()
            .filter(|node| retained.origins.nodes.contains(&node.origin))
            .flat_map(|node| node.fields.iter().map(|(slot, value)| (slot, value))),
        lower,
        length,
        retained.publication,
        creation.info.cause,
        work,
    )
    .map_err(|error| error.to_string())?;
    expected_fields.insert(Slot::Field("ril__window_backing".into()), retained);
    charge(
        work,
        output_node.fields.len() + output_node.fact.fields.len(),
    )
    .map_err(|e| e.to_string())?;
    require(
        output_node.fields.len() == expected_fields.len()
            && output_node.fact.fields.len() == expected_fields.len(),
        "window header changed its retained backing or selected slot domain",
    )?;
    let mut seen = std::collections::BTreeSet::new();
    for (slot, actual) in &output_node.fields {
        charge(
            work,
            2 + expected_fields.len().checked_ilog2().unwrap_or(0) as usize,
        )
        .map_err(|e| e.to_string())?;
        let expected = expected_fields
            .get(slot)
            .ok_or("window header introduced an unrelated storage slot")?;
        require(
            seen.insert(slot)
                && super::evaluated::same_birth_value(expected, actual, work)
                    .map_err(|e| e.to_string())?
                && output_node.fact.fields.get(slot) == Some(&expected.origins.nodes),
            "window header changed its retained backing value or selected child",
        )?;
    }
    let current = super::evaluated::transport_value_at(
        creation.output.value(),
        &facts.allocation_history,
        epoch,
        facts.allocation_history.len(),
        work,
    )
    .map_err(|e| e.to_string())?;
    let current_node = current
        .origins
        .nodes
        .first()
        .ok_or("window output has no identity")?;
    require(
        facts
            .windows
            .get(current_node)
            .is_some_and(|info| info.pattern == Some(creation.rest)),
        "window construction is missing from the retained window domain",
    )?;
    // Ordinary and conditional bindings authenticate the original Source and
    // header interpretation separately, using this exact subject occurrence.
    if let Some(observation) = creation.input.birth_coordinates().observation {
        charge(work, facts.binding_sources.len()).map_err(|e| e.to_string())?;
        require(
            facts.binding_sources.iter().any(|row| {
                row.declaration == creation.root
                    && row.initializer.expression == observation
                    && row.context == creation.context
            }),
            "window has no original pattern receiving boundary",
        )?;
    } else {
        parameter_input(facts, creation, work)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::{
        copy_contract::CopyNode,
        facts::{Heap, Multiplicity, SiteId},
        model::Constant,
    };
    use std::collections::BTreeMap;

    fn array(children: Vec<Value>) -> (Value, CopyHeapSnapshot) {
        let mut heap = Heap::default();
        let (origin, _) = heap.fresh(SiteId(0), ScopeId(0), CauseId(0));
        let mut value = Value::reference(
            Ty::Array(Box::new(children[0].ty.clone())),
            origin,
            CauseId(0),
        );
        value.publication = Publication::Live;
        let length = children.len() as u64;
        let fields: Vec<_> = children
            .into_iter()
            .enumerate()
            .map(|(index, child)| {
                value.results.extend(&child.results);
                value.must_results.extend(&child.must_results);
                (Slot::Index(index as i64), child)
            })
            .collect();
        heap.nodes[0].fields = fields
            .iter()
            .map(|(slot, child)| (slot.clone(), child.origins.nodes.clone()))
            .collect();
        (
            value,
            CopyHeapSnapshot {
                allocation_epoch: 0,
                nodes: vec![CopyNode {
                    origin,
                    fact: heap.nodes[0].clone(),
                    fields,
                    length: Some(Some(length)),
                    fixed: false,
                }],
                relations: Vec::new(),
            },
        )
    }

    #[test]
    fn window_selects_exact_nested_duties_without_new_child_authority() {
        let children = (0..3)
            .map(|id| {
                let mut child = Value::scalar(
                    Ty::Result(Box::new(Ty::Int("int".into())), Box::new(Ty::Str)),
                    None,
                    CauseId(id),
                );
                child.results.insert(id);
                child.must_results.insert(id);
                child.outer_results.insert(id);
                child
            })
            .collect();
        let (source, heap) = array(children);
        let (value, backing, lower, length) = construct(
            &source,
            &heap,
            &[],
            NodeId(1),
            CauseId(4),
            1,
            1,
            &mut 10_000,
        )
        .unwrap();
        assert_eq!(value.origins.nodes, [NodeId(1)].into());
        assert_eq!(backing, source.origins);
        assert_eq!((lower, length), (Some(1), Some(1)));
        assert_eq!(value.results, [1].into());
        assert_eq!(value.must_results, [1].into());
        assert!(value.outer_results.is_empty());
        assert_eq!(value.permission, Permission::Read);
        assert_eq!(value.publication, Publication::Live);
        assert!(!value.construction);
        assert_eq!(source.permission, Permission::Write);
        assert_eq!(source.results, [0, 1, 2].into());
        let (empty, _, _, length) = construct(
            &source,
            &heap,
            &[],
            NodeId(2),
            CauseId(4),
            1,
            2,
            &mut 10_000,
        )
        .unwrap();
        assert_eq!(length, Some(0));
        assert!(empty.results.is_empty());
        assert!(matches!(
            construct(
                &source,
                &heap,
                &[],
                NodeId(2),
                CauseId(4),
                2,
                2,
                &mut 10_000,
            ),
            Err(Error::MissingProjection)
        ));
        let mut summary = heap.clone();
        summary.nodes[0].fact.multiplicity = Multiplicity::MayMany;
        assert!(matches!(
            construct(
                &source,
                &summary,
                &[],
                NodeId(2),
                CauseId(4),
                1,
                1,
                &mut 10_000,
            ),
            Err(Error::Unresolved)
        ));
        assert!(matches!(
            construct(&source, &heap, &[], NodeId(2), CauseId(4), 1, 1, &mut 0,),
            Err(Error::BudgetExceeded)
        ));
    }

    #[test]
    fn unknown_window_offset_cannot_select_the_backings_same_numbered_slot() {
        let children = [10, 20]
            .into_iter()
            .map(|number| {
                Value::scalar(
                    Ty::Int("int".into()),
                    Some(Constant::Integer(number.into())),
                    CauseId(0),
                )
            })
            .collect();
        let (backing, mut heap) = array(children);
        let mut window = backing.clone();
        window.origins = Origins::one(NodeId(1));
        window.permission = Permission::Read;
        window.construction = false;
        let info = WindowInfo {
            pattern: Some(PatternId(0)),
            constant: None,
            backing: backing.origins,
            lower: None,
            length: Some(2),
            span: ril_compiler_core::source::Span {
                file: ril_compiler_core::source::FileId(0),
                start: 0,
                end: 0,
            },
            cause: CauseId(0),
        };
        let mut header = heap.nodes[0].clone();
        header.origin = NodeId(1);
        header.fields.clear();
        header.fact.fields = BTreeMap::new();
        heap.nodes.push(header);
        let child = select_layer(
            &crate::hir::nodes::HirProgram::default(),
            &window,
            &heap,
            &[PatternWindowInput {
                node: NodeId(1),
                origin: PatternWindowOrigin::Pattern(0),
                info,
            }],
            &[Step::ArrayFront(0)],
            &mut 10_000,
        )
        .unwrap();
        assert!(child.constant.is_none());
        assert_eq!(child.permission, Permission::Read);
        assert!(!child.construction);
    }

    fn verified_windows(target: &str) -> crate::hir::VerifiedProgram {
        crate::Session::with_options(
            ril_test::case_bytes(
                "tests/conformance/rest-patterns.ril::nested-window-evidence-pointer32",
            )
            .to_vec(),
            crate::CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|error| panic!("{target}: {error:?}"))
    }

    #[test]
    fn window_derivations_reject_changed_inputs_roles_authority_and_storage() {
        type Mutation = fn(&mut crate::sema::SemanticFacts);
        let mutations: &[(&str, Mutation)] = &[
            ("root", |facts| {
                facts.pattern_windows[0].root = PatternId(u32::MAX)
            }),
            ("rest", |facts| {
                facts.pattern_windows[0].rest = PatternId(u32::MAX)
            }),
            ("interval", |facts| facts.pattern_windows[0].prefix += 1),
            ("allocation", |facts| {
                facts.pattern_windows[0].allocation =
                    super::super::allocation::AllocationEventId(u32::MAX)
            }),
            ("site", |facts| {
                facts.pattern_windows[0].output_node.fact.kind =
                    crate::sema::facts::OriginKind::Fresh(SiteId(u32::MAX))
            }),
            ("owner", |facts| {
                facts.pattern_windows[0].owner = ScopeId(u32::MAX)
            }),
            ("context", |facts| {
                facts.pattern_windows[0].context.owner = None
            }),
            ("input birth", |facts| {
                let creation = &mut facts.pattern_windows[0];
                creation.input = Arc::new(EvaluatedValue::new(
                    creation.input.value().clone(),
                    creation.input.current_epoch(),
                ));
            }),
            ("output authority", |facts| {
                Arc::make_mut(&mut facts.pattern_windows[0].output)
                    .value
                    .permission = Permission::Write
            }),
            ("backing", |facts| {
                let creation = &mut facts.pattern_windows[0];
                creation.info.backing = creation.output.value().origins.clone();
            }),
            ("selected child", |facts| {
                let (_, value) = facts.pattern_windows[0]
                    .output_node
                    .fields
                    .iter_mut()
                    .find(|(slot, _)| matches!(slot, Slot::Index(_)))
                    .unwrap();
                value.constant = Some(Constant::Integer(999.into()));
            }),
            ("parent", |facts| {
                let creation = facts
                    .pattern_windows
                    .iter_mut()
                    .find(|creation| !creation.parents.is_empty())
                    .unwrap();
                creation.parents[0].origin = PatternWindowOrigin::Pattern(usize::MAX);
            }),
            ("duplicate parent", |facts| {
                let creation = facts
                    .pattern_windows
                    .iter_mut()
                    .find(|creation| !creation.parents.is_empty())
                    .unwrap();
                creation.parents.push(creation.parents[0].clone());
            }),
        ];
        for target in ["pointer32", "pointer64"] {
            let verified = verified_windows(target);
            let facts = verified.facts();
            assert!(facts.pattern_windows.len() >= 3);
            for &(label, mutation) in mutations {
                let mut changed = facts.clone();
                mutation(&mut changed);
                assert!(
                    crate::sema::validate::solved_facts(&changed).is_err(),
                    "{target}: {label}"
                );
            }
        }
    }

    #[test]
    fn window_coverage_requires_creation_and_replayed_final_metadata() {
        for target in ["pointer32", "pointer64"] {
            let verified = verified_windows(target);
            let facts = verified.facts();
            let mut missing = facts.clone();
            missing.pattern_windows.clear();
            assert!(crate::sema::validate::solved_facts(&missing).is_err());
            let mut changed = facts.clone();
            changed
                .windows
                .values_mut()
                .find(|info| info.pattern.is_some())
                .unwrap()
                .lower = Some(999);
            assert!(crate::sema::validate::solved_facts(&changed).is_err());
        }
    }

    #[test]
    fn window_replay_consumes_one_exact_work_allowance() {
        for target in ["pointer32", "pointer64"] {
            let verified = verified_windows(target);
            let facts = verified.facts();
            let mut remaining = 4_000_000;
            validate_creation(facts, 0, &mut remaining).unwrap();
            let used = 4_000_000 - remaining;
            let mut exact = used;
            validate_creation(facts, 0, &mut exact).unwrap();
            assert_eq!(exact, 0);
            for mut short in [0, used - 1] {
                assert!(validate_creation(facts, 0, &mut short).is_err());
            }
        }
    }
}
