//! Allocation births are recorded at the shared heap entry, before recency
//! transport. A frozen node cannot borrow a different birth of the same site.
use super::{
    SemanticFacts,
    facts::{CauseKind, Multiplicity, NodeId, OriginKind, ScopeId, SiteId},
    pattern_windows::PatternWindowCreation,
};
use ril_compiler_core::{
    diagnostic::CauseId,
    ids::{ActivationEpochId, PatternId},
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct AllocationEventId(pub u32);

#[derive(Debug, Clone)]
pub struct AllocationEvent {
    pub id: AllocationEventId,
    pub site: SiteId,
    /// The actual recent node returned by the heap, before later reuse.
    pub recent: NodeId,
    pub remap: Option<(NodeId, NodeId)>,
    pub epoch_before: usize,
    pub cause: CauseId,
    pub owner: ScopeId,
    pub anchor: Option<ActivationEpochId>,
    /// Physical emission cursor at allocation, independent of diagnostic spans.
    pub position: usize,
}
impl AllocationEvent {
    pub fn epoch_after(&self) -> usize {
        self.epoch_before
            .saturating_add(usize::from(self.remap.is_some()))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PatternWindowSite {
    pub rest: PatternId,
    pub loop_owner: ScopeId,
    pub site: SiteId,
}

type Check<T = ()> = Result<T, String>;

fn charge(work: &mut usize, amount: usize) -> Check {
    let Some(left) = work.checked_sub(amount) else {
        *work = 0;
        return Err("allocation replay exceeds its shared work bound".into());
    };
    *work = left;
    Ok(())
}
fn require(condition: bool, message: &str) -> Check {
    condition.then_some(()).ok_or_else(|| message.into())
}
fn lookup(count: usize) -> usize {
    2 + count.checked_ilog2().unwrap_or(0) as usize
}
fn scope(facts: &SemanticFacts, id: ScopeId, work: &mut usize) -> Check {
    charge(work, lookup(facts.scopes.records().len()))?;
    require(
        facts.scopes.get(&id).is_some_and(|entry| entry.id == id),
        "allocation has no registered owner scope",
    )
}
fn lineage(facts: &SemanticFacts, mut id: ScopeId, work: &mut usize) -> Check<Vec<ScopeId>> {
    let mut path = Vec::new();
    let mut seen = BTreeSet::new();
    loop {
        scope(facts, id, work)?;
        charge(work, lookup(seen.len()) + 1)?;
        require(seen.insert(id), "allocation owner ancestry is cyclic")?;
        path.push(id);
        match facts.scopes.parent(&id) {
            Some(parent) => id = *parent,
            None => return Ok(path),
        }
    }
}
fn within(facts: &SemanticFacts, owner: ScopeId, parent: ScopeId, work: &mut usize) -> Check<bool> {
    let path = lineage(facts, owner, work)?;
    charge(work, path.len())?;
    Ok(path.contains(&parent))
}
fn common_owner(facts: &SemanticFacts, a: ScopeId, b: ScopeId, work: &mut usize) -> Check<ScopeId> {
    let a = lineage(facts, a, work)?;
    let b = lineage(facts, b, work)?;
    charge(work, a.len().saturating_mul(b.len()))?;
    let owner = b
        .into_iter()
        .find(|owner| a.contains(owner))
        // Heap::fresh_in_scopes uses the module owner for unrelated roots of
        // the scope forest. This conservative owner grants no local exemption.
        .unwrap_or(ScopeId(0));
    scope(facts, owner, work)?;
    Ok(owner)
}

fn birth(facts: &SemanticFacts, event: &AllocationEvent, work: &mut usize) -> Check {
    charge(work, 8)?;
    scope(facts, event.owner, work)?;
    let cause = facts
        .explanations
        .causes
        .get(event.cause.0 as usize)
        .ok_or("allocation birth has no registered cause")?;
    require(
        cause.id == event.cause
            && facts.explanations.kinds.get(event.cause.0 as usize) == Some(&CauseKind::Allocation)
            && cause.parents.is_empty(),
        "allocation birth borrowed another cause role",
    )?;
    require(
        event.position <= facts.expressions.len(),
        "allocation birth has no physical emission cursor",
    )?;
    let node = facts
        .heap
        .nodes
        .get(event.recent.0 as usize)
        .ok_or("allocation birth has no registered recent identity")?;
    require(
        node.kind == OriginKind::Fresh(event.site),
        "allocation birth changed its raw recent site",
    )?;
    if let Some(anchor) = event.anchor {
        let host = facts
            .activations
            .get(anchor.0 as usize)
            .ok_or("allocation birth lost its actual activation")?;
        require(
            host.id == anchor
                && host.start_expression <= event.position
                && host.end_expression.is_some_and(|end| event.position < end),
            "allocation birth is outside its actual activation",
        )?;
        if let Some(source) = host.source {
            charge(work, 1)?;
            require(
                facts
                    .semantic_hir
                    .as_deref()
                    .and_then(|hir| hir.expression(source))
                    .is_some(),
                "allocation activation has no original HIR",
            )?;
        }
        scope(facts, host.scope, work)?;
        // The current activation records when allocation happened; its scope
        // is not necessarily the destination owner. Catalog/signature graphs
        // and snapshots can be module-owned while a local call is active.
        // Role-specific receivers authenticate their required ownership below.
    }
    Ok(())
}

/// Reconstruct the outermost active loop frame from real activation parents
/// and original loop syntax, rather than trusting a caller-supplied scope tag.
fn loop_owner(facts: &SemanticFacts, event: &AllocationEvent, work: &mut usize) -> Check<ScopeId> {
    use crate::hir::nodes::ExprKind;
    let mut owner = event.owner;
    let mut anchor = event.anchor;
    let mut child_source = None;
    let mut seen = BTreeSet::new();
    while let Some(id) = anchor {
        charge(work, lookup(seen.len()) + 3)?;
        require(seen.insert(id), "allocation activation ancestry is cyclic")?;
        let host = facts
            .activations
            .get(id.0 as usize)
            .filter(|host| host.id == id)
            .ok_or("allocation loop context lost an actual activation")?;
        if let Some(source) = host.source {
            let syntax = facts
                .semantic_hir
                .as_deref()
                .and_then(|hir| hir.expression(source))
                .ok_or("allocation loop context lost original HIR")?;
            let active_loop = match &syntax.kind {
                ExprKind::Loop(_) | ExprKind::WhileLet { .. } => true,
                ExprKind::While { condition, .. } => child_source != Some(*condition),
                ExprKind::For { iterable, .. } => child_source != Some(*iterable),
                _ => false,
            };
            if active_loop && within(facts, event.owner, host.scope, work)? {
                owner = host.scope;
            }
        }
        child_source = host.source;
        anchor = host.parent;
    }
    Ok(owner)
}

/// Cross-link a window to one actual shared allocation. The enclosing replay
/// also authenticates the complete allocation ledger and unique consumption.
pub(crate) fn window_event<'a>(
    facts: &'a SemanticFacts,
    creation: &PatternWindowCreation,
    work: &mut usize,
) -> Check<&'a AllocationEvent> {
    charge(work, 10 + facts.pattern_window_sites.len())?;
    require(
        !facts.allocation_poisoned,
        "allocation recording was exhausted",
    )?;
    let event = facts
        .allocation_events
        .get(creation.allocation.0 as usize)
        .filter(|event| event.id == creation.allocation)
        .ok_or("window has no original allocation event")?;
    birth(facts, event, work)?;
    if let Some(anchor) = event.anchor {
        let host = &facts.activations[anchor.0 as usize];
        require(
            within(facts, event.owner, host.scope, work)?,
            "window allocation borrowed an unrelated receiving frame",
        )?;
    }
    require(
        event.recent == creation.output_node.origin
            && creation.output_node.fact.kind == OriginKind::Fresh(event.site)
            && event.cause == creation.output_node.fact.cause
            && event.owner == creation.owner
            && event.owner == creation.output_node.fact.owner
            && event.anchor == creation.anchor
            && event.epoch_after() == creation.heap.allocation_epoch
            && event.epoch_after() == creation.input.current_epoch()
            && event.epoch_after() == creation.output.current_epoch()
            && event.cause.0 < creation.info.cause.0,
        "window borrowed another allocation birth, epoch, owner or cause",
    )?;
    let mut sites = facts
        .pattern_window_sites
        .iter()
        .filter(|site| site.site == event.site);
    let site = sites
        .next()
        .ok_or("window allocation has no typed pattern site")?;
    require(
        sites.next().is_none(),
        "window allocation has ambiguous pattern sites",
    )?;
    let hir = facts
        .semantic_hir
        .as_deref()
        .ok_or("window allocation has no original HIR")?;
    require(
        site.rest == creation.rest
            && matches!(
                hir.pattern(site.rest).map(|node| &node.kind),
                Some(crate::hir::nodes::PatternKind::Rest(Some(_)))
            )
            && site.loop_owner == loop_owner(facts, event, work)?,
        "window allocation borrowed another pattern or loop context",
    )?;
    Ok(event)
}

struct SiteState {
    recent: NodeId,
    older: Option<(NodeId, CauseId, ScopeId)>,
    cause: CauseId,
    owner: ScopeId,
}

/// Replay identity transitions once, independently of all window snapshots.
/// Final heap fields are deliberately excluded: they are mutable storage state.
pub(crate) fn validate(facts: &SemanticFacts, work: &mut usize) -> Check {
    charge(work, 1)?;
    require(
        !facts.allocation_poisoned,
        "allocation recording was exhausted",
    )?;
    for count in [
        facts.allocation_events.len(),
        facts.allocation_history.len(),
        facts.heap.nodes.len(),
        facts.pattern_window_sites.len(),
        facts.pattern_windows.len(),
    ] {
        charge(work, count)?;
    }
    let mut sites = BTreeMap::<SiteId, SiteState>::new();
    let mut roles = BTreeMap::<NodeId, OriginKind>::new();
    let mut causes = BTreeSet::new();
    let mut epoch = 0;
    let mut previous: Option<&AllocationEvent> = None;
    for (ordinal, event) in facts.allocation_events.iter().enumerate() {
        charge(
            work,
            8 + lookup(sites.len()) + lookup(roles.len()) + lookup(causes.len()),
        )?;
        require(
            event.id.0 as usize == ordinal && event.epoch_before == epoch,
            "allocation ledger changed event order or history cursor",
        )?;
        if let Some(previous) = previous {
            require(
                previous.cause.0 < event.cause.0 && previous.position <= event.position,
                "allocation ledger reordered actual births",
            )?;
        }
        birth(facts, event, work)?;
        require(
            causes.insert(event.cause.0),
            "allocation ledger repeats one birth cause",
        )?;
        if let Some(state) = sites.get_mut(&event.site) {
            let (recent, older) = event
                .remap
                .ok_or("reused allocation site lost its recency transition")?;
            require(
                recent == state.recent && event.recent == recent && recent != older,
                "allocation reuse changed its raw recent identity",
            )?;
            require(
                facts.allocation_history.get(epoch) == Some(&(recent, older)),
                "allocation ledger disagrees with its actual recency history",
            )?;
            epoch += 1;
            let registered = facts
                .heap
                .nodes
                .get(older.0 as usize)
                .ok_or("allocation reuse lost its older identity")?;
            require(
                registered.kind == OriginKind::Older(event.site),
                "allocation reuse borrowed another older site",
            )?;
            state.older = Some(match state.older {
                Some((id, cause, owner)) => {
                    require(
                        id == older,
                        "allocation site changed its older summary identity",
                    )?;
                    (id, cause, common_owner(facts, owner, state.owner, work)?)
                }
                None => {
                    require(
                        roles.insert(older, OriginKind::Older(event.site)).is_none(),
                        "allocation summary aliases another registered role",
                    )?;
                    (older, state.cause, state.owner)
                }
            });
            state.cause = event.cause;
            state.owner = event.owner;
        } else {
            require(
                event.remap.is_none(),
                "first allocation borrowed an older history",
            )?;
            require(
                roles
                    .insert(event.recent, OriginKind::Fresh(event.site))
                    .is_none(),
                "allocation sites alias one raw identity",
            )?;
            sites.insert(
                event.site,
                SiteState {
                    recent: event.recent,
                    older: None,
                    cause: event.cause,
                    owner: event.owner,
                },
            );
        }
        previous = Some(event);
    }
    require(
        epoch == facts.allocation_history.len(),
        "allocation history has unrecorded births",
    )?;
    for state in sites.values() {
        charge(work, 4)?;
        let current = &facts.heap.nodes[state.recent.0 as usize];
        require(
            current.cause == state.cause && current.owner == state.owner,
            "registered recent identity changed its latest allocation birth",
        )?;
        if let Some((id, cause, owner)) = state.older {
            let summary = &facts.heap.nodes[id.0 as usize];
            require(
                summary.cause == cause
                    && summary.owner == owner
                    && summary.multiplicity == Multiplicity::MayMany,
                "registered older identity changed its actual allocation ancestry",
            )?;
        }
    }
    for (index, node) in facts.heap.nodes.iter().enumerate() {
        if matches!(node.kind, OriginKind::Fresh(_) | OriginKind::Older(_)) {
            charge(work, lookup(roles.len()))?;
            require(
                roles.get(&NodeId(index as u32)) == Some(&node.kind),
                "registered allocation identity has no actual birth coverage",
            )?;
        }
    }

    let mut registry = BTreeMap::new();
    let mut patterns = BTreeSet::new();
    for site in &facts.pattern_window_sites {
        charge(
            work,
            lookup(registry.len()) + lookup(patterns.len()) + lookup(sites.len()) + 2,
        )?;
        scope(facts, site.loop_owner, work)?;
        let hir = facts
            .semantic_hir
            .as_deref()
            .ok_or("pattern allocation registry has no original HIR")?;
        require(
            matches!(
                hir.pattern(site.rest).map(|node| &node.kind),
                Some(crate::hir::nodes::PatternKind::Rest(Some(_)))
            ),
            "pattern allocation registry has no original named rest",
        )?;
        require(
            registry.insert(site.site, site).is_none()
                && patterns.insert((site.rest, site.loop_owner)),
            "pattern allocation registry repeats a site or original role",
        )?;
        require(
            sites.contains_key(&site.site),
            "pattern allocation registry has no actual allocation",
        )?;
    }
    let mut consumed = BTreeSet::new();
    for creation in &facts.pattern_windows {
        let event = window_event(facts, creation, work)?;
        charge(work, lookup(consumed.len()))?;
        require(
            consumed.insert(event.id),
            "windows reused one actual allocation event",
        )?;
    }
    for event in &facts.allocation_events {
        charge(work, lookup(registry.len()) + lookup(consumed.len()))?;
        if registry.contains_key(&event.site) {
            require(
                consumed.contains(&event.id),
                "typed pattern allocation lost its window construction",
            )?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
