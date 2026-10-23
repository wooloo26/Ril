//! Structural closure of a frozen heap view. The final heap registers origin
//! identities; its mutable fields cannot authenticate an earlier storage state.
use super::{
    SemanticFacts,
    copy_contract::{CopyNode, CopyValueView},
    facts::{NodeId, Slot},
    model::rows::RowIdentity,
    relations::Condition,
};
use std::collections::{BTreeMap, BTreeSet};

type Check<T = ()> = Result<T, String>;

fn charge(work: &mut usize, count: usize) -> Check {
    let Some(remaining) = work.checked_sub(count) else {
        *work = 0;
        return Err("frozen heap structure exceeds its shared work bound".into());
    };
    *work = remaining;
    Ok(())
}

fn require(condition: bool, message: &str) -> Check {
    condition.then_some(()).ok_or_else(|| message.into())
}

fn lookup_work(length: usize) -> usize {
    2 + length.checked_ilog2().unwrap_or(0) as usize
}

fn slot_work(slot: &Slot) -> usize {
    let bytes = match slot {
        Slot::Field(name) | Slot::RowTail(RowIdentity::Binder(name)) => name.len(),
        Slot::RowTail(RowIdentity::Fresh { owner, .. }) => owner.len(),
        _ => 0,
    };
    1 + bytes.div_ceil(32)
}

fn cause(facts: &SemanticFacts, cause: ril_compiler_core::diagnostic::CauseId) -> Check {
    require(
        facts
            .explanations
            .causes
            .get(cause.0 as usize)
            .is_some_and(|registered| registered.id == cause),
        "frozen heap constituent has no registered cause",
    )
}

fn fields(node: &CopyNode, nodes: &BTreeMap<NodeId, &CopyNode>, work: &mut usize) -> Check {
    charge(work, node.fields.len() + node.fact.fields.len() + 1)?;
    require(
        node.fields.len() == node.fact.fields.len(),
        "frozen heap stored edges lost their constituent values",
    )?;
    let mut actual = BTreeMap::new();
    let mut largest_slot = 1;
    for (slot, value) in &node.fields {
        largest_slot = largest_slot.max(slot_work(slot));
        charge(work, largest_slot.saturating_mul(lookup_work(actual.len())))?;
        require(
            actual.insert(slot, value).is_none(),
            "frozen heap repeats a stored constituent slot",
        )?;
    }
    for ((actual_slot, value), (slot, origins)) in actual.iter().zip(&node.fact.fields) {
        charge(
            work,
            slot_work(actual_slot)
                .max(slot_work(slot))
                .saturating_add(origins.len())
                .saturating_add(value.origins.nodes.len())
                .saturating_add(1),
        )?;
        require(
            *actual_slot == slot && value.origins.nodes == *origins,
            "frozen heap stored edges disagree with their constituent values",
        )?;
        for origin in origins {
            charge(work, lookup_work(nodes.len()))?;
            require(
                nodes.contains_key(origin),
                "frozen heap field points outside its graph",
            )?;
        }
    }
    Ok(())
}

/// Check only the frozen graph's complete structural domain. Historical field
/// contents, permissions and capture derivations still need their own receipts.
pub(crate) fn validate(facts: &SemanticFacts, view: CopyValueView<'_>, work: &mut usize) -> Check {
    charge(work, 1)?;
    charge(work, view.nodes.len())?;
    let mut nodes = BTreeMap::new();
    for node in view.nodes {
        charge(work, lookup_work(nodes.len()))?;
        require(
            nodes.insert(node.origin, node).is_none(),
            "frozen heap repeats an origin",
        )?;
        charge(work, lookup_work(facts.scopes.records().len()) + 2)?;
        require(
            facts.heap.nodes.get(node.origin.0 as usize).is_some()
                && facts
                    .scopes
                    .get(&node.fact.owner)
                    .is_some_and(|registered| registered.id == node.fact.owner),
            "frozen heap origin has no registered identity or scope",
        )?;
        cause(facts, node.fact.cause)?;
    }
    for node in view.nodes {
        charge(work, 1)?;
        fields(node, &nodes, work)?;
    }

    charge(work, 1)?;
    let mut values = vec![(view.value, 0usize)];
    let mut visited = BTreeSet::new();
    while let Some((value, depth)) = values.pop() {
        charge(work, 1)?;
        require(depth < 64, "frozen heap value exceeds its replay depth")?;
        cause(facts, value.cause)?;
        charge(
            work,
            value.origins.nodes.len() + value.origins.choices.len(),
        )?;
        for origin in &value.origins.nodes {
            charge(work, lookup_work(nodes.len()) + lookup_work(visited.len()))?;
            let node = nodes
                .get(origin)
                .ok_or("frozen heap value lost a reachable origin")?;
            if visited.insert(*origin) {
                charge(work, node.fields.len())?;
                values.extend(node.fields.iter().map(|(_, value)| (value, depth + 1)));
            }
        }
        for branches in value.origins.choices.values() {
            charge(work, branches.len())?;
            for branch in branches {
                charge(work, branch.len())?;
                for origin in branch {
                    charge(work, lookup_work(value.origins.nodes.len()))?;
                    require(
                        value.origins.nodes.contains(origin),
                        "frozen heap choice points outside its value's origins",
                    )?;
                }
            }
        }
        for payload in [
            &value.option_payload,
            &value.result_payload,
            &value.result_success,
            &value.result_error,
            &value.variant_payload,
        ] {
            charge(work, 1)?;
            if let Some(payload) = payload {
                charge(work, 1)?;
                values.push((payload.as_ref(), depth + 1));
            }
        }
        charge(work, value.variant_witnesses.len())?;
        for payload in value.variant_witnesses.values() {
            charge(work, 1)?;
            values.push((payload.as_ref(), depth + 1));
        }
    }
    require(
        visited.len() == nodes.len(),
        "frozen heap contains unobserved extra origins",
    )?;

    // Every unordered pair, including the diagonal, occurs exactly once. The
    // cardinality check plus membership/uniqueness avoids a second quadratic walk.
    charge(work, 1)?;
    let expected = nodes
        .len()
        .checked_add(1)
        .and_then(|next| nodes.len().checked_mul(next))
        .map(|pairs| pairs / 2)
        .ok_or("frozen heap relation domain overflows its replay bound")?;
    require(
        view.relations.len() == expected,
        "frozen heap relations do not cover its complete node domain",
    )?;
    charge(work, view.relations.len())?;
    let mut relations = BTreeSet::new();
    let conditions = facts.heap.conditions.node_count().saturating_add(2);
    for &(a, b, relation) in view.relations {
        charge(
            work,
            2 * lookup_work(nodes.len()) + lookup_work(relations.len()) + 1,
        )?;
        require(
            a <= b
                && nodes.contains_key(&a)
                && nodes.contains_key(&b)
                && relations.insert((a, b))
                && (relation.equal.0 as usize) < conditions
                && (relation.disjoint.0 as usize) < conditions
                && !(relation.equal == Condition::TRUE && relation.disjoint == Condition::TRUE),
            "frozen heap relations are unregistered, repeated or contradictory",
        )?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::{
        copy_contract::CopyValueSnapshot,
        facts::{CauseKind, HeapNode, Multiplicity, OriginKind, ScopeId, SiteId},
        model::{Ty, Value},
        relations::Relation,
    };
    use ril_compiler_core::diagnostic::CauseId;

    fn fixture() -> (SemanticFacts, CopyValueSnapshot) {
        let mut facts = SemanticFacts::default();
        facts.scopes.insert(ScopeId(0));
        let cause = facts
            .explanations
            .add(CauseKind::Allocation, None, "frozen graph model", []);
        let child = Slot::Field("child".into());
        let back = Slot::Field("back".into());
        let node = |site, slot, target| HeapNode {
            kind: OriginKind::Fresh(SiteId(site)),
            multiplicity: Multiplicity::One,
            owner: ScopeId(0),
            fields: BTreeMap::from([(slot, BTreeSet::from([NodeId(target)]))]),
            writable_roots: BTreeSet::new(),
            escaping: false,
            cause,
        };
        let first = node(0, child.clone(), 1);
        let second = node(1, back.clone(), 0);
        assert_eq!(facts.heap.insert(first.clone()), NodeId(0));
        assert_eq!(facts.heap.insert(second.clone()), NodeId(1));
        let reference = |origin| Value::reference(Ty::Unknown, NodeId(origin), cause);
        let snapshot = CopyValueSnapshot {
            value: reference(0),
            nodes: vec![
                CopyNode {
                    origin: NodeId(0),
                    fact: first,
                    fields: vec![(child, reference(1))],
                    length: None,
                    fixed: false,
                },
                CopyNode {
                    origin: NodeId(1),
                    fact: second,
                    fields: vec![(back, reference(0))],
                    length: None,
                    fixed: false,
                },
            ],
            relations: vec![
                (NodeId(0), NodeId(0), Relation::EQUAL),
                (NodeId(0), NodeId(1), Relation::DISJOINT),
                (NodeId(1), NodeId(1), Relation::EQUAL),
            ],
        };
        (facts, snapshot)
    }

    fn rejects(facts: &SemanticFacts, snapshot: &CopyValueSnapshot) {
        assert!(validate(facts, snapshot.as_view(), &mut 65_536).is_err());
    }

    #[test]
    fn frozen_heap_requires_its_root_and_exact_reachable_node_domain() {
        let (mut facts, snapshot) = fixture();
        validate(&facts, snapshot.as_view(), &mut 65_536).unwrap();
        let mut changed = snapshot.clone();
        changed.nodes.clear();
        changed.relations.clear();
        rejects(&facts, &changed);

        let mut changed = snapshot.clone();
        changed.nodes.push(snapshot.nodes[0].clone());
        rejects(&facts, &changed);

        let mut extra = snapshot.nodes[0].clone();
        extra.fields.clear();
        extra.fact.fields.clear();
        extra.origin = facts.heap.insert(extra.fact.clone());
        let mut changed = snapshot.clone();
        changed.nodes.push(extra);
        rejects(&facts, &changed);

        // The final heap is only the origin registry. Its later fields cannot
        // overwrite this independently retained historical graph.
        facts.heap.nodes[0].fields.clear();
        facts.heap.nodes[1].fields.clear();
        validate(&facts, snapshot.as_view(), &mut 65_536).unwrap();
    }

    #[test]
    fn frozen_heap_checks_stored_edges_choices_and_nested_payloads() {
        let (facts, snapshot) = fixture();
        for mutation in 0..5 {
            let mut changed = snapshot.clone();
            match mutation {
                0 => changed.nodes[0].fields.clear(),
                1 => changed.nodes[0].fact.fields.clear(),
                2 => changed.nodes[0].fields[0].1.origins.nodes.clear(),
                3 => changed.nodes[0]
                    .fields
                    .push(snapshot.nodes[0].fields[0].clone()),
                4 => {
                    changed
                        .value
                        .origins
                        .choices
                        .insert(0, vec![BTreeSet::from([NodeId(1)])]);
                }
                _ => unreachable!(),
            }
            rejects(&facts, &changed);
        }
        let mut nested = snapshot.clone();
        nested.value.origins.nodes.clear();
        nested.value.option_payload = Some(Box::new(snapshot.value.clone()));
        validate(&facts, nested.as_view(), &mut 65_536).unwrap();
        nested.value.option_payload.as_mut().unwrap().cause = CauseId(u32::MAX);
        rejects(&facts, &nested);

        let mut outside = snapshot.clone();
        outside.value.result_payload = Some(Box::new(Value::reference(
            Ty::Unknown,
            NodeId(2),
            snapshot.value.cause,
        )));
        rejects(&facts, &outside);
    }

    #[test]
    fn frozen_heap_requires_registered_origins_causes_and_scopes() {
        let (facts, snapshot) = fixture();
        for mutation in 0..4 {
            let mut changed = snapshot.clone();
            match mutation {
                0 => changed.nodes[0].origin = NodeId(u32::MAX),
                1 => changed.nodes[0].fact.owner = ScopeId(u32::MAX),
                2 => changed.nodes[0].fact.cause = CauseId(u32::MAX),
                3 => changed.value.cause = CauseId(u32::MAX),
                _ => unreachable!(),
            }
            rejects(&facts, &changed);
        }
    }

    #[test]
    fn frozen_heap_relations_cover_each_pair_without_contradiction() {
        let (facts, snapshot) = fixture();
        for mutation in 0..6 {
            let mut changed = snapshot.clone();
            match mutation {
                0 => {
                    changed.relations.pop();
                }
                1 => changed.relations[2] = changed.relations[0],
                2 => changed.relations[1].0 = NodeId(2),
                3 => changed.relations[1] = (NodeId(1), NodeId(0), Relation::DISJOINT),
                4 => {
                    changed.relations[1].2 = Relation {
                        equal: Condition::TRUE,
                        disjoint: Condition::TRUE,
                    };
                }
                5 => changed.relations[1].2.equal = Condition(u32::MAX),
                _ => unreachable!(),
            }
            rejects(&facts, &changed);
        }
    }

    #[test]
    fn frozen_heap_walk_spends_only_the_supplied_shared_budget() {
        let (facts, snapshot) = fixture();
        let mut remaining = 65_536;
        validate(&facts, snapshot.as_view(), &mut remaining).unwrap();
        let used = 65_536 - remaining;
        assert!(used > 0);
        let mut exact = used;
        validate(&facts, snapshot.as_view(), &mut exact).unwrap();
        assert_eq!(exact, 0);
        for mut short in [0, used - 1] {
            assert!(validate(&facts, snapshot.as_view(), &mut short).is_err());
            assert_eq!(short, 0);
        }
        let mut shared = used * 2;
        validate(&facts, snapshot.as_view(), &mut shared).unwrap();
        validate(&facts, snapshot.as_view(), &mut shared).unwrap();
        assert_eq!(shared, 0);
        assert!(validate(&facts, snapshot.as_view(), &mut shared).is_err());

        let mut deep = snapshot.clone();
        for _ in 0..64 {
            let mut outer = Value::scalar(Ty::Unknown, None, snapshot.value.cause);
            outer.option_payload = Some(Box::new(deep.value));
            deep.value = outer;
        }
        rejects(&facts, &deep);
    }
}
