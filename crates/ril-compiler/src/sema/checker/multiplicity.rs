//! Abstract collection members can denote many concrete objects. Their formal
//! pivot identifies a family, not a singleton suitable for a strong heap write.
use super::*;

impl Checker {
    fn active_field_graph(&self, base: &Value, frame: &Frame) -> BTreeSet<NodeId> {
        // Finished definition probes are separate proof contexts. Include all
        // live bindings and the current lexical environment (including retained
        // captures whose creating scope has ended), never stale formal probes.
        let bindings = self
            .bindings
            .iter()
            .filter(|binding| binding.alive)
            .chain(frame.env.values().map(|id| &self.bindings[*id]));
        self.heap
            .reachable(
                base.origins
                    .nodes
                    .iter()
                    .copied()
                    .chain(bindings.flat_map(|binding| {
                        binding
                            .value
                            .origins
                            .nodes
                            .iter()
                            .copied()
                            .chain(binding.cell)
                    })),
            )
    }

    fn aliased_field_targets(
        &self,
        base: &Value,
        slot: &Slot,
        live: &BTreeSet<NodeId>,
    ) -> BTreeSet<(NodeId, Slot)> {
        let compatible_slot = |candidate: &Slot| match (slot, candidate) {
            (Slot::AnyIndex, Slot::AnyIndex | Slot::Index(_)) => true,
            (Slot::Index(_), Slot::AnyIndex) => true,
            _ => slot == candidate,
        };
        // Snapshot all possible targets before updating any of them. Separate
        // formal/copy nodes may be aliases; writing one must update the other's
        // may-state instead of preserving a stale, apparently disjoint child.
        let mut targets: BTreeSet<_> = self
            .fields
            .keys()
            .filter(|(node, candidate)| {
                live.contains(node)
                    && compatible_slot(candidate)
                    && base.origins.nodes.iter().any(|source| {
                        self.heap.relation(*source, *node).disjoint != Condition::TRUE
                    })
            })
            .cloned()
            .collect();
        targets.extend(base.origins.nodes.iter().map(|node| (*node, slot.clone())));
        targets
    }

    pub(super) fn result_field_update_is_closed(
        &self,
        base: &Value,
        slot: &Slot,
        value: &Value,
        frame: &Frame,
    ) -> bool {
        let inspected = |value: &Value| {
            self.result_family_closure(value.results.iter().copied())
                .iter()
                .all(|id| {
                    self.result_duties
                        .get(*id as usize)
                        .is_some_and(|duty| duty.inspected)
                })
        };
        if !inspected(value) {
            return false;
        }
        let live = self.active_field_graph(base, frame);
        self.aliased_field_targets(base, slot, &live)
            .iter()
            .all(|key| {
                self.fields.get(key).is_none_or(|old| {
                    old.results.is_empty()
                        || (self.heap.nodes[key.0.0 as usize].multiplicity == Multiplicity::One
                            && inspected(old))
                })
            })
    }

    pub(super) fn write_aliased_field(
        &mut self,
        base: &Value,
        slot: &Slot,
        value: &Value,
        frame: &Frame,
        span: Span,
    ) {
        let live = self.active_field_graph(base, frame);
        self.update_aliased_fields(base, slot, value, &live, span);
    }

    fn update_aliased_fields(
        &mut self,
        base: &Value,
        slot: &Slot,
        value: &Value,
        live: &BTreeSet<NodeId>,
        span: Span,
    ) {
        let targets = self.aliased_field_targets(base, slot, live);
        let previous: Vec<_> = targets
            .into_iter()
            .map(|key| {
                let old = self.fields.get(&key).cloned();
                (key, old)
            })
            .collect();
        for ((node, candidate), old) in previous {
            let strong = candidate == *slot
                && !matches!(slot, Slot::AnyIndex)
                && self.heap.relation(node, node).equal == Condition::TRUE
                && !base.origins.nodes.is_empty()
                && base
                    .origins
                    .nodes
                    .iter()
                    .all(|source| self.heap.relation(*source, node).equal == Condition::TRUE);
            let stored = if strong {
                self.uncertain_slots.remove(&(node, candidate.clone()));
                value.clone()
            } else if let Some(old) = old {
                let cause = self.cause(CauseKind::BranchJoin, span,
                    "possible alias or multi-object field update retains old and replacement constituents",
                    [base.cause, old.cause, value.cause]);
                let mut joined = old.join(value, self.choice(), cause);
                loop_graph::forget_choices(&mut joined);
                joined
            } else {
                value.clone()
            };
            self.store_field(node, candidate, stored);
        }
    }

    pub(super) fn mark_formal_member_family(&mut self, parent: NodeId, child: &Value) {
        for node in self.heap.reachable(child.origins.nodes.iter().copied()) {
            if !matches!(self.heap.nodes[node.0 as usize].kind, OriginKind::Formal(_)) {
                continue;
            }
            // A pre-existing summary with no collection reason (for example
            // an opaque row family) remains many even for a one-item array.
            if self.heap.nodes[node.0 as usize].multiplicity == Multiplicity::One
                || self.formal_family_parents.contains_key(&node)
            {
                self.formal_family_parents
                    .entry(node)
                    .or_default()
                    .insert(parent);
            }
            self.heap.set_relation(node, node, Relation::UNKNOWN);
        }
    }

    pub(super) fn prove_single_formal_member(&mut self, parent: NodeId) {
        if !matches!(
            self.heap.nodes[parent.0 as usize].kind,
            OriginKind::Formal(_)
        ) || self.array_lengths.get(&parent) != Some(&Some(1))
        {
            return;
        }
        let mut singletons = Vec::new();
        for (node, parents) in &mut self.formal_family_parents {
            if parents.remove(&parent) && parents.is_empty() {
                singletons.push(*node);
            }
        }
        for node in singletons {
            self.formal_family_parents.remove(&node);
            self.heap.prove_singleton_formal(node);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn weak_summary_writes_contain_every_concrete_two_iteration_state() {
        let slot = Slot::Field("child".into());
        for partition in 0u8..8 {
            for selected in 0..3 {
                for readonly in [false, true] {
                    let mut checker = Checker::new(FileId(0));
                    let nodes: Vec<_> = (0..6)
                        .map(|site| checker.heap.fresh(SiteId(site), ScopeId(0), CauseId(0)).0)
                        .collect();
                    let class = |object: usize| ((partition >> object) & 1) as usize;
                    for group in 0..2 {
                        let members: Vec<_> =
                            (0..3).filter(|object| class(*object) == group).collect();
                        if members.is_empty() {
                            continue;
                        }
                        if members.len() > 1 {
                            checker.heap.set_relation(
                                nodes[group],
                                nodes[group],
                                Relation::UNKNOWN,
                            );
                        }
                        let mut field = Value::reference(
                            Ty::Record(BTreeMap::new()),
                            nodes[members[0] + 2],
                            CauseId(0),
                        );
                        field.origins.nodes =
                            members.iter().map(|object| nodes[*object + 2]).collect();
                        if readonly {
                            field.permission = Permission::Read;
                        }
                        checker.store_field(nodes[group], slot.clone(), field);
                    }
                    let base = Value::reference(
                        Ty::Record(BTreeMap::new()),
                        nodes[class(selected)],
                        CauseId(0),
                    );
                    let replacement =
                        Value::reference(Ty::Record(BTreeMap::new()), nodes[5], CauseId(0));
                    checker.update_aliased_fields(
                        &base,
                        &slot,
                        &replacement,
                        &nodes.iter().copied().collect(),
                        Span {
                            file: FileId(0),
                            start: 0,
                            end: 1,
                        },
                    );
                    for object in 0..3 {
                        let expected = if object == selected {
                            nodes[5]
                        } else {
                            nodes[object + 2]
                        };
                        let actual = &checker.fields[&(nodes[class(object)], slot.clone())];
                        assert!(
                            actual.origins.nodes.contains(&expected),
                            "lost an unselected concrete object's field"
                        );
                        if readonly
                            && (0..3)
                                .filter(|other| class(*other) == class(object))
                                .count()
                                > 1
                        {
                            assert_eq!(actual.permission, Permission::Read);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn one_outer_member_does_not_make_its_inner_array_or_row_a_single_object() {
        let mut checker = Checker::new(FileId(0));
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 1,
        };
        let value = checker.formal_value(
            Ty::Array(Box::new(Ty::Array(Box::new(Ty::Record(BTreeMap::new()))))),
            0,
            span,
            &mut BTreeSet::new(),
        );
        let outer = *value.origins.nodes.first().unwrap();
        let inner = *checker.fields[&(outer, Slot::AnyIndex)]
            .origins
            .nodes
            .first()
            .unwrap();
        let member = *checker.fields[&(inner, Slot::AnyIndex)]
            .origins
            .nodes
            .first()
            .unwrap();
        checker.array_lengths.insert(outer, Some(1));
        checker.prove_single_formal_member(outer);
        assert_eq!(
            checker.heap.nodes[inner.0 as usize].multiplicity,
            Multiplicity::One
        );
        assert_eq!(
            checker.heap.nodes[member.0 as usize].multiplicity,
            Multiplicity::MayMany
        );
        checker.array_lengths.insert(inner, Some(1));
        checker.prove_single_formal_member(inner);
        assert_eq!(
            checker.heap.nodes[member.0 as usize].multiplicity,
            Multiplicity::One
        );
    }
}
