//! Exact immutable paths may preserve conditional producer presence. Absence
//! requires a complete construction graph, never just a missing observed edge.
use super::*;

impl Checker {
    pub(in crate::sema::checker) fn project_immutable_result_presence(
        &self,
        base: &Value,
        slot: &Slot,
        projected: &mut Value,
    ) {
        if base.publication != Publication::Immutable
            || matches!(slot, Slot::AnyIndex)
            || base.origins.nodes.is_empty()
            || self.has_unresolved_row(base)
        {
            return;
        }
        for id in base.must_results.intersection(&projected.results) {
            let present = base.origins.nodes.iter().all(|node| {
                if self
                    .uncertain_slots
                    .iter()
                    .any(|(parent, _)| parent == node)
                {
                    return false;
                }
                if self
                    .fields
                    .get(&(*node, slot.clone()))
                    .is_some_and(|value| value.must_results.contains(id))
                {
                    return true;
                }
                self.complete_constructed_results(
                    *node,
                    &self.collection_type(base),
                    &mut BTreeSet::new(),
                )
                .is_some_and(|all| !all.contains(id))
            });
            if present {
                projected.must_results.insert(*id);
            }
        }
    }

    fn complete_result_value(
        &self,
        value: &Value,
        seen: &mut BTreeSet<NodeId>,
    ) -> Option<BTreeSet<u32>> {
        if self.has_unresolved_row(value) || !value.scoped.is_empty() || !value.callables.is_empty()
        {
            return None;
        }
        let ty = self.collection_type(value);
        match ty {
            Ty::Result(..) => {
                value.result_tag?;
                if value.outer_results.is_empty() || value.outer_results != value.must_outer_results
                {
                    return None;
                }
                let mut result = value.outer_results.clone();
                result.extend(self.complete_result_value(value.result_payload.as_deref()?, seen)?);
                (result == value.results).then_some(result)
            }
            Ty::Optional(..) => match value.option_tag? {
                true => self.complete_result_value(value.option_payload.as_deref()?, seen),
                false => value.results.is_empty().then(BTreeSet::new),
            },
            _ if ty.scalar() => value.results.is_empty().then(BTreeSet::new),
            _ => {
                if value.origins.nodes.is_empty() {
                    return None;
                }
                let mut results = BTreeSet::new();
                for node in &value.origins.nodes {
                    results.extend(self.complete_constructed_results(*node, &ty, seen)?);
                }
                Some(results)
            }
        }
    }

    fn complete_constructed_results(
        &self,
        node: NodeId,
        ty: &Ty,
        seen: &mut BTreeSet<NodeId>,
    ) -> Option<BTreeSet<u32>> {
        let origin = &self.heap.nodes[node.0 as usize];
        if !matches!(origin.kind, OriginKind::Fresh(_))
            || origin.multiplicity != super::super::super::facts::Multiplicity::One
            || self
                .uncertain_slots
                .iter()
                .any(|(parent, _)| *parent == node)
            || !seen.insert(node)
        {
            return None;
        }
        let fields: BTreeMap<_, _> = self
            .fields
            .iter()
            .filter_map(|((parent, slot), value)| {
                (*parent == node).then_some((slot.clone(), value))
            })
            .collect();
        let complete=match ty {
            Ty::Record(types)=>fields.len()==types.len()&&types.keys().all(|name|fields.contains_key(&Slot::Field(name.clone()))),
            Ty::Tuple(types)=>fields.len()==types.len()&&(0..types.len()).all(|index|fields.contains_key(&Slot::Tuple(index as u32))),
            Ty::Array(_)=>self.array_lengths.get(&node).copied().flatten().is_some_and(|length|fields.len() as u64==length&&fields.keys().all(|slot|matches!(slot,Slot::Index(index)if *index>=0&&(*index as u64)<length))),
            _=>false,
        };
        if !complete {
            return None;
        }
        let mut results = BTreeSet::new();
        for value in fields.values() {
            results.extend(self.complete_result_value(value, seen)?);
        }
        seen.remove(&node);
        Some(results)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_missing_observation_is_never_a_complete_absence_certificate() {
        let source = "fn example(){let record:{first:Result<int,str>,second:Result<int,str>}=.{first:Ok(1),second:Err(\"other\")};assert(record.first is Ok(_));assert(record.second is Err(_))}";
        let syntax = ril_syntax::parse(source);
        assert!(syntax.is_ok());
        let mut checker = Checker::new(FileId(0));
        checker.run(&syntax.program);
        assert!(checker.diagnostics.is_empty(), "{:?}", checker.diagnostics);
        let value = checker
            .bindings
            .iter()
            .find(|binding| binding.name == "record")
            .unwrap()
            .value
            .clone();
        let node = *value.origins.nodes.first().unwrap();
        let ty = checker.collection_type(&value);
        let complete = checker
            .complete_constructed_results(node, &ty, &mut BTreeSet::new())
            .unwrap();
        assert_eq!(complete.len(), 2);
        let key = (node, Slot::Field("second".into()));
        let missing = checker.fields.remove(&key).unwrap();
        assert!(
            checker
                .complete_constructed_results(node, &ty, &mut BTreeSet::new())
                .is_none()
        );
        checker.fields.insert(key.clone(), missing);
        checker.uncertain_slots.insert(key);
        assert!(
            checker
                .complete_constructed_results(node, &ty, &mut BTreeSet::new())
                .is_none()
        );
    }
}
