//! Structure sharing across imports from immutable arenas. Full source IDs,
//! including their arena, are the only keys; no type spelling or hash is used.
use super::*;
use std::collections::BTreeMap;

fn lookup_cost(length: usize) -> usize {
    length.checked_ilog2().unwrap_or(0) as usize + 1
}

impl SourceBuilder {
    pub(crate) fn import_frozen(
        &mut self,
        source: &SourceTypes,
        root: SourceTypeId,
        work: &mut WorkLimit,
    ) -> Result<SourceTypeId, SourceTypesError> {
        work.charge(1 + lookup_cost(self.imports.len()))?;
        source.get(root)?;
        if let Some(target) = self.imports.get(&root).copied() {
            self.get(target)?;
            return Ok(target);
        }
        let checkpoint = self.checkpoint();
        let result = self.import_uncopied(source, root, work);
        if result.is_err() {
            self.rollback(checkpoint);
        }
        result
    }

    fn import_uncopied(
        &mut self,
        source: &SourceTypes,
        root: SourceTypeId,
        work: &mut WorkLimit,
    ) -> Result<SourceTypeId, SourceTypesError> {
        work.charge(1)?;
        let mut pending = vec![root];
        let mut mapping = BTreeMap::new();
        let mut fresh = Vec::new();
        while let Some(id) = pending.pop() {
            work.charge(lookup_cost(mapping.len()))?;
            if mapping.contains_key(&id) {
                continue;
            }
            let node = source.get(id)?;
            work.charge(lookup_cost(self.imports.len()) + lookup_cost(mapping.len()))?;
            if let Some(target) = self.imports.get(&id).copied() {
                self.get(target)?;
                mapping.insert(id, target);
                continue;
            }
            node.charge(work)?;
            work.charge(1)?;
            let target = self.reserve(work)?;
            mapping.insert(id, target);
            fresh.push(id);
            pending.extend(node.children());
        }
        for id in &fresh {
            let node = source.get(*id)?;
            node.charge(work)?;
            work.charge(lookup_cost(mapping.len()) * (node.children().len() + 1))?;
            let copied = node.map_children(|child| {
                mapping
                    .get(&child)
                    .copied()
                    .ok_or(SourceTypesError::MissingNode)
            })?;
            self.define(mapping[id], copied, work)?;
        }
        for id in fresh {
            // Prepay removal too: failure must roll back the copy index along
            // with reservations without asking an exhausted caller for work.
            work.charge(2 * lookup_cost(self.imports.len()) + lookup_cost(mapping.len()) + 1)?;
            let target = *mapping.get(&id).ok_or(SourceTypesError::MissingNode)?;
            self.imports.insert(id, target);
            self.import_order.push(id);
        }
        work.charge(lookup_cost(mapping.len()))?;
        mapping
            .get(&root)
            .copied()
            .ok_or(SourceTypesError::MissingNode)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::source_types::SourceTypeQueries;

    fn recursive_graph() -> (SourceTypes, SourceTypeId, SourceTypeId) {
        let mut source = SourceBuilder::new().unwrap();
        let mut work = WorkLimit::new(4096);
        let root = source.reserve(&mut work).unwrap();
        let element = source
            .insert(SourceNode::Scalar(SourceScalar::I8), &mut work)
            .unwrap();
        let shared = source
            .insert(
                SourceNode::Alias {
                    declaration: "shared".into(),
                    target: element,
                },
                &mut work,
            )
            .unwrap();
        source
            .define(
                root,
                SourceNode::Tuple(vec![root, shared, shared]),
                &mut work,
            )
            .unwrap();
        (source.freeze(&mut work).unwrap(), root, element)
    }

    #[test]
    fn frozen_import_reuses_root_shared_children_and_recursive_edges() {
        let (source, root, element) = recursive_graph();
        let mut target = SourceBuilder::new().unwrap();
        let mut work = WorkLimit::new(4096);
        let scalar = target.import_frozen(&source, element, &mut work).unwrap();
        let copied = target.import_frozen(&source, root, &mut work).unwrap();
        let checkpoint = target.checkpoint();
        for _ in 0..256 {
            assert_eq!(
                target.import_frozen(&source, root, &mut WorkLimit::new(8)),
                Ok(copied)
            );
        }
        assert_eq!(target.checkpoint(), checkpoint);
        let graph = target.freeze(&mut work).unwrap();
        let SourceNode::Tuple(children) = graph.get(copied).unwrap() else {
            panic!()
        };
        assert_eq!(children[0], copied);
        assert_eq!(children[1], children[2]);
        assert!(
            matches!(graph.get(children[1]), Ok(SourceNode::Alias { target, .. }) if *target == scalar)
        );
        assert_eq!(graph.reachable([copied], &mut work).unwrap().len(), 3);
        assert_eq!(
            crate::sema::source_types::reception::equivalent(
                &source, root, &graph, copied, &mut work
            ),
            Ok(true)
        );
    }

    #[test]
    fn failed_frozen_import_restores_nodes_and_every_memo_entry() {
        let (source, root, element) = recursive_graph();
        let mut saw_late_failure = false;
        let mut saw_success = false;
        for units in 0..128 {
            let mut target = SourceBuilder::new().unwrap();
            let preserved = target
                .insert(
                    SourceNode::Scalar(SourceScalar::Bool),
                    &mut WorkLimit::new(128),
                )
                .unwrap();
            let shared = target
                .import_frozen(&source, element, &mut WorkLimit::new(128))
                .unwrap();
            let checkpoint = target.checkpoint();
            let result = target.import_frozen(&source, root, &mut WorkLimit::new(units));
            if result.is_ok() {
                saw_success = true;
                continue;
            }
            assert_eq!(result, Err(SourceTypesError::BudgetExceeded));
            assert_eq!(target.checkpoint(), checkpoint);
            assert_eq!(target.imports.len(), 1);
            assert_eq!(target.imports.get(&element), Some(&shared));
            assert_eq!(
                target.get(preserved),
                Ok(&SourceNode::Scalar(SourceScalar::Bool))
            );
            // A later copy may reuse rolled-back node ordinals but must never
            // observe an import entry pointing into those removed nodes.
            let copied = target
                .import_frozen(&source, root, &mut WorkLimit::new(4096))
                .unwrap();
            let SourceNode::Tuple(children) = target.get(copied).unwrap() else {
                panic!()
            };
            assert_eq!(children[0], copied);
            assert_eq!(children[1], children[2]);
            assert!(
                matches!(target.get(children[1]), Ok(SourceNode::Alias { target, .. }) if *target == shared)
            );
            saw_late_failure |= units > 32;
        }
        assert!(saw_late_failure && saw_success);
    }

    #[test]
    fn frozen_import_never_uses_another_arena_or_waives_work_on_a_hit() {
        let (first, root, _) = recursive_graph();
        let (other, other_root, _) = recursive_graph();
        let mut target = SourceBuilder::new().unwrap();
        let first_copy = target
            .import_frozen(&first, root, &mut WorkLimit::new(4096))
            .unwrap();
        let checkpoint = target.checkpoint();
        assert_eq!(
            target.import_frozen(&other, root, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::ForeignIdentity)
        );
        assert_eq!(
            target.import_frozen(&first, root, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        );
        assert_eq!(target.checkpoint(), checkpoint);
        let second_copy = target
            .import_frozen(&other, other_root, &mut WorkLimit::new(4096))
            .unwrap();
        assert_ne!(first_copy, second_copy);
    }
}
