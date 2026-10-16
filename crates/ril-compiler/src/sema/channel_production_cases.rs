//! Conditional existence of physical Result producers in a complete carrier.
//! This enumerates possible contents. A constructor choice pays no inspection.
use super::*;
use crate::sema::channel_messages::{ChannelGuard, GuardLiteral};

#[derive(Clone)]
pub(in crate::sema) struct ProductionCase {
    pub guard: ChannelGuard,
    pub producers: BTreeSet<u32>,
}

/// The caller must first establish `complete` for this exact snapshot. Cases
/// preserve producer identities and versions; branch-exclusive children are
/// never promoted into unconditional must duties.
pub(in crate::sema) fn cases(
    snapshot: &CopyValueSnapshot,
    versions: &BTreeMap<u32, u32>,
) -> Option<Vec<ProductionCase>> {
    fn combine(
        left: Vec<ProductionCase>,
        right: Vec<ProductionCase>,
        work: &mut usize,
    ) -> Option<Vec<ProductionCase>> {
        let mut result = Vec::new();
        for a in &left {
            for b in &right {
                *work = work.checked_sub(1)?;
                let guard = a.guard.and(&b.guard)?;
                if guard.is_never() {
                    continue;
                }
                result.push(ProductionCase {
                    guard,
                    producers: a.producers.union(&b.producers).copied().collect(),
                });
                if result.len() > 256 {
                    return None;
                }
            }
        }
        Some(result)
    }
    fn empty() -> Vec<ProductionCase> {
        vec![ProductionCase {
            guard: ChannelGuard::always(),
            producers: BTreeSet::new(),
        }]
    }
    fn coalesce(cases: Vec<ProductionCase>) -> Option<Vec<ProductionCase>> {
        let mut result = BTreeMap::<BTreeSet<u32>, ChannelGuard>::new();
        for case in cases {
            if let Some(guard) = result.get_mut(&case.producers) {
                *guard = guard.or(&case.guard)?;
            } else {
                result.insert(case.producers, case.guard);
            }
        }
        Some(
            result
                .into_iter()
                .map(|(producers, guard)| ProductionCase { guard, producers })
                .collect(),
        )
    }
    fn visit(
        value: &Value,
        snapshot: &CopyValueSnapshot,
        versions: &BTreeMap<u32, u32>,
        active: &mut BTreeSet<NodeId>,
        work: &mut usize,
        depth: usize,
    ) -> Option<Vec<ProductionCase>> {
        *work = work.checked_sub(1)?;
        if depth > 128 {
            return None;
        }
        // `complete` has already proved that this exact constituent has no
        // hidden Result producer. Its runtime shape need not be enumerated.
        if value.results.is_empty() {
            return Some(empty());
        }
        if !value.outer_results.is_empty() {
            let mut result = Vec::new();
            for success in [false, true] {
                if value.result_tag.is_some_and(|known| known != success) {
                    continue;
                }
                let choice = if value.result_tag.is_none() {
                    if value.outer_results.len() != 1
                        || value.outer_results != value.must_outer_results
                    {
                        return None;
                    }
                    let producer = *value.outer_results.first()?;
                    ChannelGuard::literal(GuardLiteral::Result {
                        producer,
                        version: versions.get(&producer).copied().unwrap_or(0),
                        success,
                    })
                } else {
                    ChannelGuard::always()
                };
                let payload = (if success {
                    value.result_success.as_deref()
                } else {
                    value.result_error.as_deref()
                })
                .or_else(|| {
                    (value.result_tag == Some(success))
                        .then_some(value.result_payload.as_deref())
                        .flatten()
                });
                let branches = match payload {
                    Some(payload) => visit(payload, snapshot, versions, active, work, depth + 1)?,
                    None => empty(), // completeness separately proves type absence
                };
                for mut branch in branches {
                    branch.guard = branch.guard.and(&choice)?;
                    if branch.guard.is_never() {
                        continue;
                    }
                    branch.producers.extend(&value.outer_results);
                    result.push(branch);
                    if result.len() > 256 {
                        return None;
                    }
                }
            }
            return coalesce(result);
        }
        if value.option_tag.is_some() || value.option_payload.is_some() {
            return match value.option_tag {
                Some(false) => Some(empty()),
                Some(true) => visit(
                    value.option_payload.as_deref()?,
                    snapshot,
                    versions,
                    active,
                    work,
                    depth + 1,
                ),
                None => {
                    let identity = value.option_identity?;
                    let mut present = visit(
                        value.option_payload.as_deref()?,
                        snapshot,
                        versions,
                        active,
                        work,
                        depth + 1,
                    )?;
                    for case in &mut present {
                        case.guard =
                            case.guard
                                .and(&ChannelGuard::literal(GuardLiteral::Optional {
                                    identity,
                                    present: true,
                                }))?;
                    }
                    present.push(ProductionCase {
                        guard: ChannelGuard::literal(GuardLiteral::Optional {
                            identity,
                            present: false,
                        }),
                        producers: BTreeSet::new(),
                    });
                    coalesce(present)
                }
            };
        }
        if let Some(payload) = &value.variant_payload {
            return visit(payload, snapshot, versions, active, work, depth + 1);
        }
        let mut result = empty();
        for origin in &value.origins.nodes {
            if !active.insert(*origin) {
                return None;
            }
            let node = snapshot.nodes.iter().find(|node| node.origin == *origin)?;
            for (_, child) in &node.fields {
                let child = visit(child, snapshot, versions, active, work, depth + 1)?;
                result = combine(result, child, work)?;
            }
            active.remove(origin);
        }
        Some(result)
    }
    let result = visit(
        &snapshot.value,
        snapshot,
        versions,
        &mut BTreeSet::new(),
        &mut 4096,
        0,
    )?;
    let represented = result
        .iter()
        .flat_map(|case| &case.producers)
        .copied()
        .collect::<BTreeSet<_>>();
    (represented == snapshot.value.results).then_some(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ril_compiler_core::diagnostic::CauseId;
    fn scalar() -> Value {
        Value::scalar(Ty::Int("int".into()), None, CauseId(0))
    }
    fn result(id: u32, success: Value, error: Value) -> Value {
        let mut value = Value::scalar(
            Ty::Result(Box::new(success.ty.clone()), Box::new(error.ty.clone())),
            None,
            CauseId(id),
        );
        value.outer_results = [id].into();
        value.must_outer_results = [id].into();
        value.must_results = [id].into();
        value.results = [id].into();
        value.results.extend(&success.results);
        value.results.extend(&error.results);
        value.result_success = Some(Box::new(success));
        value.result_error = Some(Box::new(error));
        value
    }
    fn frozen(value: Value) -> CopyValueSnapshot {
        CopyValueSnapshot {
            value,
            nodes: Vec::new(),
            relations: Vec::new(),
        }
    }
    #[test]
    fn conditional_children_exist_only_under_their_actual_parent_constructor() {
        let value = frozen(result(0, result(1, scalar(), scalar()), scalar()));
        let cases = cases(&value, &[(0, 7), (1, 9)].into()).unwrap();
        assert_eq!(cases.len(), 2);
        for case in cases {
            let has_child = case.producers.contains(&1);
            assert_eq!(case.producers.len(), if has_child { 2 } else { 1 });
            let parent = ChannelGuard::literal(GuardLiteral::Result {
                producer: 0,
                version: 7,
                success: has_child,
            });
            assert!(case.guard.and(&parent.not().unwrap()).unwrap().is_never());
            assert!(case.guard.terms.iter().flatten().all(|literal| {
                !matches!(literal, GuardLiteral::Result { producer: 1, version, .. } if *version != 9)
            }));
        }
    }
    #[test]
    fn both_conditional_branches_retain_their_distinct_physical_children() {
        let value = frozen(result(
            0,
            result(1, scalar(), scalar()),
            result(2, scalar(), scalar()),
        ));
        let cases = cases(&value, &BTreeMap::new()).unwrap();
        assert_eq!(cases.len(), 2);
        assert!(cases.iter().all(|case| case.producers.len() == 2));
        assert!(
            cases
                .iter()
                .all(|case| { case.producers.contains(&1) != case.producers.contains(&2) })
        );
        let covered = cases
            .iter()
            .try_fold(ChannelGuard::never(), |guard, case| guard.or(&case.guard));
        assert_eq!(covered, Some(ChannelGuard::always()));
    }
    #[test]
    fn missing_conditional_witnesses_do_not_become_production_coverage() {
        let mut value = frozen(result(0, result(1, scalar(), scalar()), scalar()));
        value.value.result_success = None;
        assert!(cases(&value, &BTreeMap::new()).is_none());
        assert!(!complete(&value, &BTreeMap::new(), &BTreeMap::new()));
    }
}
