//! Dynamic closure objects select one specialized lexical site, including after
//! their creator's activation has ended. Source spans never identify an object.
use super::*;
use crate::sema::effect_identity::ClosureInvocationId;
use ril_compiler_core::ids::ClosureSiteId;

pub(super) struct ClosurePlan {
    pub target: ClosureSiteId,
    pub objects: BTreeSet<usize>,
    pub calls: BTreeSet<ClosureInvocationId>,
    pub operations: BTreeMap<Site, u64>,
}

pub(super) fn prepare(plan: &mut Plan, facts: &SemanticFacts) -> Result<(), NotImplemented> {
    let mut next = facts
        .closure_sites
        .iter()
        .map(|site| site.id.0)
        .max()
        .map_or(Some(0), |id| id.checked_add(1))
        .ok_or_else(|| unsupported("specialized closure identity exhausted"))?;
    for instance in &mut plan.instances {
        loop {
            let selected: Vec<_> = facts
                .closure_sites
                .iter()
                .filter(|site| {
                    instance
                        .record
                        .owners
                        .iter()
                        .any(|mapping| mapping.source == site.owner)
                        && !instance.closures.contains_key(&site.id)
                        && !instance.pruned_default_site(facts, site.id)
                })
                .cloned()
                .collect();
            if selected.is_empty() {
                break;
            }
            for site in selected {
                let target = ClosureSiteId(next);
                next = next
                    .checked_add(1)
                    .ok_or_else(|| unsupported("specialized closure identity exhausted"))?;
                instance.record.owners.push(irs::OwnerMap {
                    source: CallableOwner::Lambda(site.id),
                    target: CallableOwner::Lambda(target),
                });
                instance.closures.insert(
                    site.id,
                    ClosurePlan {
                        target,
                        objects: BTreeSet::new(),
                        calls: BTreeSet::new(),
                        operations: BTreeMap::new(),
                    },
                );
            }
        }
        loop {
            let mut added = false;
            for (id, closure) in facts.closures.iter().enumerate() {
                let Some(site) = closure.site else {
                    continue;
                };
                if !instance.closures.contains_key(&site) {
                    continue;
                }
                let lexical = facts
                    .closure_sites
                    .iter()
                    .find(|item| item.id == site)
                    .ok_or_else(|| unsupported("closure creation has no lexical site"))?;
                let selected = match lexical.owner {
                    CallableOwner::Function(owner) if owner == instance.record.template => {
                        if let Some(id) = closure.creation_default {
                            instance.default_contains(id)
                        } else {
                            closure.creation_invocation.is_some_and(|id| {
                                instance
                                    .record
                                    .invocations
                                    .iter()
                                    .any(|call| call.0 == id.0)
                            })
                        }
                    }
                    CallableOwner::Lambda(parent) => closure
                        .creation_closure
                        .and_then(|id| facts.closure_invocations.get(id.0 as usize))
                        .is_some_and(|call| {
                            instance
                                .closures
                                .get(&parent)
                                .is_some_and(|plan| plan.objects.contains(&call.closure))
                        }),
                    _ => false,
                };
                if selected {
                    added |= instance.closures.get_mut(&site).unwrap().objects.insert(id);
                }
            }
            if !added {
                break;
            }
        }
        for (&site, closure) in &mut instance.closures {
            if closure.objects.is_empty() {
                return Err(unsupported(
                    "specialized closure site has no covered creation object",
                ));
            }
            for call in &facts.closure_invocations {
                if !closure.objects.contains(&call.closure) {
                    continue;
                }
                if call.status != CopyInvocationStatus::Completed {
                    return Err(unsupported(
                        "specialized closure has an incomplete invocation",
                    ));
                }
                closure.calls.insert(call.id);
            }
            let first = *closure.calls.first().ok_or_else(|| {
                unsupported("specialized closure has no complete latent or actual invocation")
            })?;
            closure.operations = operation_map(
                facts,
                Selection::Closure(first, CallableOwner::Lambda(site)),
            )?;
            for &call in &closure.calls {
                if operation_map(facts, Selection::Closure(call, CallableOwner::Lambda(site)))?
                    != closure.operations
                {
                    return Err(unsupported(
                        "specialized closure invocations select conflicting effect operations",
                    ));
                }
            }
        }
    }
    Ok(())
}

impl Plan {
    pub fn closure_facts(
        &self,
        facts: &SemanticFacts,
        index: usize,
        site_id: ClosureSiteId,
    ) -> Result<SemanticFacts, NotImplemented> {
        let closure = self.instances[index]
            .closures
            .get(&site_id)
            .ok_or_else(|| {
                unsupported("specialized closure has no creation/invocation certificate")
            })?;
        let first = *closure
            .calls
            .iter()
            .find(|call|!facts.closure_invocations[call.0 as usize].budget_validation)
            .ok_or_else(|| unsupported("specialized closure has no checked creation or ordinary invocation outside zero-budget validation"))?;
        let selected = self.project(
            facts,
            index,
            Selection::Closure(first, CallableOwner::Lambda(site_id)),
        )?;
        let expected = shape(&selected, facts)?;
        for &call in &closure.calls {
            let actual = self.project(
                facts,
                index,
                Selection::Closure(call, CallableOwner::Lambda(site_id)),
            )?;
            let actual = shape(&actual, facts)?;
            // A known nonpositive budget checks the action but never enters it.
            // That explicit frontend mode can omit selection of a retained arm;
            // it is not an empty recipe for any ordinary call. Keep comparing
            // the complete emitted code shape and publish only the independently
            // checked creation/ordinary recipe selected above.
            let mut required = expected.clone();
            if facts.closure_invocations[call.0 as usize].budget_validation
                && actual.recipes.is_empty()
            {
                required.recipes.clear();
            }
            if actual != required {
                return Err(unsupported(
                    "specialized closure invocations have conflicting lowering witnesses",
                ));
            }
        }
        let observed: BTreeSet<_> = selected
            .expressions
            .iter()
            .map(|fact| site(fact.span))
            .collect();
        for expression in &facts.invocation_expressions {
            if expression.context.owner == Some(CallableOwner::Lambda(site_id))
                && !observed.contains(&site(facts.expressions[expression.expression].span))
            {
                return Err(unsupported(
                    "specialized closure has incomplete emitted-expression coverage",
                ));
            }
        }
        Ok(selected)
    }

    pub fn closure_operations(
        &self,
        index: usize,
        site: ClosureSiteId,
    ) -> Result<BTreeMap<Site, u64>, NotImplemented> {
        self.instances[index]
            .closures
            .get(&site)
            .map(|closure| closure.operations.clone())
            .ok_or_else(|| unsupported("specialized closure operation map is missing"))
    }

    pub fn publish_closures(
        &self,
        facts: &SemanticFacts,
        graph: &mut ril_ir::metadata::ProgramMetadata,
    ) -> Result<(), NotImplemented> {
        for (index, instance) in self.instances.iter().enumerate() {
            for (&source, closure) in &instance.closures {
                let original = facts
                    .closure_sites
                    .iter()
                    .find(|site| site.id == source)
                    .ok_or_else(|| unsupported("specialized closure lexical site is missing"))?;
                let owner = instance
                    .record
                    .owners
                    .iter()
                    .find(|mapping| mapping.source == original.owner)
                    .ok_or_else(|| unsupported("specialized closure parent owner is missing"))?
                    .target;
                graph.closure_sites.push(ril_ir::metadata::ClosureSite {
                    id: closure.target,
                    owner,
                    source: original.source,
                    span: original.span,
                });
                let selected = self.closure_facts(facts, index, source)?;
                for proof in &selected.retained_handlers {
                    if !matches!(&proof.callable,Callable::Closure(id) if facts.closures[*id].site==Some(source))
                    {
                        return Err(unsupported(
                            "retained specialization proof belongs to a different closure owner",
                        ));
                    }
                    let definitions = proof
                        .handlers
                        .iter()
                        .map(|&id| {
                            let source = facts
                                .handlers
                                .get(id)
                                .and_then(|handler| handler.site)
                                .ok_or_else(|| {
                                    unsupported(
                                        "retained specialization handler has no lexical identity",
                                    )
                                })?;
                            Ok(instance
                                .record
                                .handlers
                                .iter()
                                .find(|mapping| mapping.source == source)
                                .map_or(source, |mapping| mapping.target))
                        })
                        .collect::<Result<Vec<_>, NotImplemented>>()?;
                    graph
                        .retained_handlers
                        .push(ril_ir::metadata::RetainedHandler {
                            callable: Some(CallableOwner::Lambda(closure.target)),
                            span: proof.span,
                            definitions: Some(definitions),
                        });
                }
            }
        }
        Ok(())
    }
}
