//! A fallback is selected by completed application records, never its span.
use super::*;
use crate::sema::default_uses::{ArgumentSource, DefaultOrigin, DefaultUseId};

pub(super) struct DefaultPlan {
    pub uses: BTreeSet<DefaultUseId>,
    pub operations: BTreeMap<Site, u64>,
}

pub(super) fn prepare(plan: &mut Plan, facts: &SemanticFacts) -> Result<(), NotImplemented> {
    for instance in &mut plan.instances {
        let syntax = &facts
            .functions
            .iter()
            .find(|info| info.definition == instance.record.template)
            .ok_or_else(|| unsupported("default instance has no declaration"))?
            .syntax;
        for (parameter, syntax) in syntax.parameters.iter().enumerate() {
            if syntax.default.is_none() {
                continue;
            }
            let parameter = parameter as u32;
            let mut uses = BTreeSet::new();
            let mut applications = BTreeSet::new();
            for call in &instance.record.invocations {
                let call = &facts.copy_invocations[call.0 as usize];
                let event = call.source_event.ok_or_else(|| {
                    unsupported("specialized defaults require an explicit application event")
                })?;
                let records: Vec<_> = facts
                    .call_arguments
                    .iter()
                    .filter(|record| record.source_event == event)
                    .collect();
                let [record] = records.as_slice() else {
                    return Err(unsupported(
                        "specialized defaults require unique argument-slot evidence",
                    ));
                };
                if !record.evaluation_complete
                    || record.target != Some(instance.record.template)
                    || record.slots.len()
                        != facts
                            .functions
                            .iter()
                            .find(|info| info.definition == instance.record.template)
                            .unwrap()
                            .syntax
                            .parameters
                            .len()
                {
                    return Err(unsupported(
                        "specialized default application did not complete its parameter slots",
                    ));
                }
                applications.insert(event);
                match record.slots[parameter as usize] {
                    ArgumentSource::Supplied => {}
                    ArgumentSource::Missing => {
                        return Err(unsupported(
                            "specialized default application has an unproved missing argument",
                        ));
                    }
                    ArgumentSource::Default(id) => {
                        let usage = facts
                            .default_uses
                            .get(id.0 as usize)
                            .filter(|usage| usage.id == id)
                            .ok_or_else(|| {
                                unsupported("specialized default evaluation is missing")
                            })?;
                        if usage.origin != DefaultOrigin::Call(event)
                            || usage.target != Some(instance.record.template)
                            || usage.parameter != parameter
                            || usage.owner
                                != Some(CallableOwner::Function(instance.record.template))
                            || !usage.evaluation_complete
                            || usage.status != CopyInvocationStatus::Completed
                            || !usage.entered.contains(&call.id)
                            || !usage.unresolved_captured_binders.is_empty()
                            || usage
                                .arguments
                                .iter()
                                .map(argument)
                                .collect::<Result<Vec<_>, _>>()?
                                != instance.record.arguments
                            || usage
                                .captured_arguments
                                .iter()
                                .map(argument)
                                .collect::<Result<Vec<_>, _>>()?
                                != instance.record.captured_arguments
                        {
                            return Err(unsupported(
                                "specialized default lacks its completed owner and static-argument certificate",
                            ));
                        }
                        uses.insert(id);
                    }
                }
            }
            let mut operations = None;
            for &id in &uses {
                let current = operation_map(
                    facts,
                    Selection::Default(id, CallableOwner::Function(instance.record.template)),
                )?;
                if operations
                    .as_ref()
                    .is_some_and(|previous| previous != &current)
                {
                    return Err(unsupported(
                        "equal static instances have conflicting default operation selections",
                    ));
                }
                operations = Some(current);
            }
            instance.record.defaults.push(irs::DefaultSlot {
                parameter,
                applications: applications
                    .into_iter()
                    .map(|id| ril_ir::specialization::ApplicationId(id.0))
                    .collect(),
                evaluations: uses.iter().map(|id| irs::DefaultUseId(id.0)).collect(),
            });
            instance.defaults.insert(
                parameter,
                DefaultPlan {
                    uses,
                    operations: operations.unwrap_or_default(),
                },
            );
        }
    }
    Ok(())
}

impl Instance {
    pub(super) fn default_contains(&self, id: DefaultUseId) -> bool {
        self.defaults.values().any(|slot| slot.uses.contains(&id))
    }

    pub(super) fn pruned_default_site(
        &self,
        facts: &SemanticFacts,
        site: ril_compiler_core::ids::ClosureSiteId,
    ) -> bool {
        let objects: Vec<_> = facts
            .closures
            .iter()
            .filter(|closure| closure.site == Some(site))
            .collect();
        !objects.is_empty()
            && objects.iter().all(|closure| {
                closure
                    .creation_default
                    .and_then(|id| facts.default_uses.get(id.0 as usize))
                    .is_some_and(|usage| {
                        usage.target == Some(self.record.template)
                            && self
                                .defaults
                                .get(&usage.parameter)
                                .is_some_and(|slot| slot.uses.is_empty())
                    })
            })
    }
}

impl Plan {
    /// Calls that stop while evaluating arguments have no named invocation. A
    /// successful sibling observation at the same source site cannot cover it.
    pub(super) fn validate_default_applications(
        &self,
        facts: &SemanticFacts,
        owner: Option<CallableOwner>,
        index: Option<usize>,
        default: Option<u32>,
        span: Span,
    ) -> Result<(), NotImplemented> {
        for event in &facts.copy_call_events {
            let Some(target) = event.target else {
                continue;
            };
            if event.owner != owner || event.span != span || !self.templates.contains(&target) {
                continue;
            }
            if !facts.functions.iter().any(|info| {
                info.definition == target
                    && info
                        .syntax
                        .parameters
                        .iter()
                        .any(|parameter| parameter.default.is_some())
            }) {
                continue;
            }
            let expression = event.callee_expression.ok_or_else(|| {
                unsupported("specialized default application has no evaluated callee identity")
            })?;
            let contexts: Vec<_> = facts
                .invocation_expressions
                .iter()
                .filter(|observed| observed.expression == expression)
                .map(|observed| observed.context)
                .collect();
            if contexts.is_empty() {
                return Err(unsupported(
                    "specialized default application lacks its evaluation context",
                ));
            }
            let relevant = index.is_none_or(|index| {
                let instance = &self.instances[index];
                contexts.iter().any(|&context| {
                    if let Some(parameter) = default {
                        instance.defaults[&parameter].uses.iter().any(|&id| {
                            Selection::Default(id, owner.unwrap()).matches(context, facts)
                        })
                    } else if let Some(CallableOwner::Lambda(site)) = owner {
                        instance.closures.get(&site).is_some_and(|closure| {
                            closure.calls.iter().any(|&id| {
                                Selection::Closure(id, CallableOwner::Lambda(site))
                                    .matches(context, facts)
                            })
                        })
                    } else {
                        instance.record.invocations.iter().any(|id| {
                            Selection::Named(
                                InstanceId(id.0),
                                CallableOwner::Function(instance.record.template),
                            )
                            .matches(context, facts)
                        })
                    }
                })
            });
            if relevant
                && !facts.copy_invocations.iter().any(|call| {
                    call.source_event == Some(event.id)
                        && call.target == target
                        && call.status == CopyInvocationStatus::Completed
                        && self.calls.contains_key(&call.id)
                })
            {
                return Err(unsupported(
                    "specialized default application has no completed body-entry certificate",
                ));
            }
        }
        Ok(())
    }

    pub fn default_facts(
        &self,
        facts: &SemanticFacts,
        index: usize,
        parameter: u32,
    ) -> Result<Option<SemanticFacts>, NotImplemented> {
        let instance = &self.instances[index];
        let slot = instance
            .defaults
            .get(&parameter)
            .ok_or_else(|| unsupported("specialized default slot has no certificate"))?;
        let Some(&first) = slot.uses.first() else {
            return Ok(None);
        };
        let selection =
            |id| Selection::Default(id, CallableOwner::Function(instance.record.template));
        let selected = self.project(facts, index, selection(first))?;
        let expected = shape(&selected, facts)?;
        for &id in &slot.uses {
            if shape(&self.project(facts, index, selection(id))?, facts)? != expected {
                return Err(unsupported(
                    "equal static instances have conflicting default lowering witnesses",
                ));
            }
        }
        let present: BTreeSet<_> = selected
            .expressions
            .iter()
            .map(|fact| site(fact.span))
            .collect();
        for observation in &facts.invocation_expressions {
            let Some(id) = observation.context.default_use else {
                continue;
            };
            let usage = &facts.default_uses[id.0 as usize];
            if usage.target == Some(instance.record.template)
                && usage.parameter == parameter
                && observation.context.owner
                    == Some(CallableOwner::Function(instance.record.template))
                && !present.contains(&site(facts.expressions[observation.expression].span))
            {
                return Err(unsupported(
                    "specialized default lacks complete emitted-expression coverage",
                ));
            }
        }
        Ok(Some(selected))
    }

    pub fn default_operations(&self, index: usize, parameter: u32) -> BTreeMap<Site, u64> {
        self.instances[index].defaults[&parameter]
            .operations
            .clone()
    }
}
