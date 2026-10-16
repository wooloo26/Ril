//! Guaranteed producer presence in one guarded message world.
//! This reader does not inspect a tag, discard debt or modify a Value.
use super::{
    messages::{Flow, World},
    *,
};
use crate::sema::channel_messages::GuardLiteral;

pub(super) fn present(
    value: &Value,
    world: &World,
    flow: &Flow,
    fields: &BTreeMap<(NodeId, Slot), Value>,
) -> Option<BTreeSet<u32>> {
    fn visit(
        value: &Value,
        world: &World,
        flow: &Flow,
        fields: &BTreeMap<(NodeId, Slot), Value>,
        active: &mut BTreeSet<NodeId>,
        budget: &mut usize,
    ) -> Option<BTreeSet<u32>> {
        *budget = budget.checked_sub(1)?;
        if !value.outer_results.is_empty() {
            let mut result = value.must_outer_results.clone();
            let events: BTreeSet<_> = value
                .outer_results
                .iter()
                .filter_map(|producer| flow.aliases.get(producer))
                .flatten()
                .filter(|event| world.executed.contains(event))
                .copied()
                .collect();
            let family = (value.outer_results.len() == 1)
                .then(|| {
                    flow.result_outcomes
                        .get(value.outer_results.first().unwrap())
                })
                .flatten();
            let physical = (events.is_empty()
                && value.result_tag.is_none()
                && value.outer_results.len() == 1)
                .then(|| {
                    let producer = *value.outer_results.first().unwrap();
                    [false, true].map(|success| {
                        crate::sema::channel_messages::ChannelGuard::literal(GuardLiteral::Result {
                            producer,
                            version: flow.generations.get(&producer).copied().unwrap_or(0),
                            success,
                        })
                    })
                });
            let family = family.or(physical.as_ref());
            let selected = if let Some(outcomes) = family {
                let mut selected = None;
                for success in [false, true] {
                    let missing = world.guard.and(&outcomes[usize::from(success)].not()?)?;
                    if missing.is_never() {
                        selected = Some(success);
                    }
                }
                selected
            } else if events.len() == 1 {
                let event = *events.first()?;
                [false, true].into_iter().find(|success| world.guard.terms.iter().all(|term| {
                    term.iter().any(|literal| matches!(literal, GuardLiteral::Transport { event: actual, success: actual_success, .. } if *actual == event && actual_success == success))
                }))
            } else if events.is_empty() {
                value.result_tag
            } else {
                None
            };
            if let Some(success) = selected {
                let payload = if success {
                    value.result_success.as_deref()
                } else {
                    value.result_error.as_deref()
                }
                .or_else(|| {
                    (value.result_tag == Some(success))
                        .then_some(value.result_payload.as_deref())
                        .flatten()
                });
                if let Some(payload) = payload {
                    result.extend(visit(payload, world, flow, fields, active, budget)?);
                }
            } else if let (Some(success), Some(error)) =
                (&value.result_success, &value.result_error)
            {
                let success = visit(success, world, flow, fields, active, budget)?;
                let error = visit(error, world, flow, fields, active, budget)?;
                result.extend(success.intersection(&error).copied());
            }
            return Some(result);
        }
        if value.option_tag.is_some() || value.option_payload.is_some() {
            let selected = value.option_tag.or_else(|| {
                let identity = value.option_identity?;
                let present =
                    crate::sema::channel_messages::ChannelGuard::literal(GuardLiteral::Optional {
                        identity,
                        present: true,
                    });
                world
                    .guard
                    .and(&present.not()?)
                    .filter(|missing| missing.is_never())
                    .map(|_| true)
            });
            return match selected {
                Some(true) => visit(
                    value.option_payload.as_deref()?,
                    world,
                    flow,
                    fields,
                    active,
                    budget,
                ),
                _ => Some(BTreeSet::new()),
            };
        }
        if let Some(payload) = &value.variant_payload {
            return visit(payload, world, flow, fields, active, budget);
        }
        let mut result: Option<BTreeSet<u32>> = None;
        for origin in &value.origins.nodes {
            if !active.insert(*origin) {
                continue;
            }
            let mut from_origin = BTreeSet::new();
            for ((node, _), child) in fields {
                if node == origin {
                    from_origin.extend(visit(child, world, flow, fields, active, budget)?);
                }
            }
            active.remove(origin);
            result = Some(match result {
                None => from_origin,
                Some(previous) => previous.intersection(&from_origin).copied().collect(),
            });
        }
        let mut result = result.unwrap_or_default();
        result.retain(|producer| value.must_results.contains(producer));
        Some(result)
    }
    visit(value, world, flow, fields, &mut BTreeSet::new(), &mut 4096)
}
