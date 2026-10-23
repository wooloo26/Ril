//! Keep shared allocation history and typed sites across the Core boundary.
use super::*;

pub(super) fn lower(
    facts: &SemanticFacts,
    graph: &mut p::Graph,
    contracts: &mut ReturnContracts,
) -> Result<(), NotImplemented> {
    contracts.source_query(|_, work| {
        work.charge(1)?;
        work.charge(facts.allocation_events.len().saturating_mul(10))?;
        work.charge(facts.pattern_window_sites.len().saturating_mul(3))
    })?;
    graph.allocation_poisoned = facts.allocation_poisoned;
    graph.allocation_events = facts
        .allocation_events
        .iter()
        .map(|event| p::AllocationEvent {
            id: p::AllocationEventId(event.id.0),
            site: event.site.0,
            recent: origin(event.recent),
            remap: event
                .remap
                .map(|(recent, older)| (origin(recent), origin(older))),
            epoch_before: event.epoch_before as u64,
            cause: event.cause,
            owner: event.owner.0,
            anchor: event.anchor,
            position: event.position as u64,
        })
        .collect();
    graph.pattern_window_sites = facts
        .pattern_window_sites
        .iter()
        .map(|site| p::PatternWindowSite {
            rest: site.rest,
            loop_owner: site.loop_owner.0,
            site: site.site.0,
        })
        .collect();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn core_retains_actual_allocation_ordinals_and_typed_pattern_roles() {
        let facts = SemanticFacts {
            allocation_events: vec![crate::sema::allocation::AllocationEvent {
                id: crate::sema::allocation::AllocationEventId(7),
                site: f::SiteId(3),
                recent: f::NodeId(5),
                remap: Some((f::NodeId(5), f::NodeId(8))),
                epoch_before: 11,
                cause: ril_compiler_core::diagnostic::CauseId(13),
                owner: f::ScopeId(17),
                anchor: Some(ril_compiler_core::ids::ActivationEpochId(19)),
                position: 23,
            }],
            pattern_window_sites: vec![crate::sema::allocation::PatternWindowSite {
                rest: ril_compiler_core::ids::PatternId(29),
                loop_owner: f::ScopeId(31),
                site: f::SiteId(3),
            }],
            allocation_poisoned: true,
            ..Default::default()
        };
        let mut graph = p::Graph::default();
        let mut contracts = ReturnContracts {
            packet_sources: Some(evaluated::PacketSources::new(&facts)),
            ..Default::default()
        };
        lower(&facts, &mut graph, &mut contracts).unwrap();
        let event = &graph.allocation_events[0];
        assert_eq!(event.id, p::AllocationEventId(7));
        assert_eq!(
            (event.site, event.recent, event.remap),
            (3, OriginId(5), Some((OriginId(5), OriginId(8))))
        );
        assert_eq!(
            (
                event.epoch_before,
                event.cause.0,
                event.owner,
                event.position
            ),
            (11, 13, 17, 23)
        );
        assert_eq!(
            event.anchor,
            Some(ril_compiler_core::ids::ActivationEpochId(19))
        );
        assert_eq!(
            graph.pattern_window_sites[0],
            p::PatternWindowSite {
                rest: ril_compiler_core::ids::PatternId(29),
                loop_owner: 31,
                site: 3,
            }
        );
        assert!(graph.allocation_poisoned);
    }
}
