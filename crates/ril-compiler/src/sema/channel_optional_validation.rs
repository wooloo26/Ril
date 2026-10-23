//! Fresh symbolic formal slots cannot share an immutable optional choice.
//! Actual call arguments may share a value; declaration input templates may not
//! assume that equality and discard independent concrete assignments.
use super::*;

pub(super) fn validate(facts: &SemanticFacts) -> Check {
    fn visit(
        value: &Value,
        snapshot: crate::sema::copy_contract::CopyValueView<'_>,
        path: &mut Vec<String>,
        output: &mut Vec<(ril_compiler_core::ids::OptionalTagId, Vec<String>)>,
        active: &mut BTreeSet<NodeId>,
        work: &mut usize,
    ) -> Check {
        *work = work
            .checked_sub(1)
            .ok_or("optional formal path reconstruction exceeds its bound")?;
        if path.len() > 128 {
            return Err("optional formal path depth exceeds its bound".into());
        }
        if let Some(identity) = value.option_identity {
            output.push((identity, path.clone()));
        }
        if let Some(payload) = &value.option_payload {
            path.push("optional-payload".into());
            visit(payload, snapshot, path, output, active, work)?;
            path.pop();
            return Ok(());
        }
        if !value.outer_results.is_empty() {
            for success in [false, true] {
                if value.result_tag.is_some_and(|known| known != success) {
                    continue;
                }
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
                if let Some(payload) = payload {
                    path.push(
                        if success {
                            "result-success"
                        } else {
                            "result-error"
                        }
                        .into(),
                    );
                    visit(payload, snapshot, path, output, active, work)?;
                    path.pop();
                }
            }
            return Ok(());
        }
        for origin in &value.origins.nodes {
            if !active.insert(*origin) {
                continue;
            }
            let node = snapshot
                .nodes
                .iter()
                .find(|node| node.origin == *origin)
                .ok_or("optional formal path lacks its frozen storage node")?;
            for (slot, child) in &node.fields {
                path.push(format!("storage:{}:{slot:?}", origin.0));
                visit(child, snapshot, path, output, active, work)?;
                path.pop();
            }
            active.remove(origin);
        }
        Ok(())
    }
    fn argument_tags(
        invocation: &crate::sema::copy_contract::CopyInvocation,
        work: &mut usize,
    ) -> Check<Vec<(usize, ril_compiler_core::ids::OptionalTagId, Vec<String>)>> {
        let mut arguments = Vec::new();
        for (index, argument) in invocation.entry.arguments.iter().enumerate() {
            let mut budget = crate::sema::source_types::WorkLimit::new(*work);
            let snapshot = argument.snapshot_view(&mut budget);
            *work = budget.remaining();
            let snapshot = snapshot.map_err(|error| error.to_string())?;
            if argument.packet.current_epoch() != invocation.entry.allocation_epoch {
                return Err("optional formal borrowed another entry heap epoch".into());
            }
            let mut tags = Vec::new();
            visit(
                snapshot.value,
                snapshot,
                &mut Vec::new(),
                &mut tags,
                &mut BTreeSet::new(),
                work,
            )?;
            arguments.extend(
                tags.into_iter()
                    .map(|(identity, path)| (index, identity, path)),
            );
        }
        Ok(arguments)
    }
    fn guard_tags(
        guard: &ChannelGuard,
        needed: &mut BTreeSet<ril_compiler_core::ids::OptionalTagId>,
        work: &mut usize,
    ) -> Check {
        for literal in guard.terms.iter().flatten() {
            *work = work
                .checked_sub(1)
                .ok_or("optional proof dependency reconstruction exceeds its bound")?;
            if let GuardLiteral::Optional { identity, .. } = literal {
                needed.insert(*identity);
            }
        }
        Ok(())
    }
    fn carrier_tags(
        snapshot: &CopyValueSnapshot,
        needed: &mut BTreeSet<ril_compiler_core::ids::OptionalTagId>,
        work: &mut usize,
    ) -> Check {
        if snapshot.value.results.is_empty() {
            return Ok(());
        }
        let mut tags = Vec::new();
        visit(
            &snapshot.value,
            snapshot.as_view(),
            &mut Vec::new(),
            &mut tags,
            &mut BTreeSet::new(),
            work,
        )?;
        needed.extend(tags.into_iter().map(|(identity, _)| identity));
        Ok(())
    }

    let mut seen = BTreeMap::new();
    let mut work = 65_536usize;
    // First discharge universal source-header duties, including a completely
    // deleted input table. Tag absence or unrelated proof work cannot skip it.
    for invocation in &facts.copy_invocations {
        let header = facts
            .functions
            .iter()
            .find(|function| function.definition == invocation.target)
            .ok_or("optional formal template lacks its actual function declaration")?;
        // A declaration entry is an observation of the real whole-function
        // source span, rather than a call occurrence in a caller's body. Its
        // independent input positions cannot be disabled by registry flags.
        if invocation.span != header.syntax.span {
            continue;
        }
        if invocation.entry.arguments.len() != header.syntax.parameters.len() {
            return Err(
                "optional formal template does not cover the actual parameter header".into(),
            );
        }
        for (index, identity, path) in argument_tags(invocation, &mut work)? {
            facts
                .optional_tags
                .get(identity.0 as usize)
                .filter(|tag| tag.id == identity)
                .ok_or("optional formal path names an unregistered tag")?;
            // The real declaration entry defines an independent symbolic
            // input position. Arena owner metadata cannot turn it into an
            // actual aliased argument and disable this reconstruction.
            let position = (invocation.id, index, path);
            if seen
                .insert(identity, position.clone())
                .is_some_and(|previous| previous != position)
            {
                return Err(
                    "independent symbolic formal parameter paths reuse one optional tag identity"
                        .into(),
                );
            }
        }
    }

    // Actual-call source reconstruction is required by tags used in a Result
    // proof, message presence, or an execution/exit guard of that proof. Plain
    // unrelated Option<int> computations do not owe channel source evidence.
    let mut regions = BTreeSet::new();
    let mut needed = BTreeSet::new();
    for event in &facts.channel_messages {
        let proof = match &event.action {
            ChannelAction::Send {
                payload, transport, ..
            }
            | ChannelAction::Receive {
                payload, transport, ..
            } => {
                carrier_tags(payload, &mut needed, &mut work)?;
                carrier_tags(transport, &mut needed, &mut work)?;
                true
            }
            ChannelAction::TagTest { subject, .. }
            | ChannelAction::ConditionEvaluated { subject, .. }
            | ChannelAction::Inspect { value: subject, .. } => {
                carrier_tags(subject, &mut needed, &mut work)?;
                !subject.value.results.is_empty()
            }
            ChannelAction::ResultTransfer {
                source, producers, ..
            } => {
                carrier_tags(source, &mut needed, &mut work)?;
                !producers.is_empty()
            }
            ChannelAction::ResultAliases { map } => !map.is_empty(),
            ChannelAction::Select { evaluation, .. } => facts
                .condition_evaluations
                .get(evaluation.0 as usize)
                .is_some_and(|evaluation| {
                    !evaluation.inspections.when_true.is_empty()
                        || !evaluation.inspections.when_false.is_empty()
                }),
            ChannelAction::TaskFork { .. } | ChannelAction::TaskJoin { .. } => false,
        };
        if proof {
            regions.insert(super::region(facts, event.context)?);
        }
    }
    for evaluation in &facts.condition_evaluations {
        if !evaluation.inspections.when_true.is_empty()
            || !evaluation.inspections.when_false.is_empty()
        {
            regions.insert(super::region(facts, evaluation.context)?);
            guard_tags(
                &evaluation.inspections.channel_when_true,
                &mut needed,
                &mut work,
            )?;
            guard_tags(
                &evaluation.inspections.channel_when_false,
                &mut needed,
                &mut work,
            )?;
        }
    }
    for exit in &facts.channel_exits {
        if !exit.returned.value.results.is_empty() {
            regions.insert(super::region(facts, exit.context)?);
            carrier_tags(&exit.returned, &mut needed, &mut work)?;
        }
    }
    for event in &facts.channel_messages {
        if regions.contains(&super::region(facts, event.context)?) {
            guard_tags(&event.guard, &mut needed, &mut work)?;
            if let ChannelAction::Receive { sources, .. } = &event.action {
                for source in sources {
                    guard_tags(&source.guard, &mut needed, &mut work)?;
                }
            }
        }
    }
    for exit in &facts.channel_exits {
        if regions.contains(&super::region(facts, exit.context)?) {
            guard_tags(&exit.guard, &mut needed, &mut work)?;
        }
    }
    let mut sources = super::repetition::Analysis::new(facts);
    for invocation in &facts.copy_invocations {
        let header = facts
            .functions
            .iter()
            .find(|function| function.definition == invocation.target)
            .ok_or("optional input call lacks its actual function declaration")?;
        if invocation.span != header.syntax.span
            && argument_tags(invocation, &mut work)?
                .iter()
                .any(|(_, identity, _)| needed.contains(identity))
        {
            sources.named_entry_source(invocation)?;
        }
    }
    Ok(())
}
