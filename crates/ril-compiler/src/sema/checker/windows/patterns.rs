//! A pattern consumes its already evaluated subject. It never reevaluates a
//! synthetic index expression to create the remainder.
use super::*;
use crate::sema::{
    evaluated::EvaluatedValue, pattern_windows as proof, source_types::SourceTypesError,
};
use ril_compiler_core::ids::PatternId;
use std::sync::Arc;

impl Checker {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::sema::checker) fn pattern_array_window(
        &mut self,
        subject: &EvaluatedValue,
        value: &Value,
        root: PatternId,
        rest: PatternId,
        prefix: u32,
        suffix: u32,
        frame: &mut Frame,
    ) -> Option<Value> {
        let span = self.semantic_hir.pattern(rest)?.info.span;
        let outcome = (|| -> Result<Value, SourceTypesError> {
            if !value.stable && value.publication != Publication::Immutable {
                self.error(
                    "E0531",
                    span,
                    "live remainder windows require a pinned stable source",
                    [value.cause],
                );
            }
            self.access(value, None, Mode::Read, span, frame);
            let owner = self.loop_allocation_context(frame.owner);
            let site = if let Some(site) = self.pattern_window_sites.get(&(rest, owner)) {
                *site
            } else {
                if !self.application_effect.admit(2) {
                    return Err(SourceTypesError::BudgetExceeded);
                }
                let site = SiteId(self.next_site);
                self.next_site = self
                    .next_site
                    .checked_add(1)
                    .ok_or(SourceTypesError::IdentityExhausted)?;
                self.pattern_window_sites.insert((rest, owner), site);
                site
            };
            let window = self.allocate_site(span, site, frame.owner);
            let allocation = self
                .last_allocation_event(window)
                .ok_or(SourceTypesError::MissingNode)?;
            self.application_effect.with_work(|work| {
                crate::sema::evaluated::charge_value_export(subject.value(), work)
            })?;
            let mut input = subject.clone();
            self.prepare_evaluation_packet(&mut input, span)?;
            let heap = Arc::new(self.entry_heap_snapshot(input.value(), input.current_epoch())?);
            let mut lease = self.application_effect.lease_work(1_000_000);
            let selected = (|| {
                let budget = lease.work();
                let mut work = budget.remaining();
                let path =
                    proof::selection(&self.semantic_hir, root, rest, prefix, suffix, &mut work);
                budget.charge(budget.remaining() - work)?;
                let path = path?;
                let mut parents = Vec::new();
                for node in &heap.nodes {
                    budget.charge(1)?;
                    let Some(info) = self.windows.get(&node.origin) else {
                        continue;
                    };
                    budget.charge(self.pattern_windows.len())?;
                    let mut found = None;
                    for (index, creation) in self.pattern_windows.iter().enumerate().rev() {
                        budget.charge(
                            1 + input
                                .current_epoch()
                                .saturating_sub(creation.output.current_epoch()),
                        )?;
                        let mut origins = creation.output.value().origins.nodes.clone();
                        for &(recent, older) in self
                            .recency_moves
                            .get(creation.output.current_epoch()..input.current_epoch())
                            .ok_or(SourceTypesError::Unresolved)?
                        {
                            if origins.remove(&recent) {
                                origins.insert(older);
                            }
                        }
                        // This search selects identity only. Independent replay
                        // authenticates the original creation and metadata.
                        if origins.contains(&node.origin) {
                            found = Some(index);
                            break;
                        }
                    }
                    if let Some(creation) = found {
                        let mut remaining = budget.remaining();
                        let admitted = proof::charge_info(info, &mut remaining);
                        budget.charge(budget.remaining() - remaining)?;
                        admitted?;
                        parents.push(proof::PatternWindowInput {
                            node: node.origin,
                            origin: proof::PatternWindowOrigin::Pattern(creation),
                            info: info.clone(),
                        });
                    } else if let Some(reference) = info.constant {
                        let mut remaining = budget.remaining();
                        let admitted = proof::charge_info(info, &mut remaining);
                        budget.charge(budget.remaining() - remaining)?;
                        admitted?;
                        parents.push(proof::PatternWindowInput {
                            node: node.origin,
                            origin: proof::PatternWindowOrigin::Constant(reference),
                            info: info.clone(),
                        });
                    } else if info.pattern.is_some() {
                        return Err(SourceTypesError::MissingNode);
                    }
                }
                let mut remaining = budget.remaining();
                let layer = proof::select_layer(
                    &self.semantic_hir,
                    input.value(),
                    &heap,
                    &parents,
                    &path,
                    &mut remaining,
                );
                budget.charge(budget.remaining() - remaining)?;
                let layer = layer?;
                if layer.origins.nodes.iter().any(|id| {
                    self.windows.contains_key(id)
                        && !parents.iter().any(|parent| parent.node == *id)
                }) {
                    return Err(SourceTypesError::Unresolved);
                }
                let cause = self.cause(
                    CauseKind::Projection,
                    span,
                    "pattern remainder window retains selected backing slots",
                    [layer.cause],
                );
                let mut remaining = budget.remaining();
                let result = proof::construct(
                    &layer,
                    &heap,
                    &parents,
                    window,
                    cause,
                    prefix,
                    suffix,
                    &mut remaining,
                );
                budget.charge(budget.remaining() - remaining)?;
                let (value, backing, lower, length) = result?;
                Ok((value, layer, parents, backing, lower, length, cause))
            })();
            let returned = self.application_effect.return_work(lease);
            let (value, layer, parents, backing, lower, length, cause) = selected?;
            returned?;
            let info = super::super::super::WindowInfo {
                pattern: Some(rest),
                constant: None,
                backing: backing.clone(),
                lower,
                length,
                span,
                cause,
            };
            self.windows.insert(window, info.clone());
            let mut retained = layer;
            retained.origins = backing;
            retained.permission = Permission::Read;
            retained.construction = false;
            retained.marker = false;
            retained.retention_result = false;
            self.store_field(window, Slot::Field(BACKING.into()), retained);
            self.array_lengths.insert(window, length);
            self.application_effect.with_work(|work| {
                crate::sema::evaluated::charge_value_export(&value, work)?;
                *work = work
                    .checked_sub(3 + self.fields.len())
                    .ok_or(SourceTypesError::BudgetExceeded)?;
                for ((node, slot), child) in &self.fields {
                    if *node != window {
                        continue;
                    }
                    let text = match slot {
                        Slot::Field(name) => name.len().div_ceil(32),
                        _ => 0,
                    };
                    *work = work
                        .checked_sub(3 + text + child.origins.nodes.len())
                        .ok_or(SourceTypesError::BudgetExceeded)?;
                    crate::sema::evaluated::charge_value_export(child, work)?;
                }
                proof::charge_info(&info, work)
            })?;
            let output_node = crate::sema::copy_contract::CopyNode {
                origin: window,
                fact: self.heap.nodes[window.0 as usize].clone(),
                fields: self
                    .fields
                    .iter()
                    .filter(|((node, _), _)| *node == window)
                    .map(|((_, slot), value)| (slot.clone(), value.clone()))
                    .collect(),
                length: Some(length),
                fixed: false,
            };
            self.pattern_windows.push(proof::PatternWindowCreation {
                allocation,
                root,
                rest,
                anchor: self.application_effect.current_activation(),
                context: self.invocation_context(frame.callable_owner),
                owner: frame.owner,
                input: Arc::new(input),
                heap,
                parents,
                prefix,
                suffix,
                output: Arc::new(EvaluatedValue::new(value.clone(), self.recency_moves.len())),
                output_node,
                info,
            });
            Ok(value)
        })();
        match outcome {
            Ok(value) => Some(value),
            Err(error) => {
                self.unsupported(
                    span,
                    format!(
                        "array remainder requires its actual subject and window derivation: {error}"
                    ),
                );
                None
            }
        }
    }
}
