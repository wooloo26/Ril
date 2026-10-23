//! Invocation inputs keep their evaluation birth while current storage moves.
use super::*;
use crate::sema::{
    application_effect::EntryArgument,
    copy_contract::{CopyHeapSnapshot, CopyNode},
    source_types::SourceTypesError,
};
use std::sync::Arc;

fn charge(work: &mut usize, amount: usize) -> Result<(), SourceTypesError> {
    let Some(remaining) = work.checked_sub(amount) else {
        *work = 0;
        return Err(SourceTypesError::BudgetExceeded);
    };
    *work = remaining;
    Ok(())
}

fn slot_work(slot: &Slot) -> usize {
    match slot {
        Slot::Field(name) => name.len(),
        Slot::RowTail(crate::sema::model::rows::RowIdentity::Binder(name)) => name.len(),
        Slot::RowTail(crate::sema::model::rows::RowIdentity::Fresh { owner, .. }) => owner.len(),
        _ => 0,
    }
}

impl Checker {
    pub(super) fn freeze_entry_callee(
        &mut self,
        callee: Option<Arc<EvaluatedValue>>,
        span: Span,
    ) -> Result<Option<Arc<EvaluatedValue>>, SourceTypesError> {
        callee
            .map(|callee| {
                if callee.current_epoch() == self.recency_moves.len() {
                    return Ok(callee);
                }
                let mut packet = self.clone_evaluation_packet(&callee, span)?;
                self.prepare_evaluation_packet(&mut packet, span)?;
                Ok(Arc::new(packet))
            })
            .transpose()
    }
    pub(super) fn resolve_named_callee_packet(
        &mut self,
        original: &Arc<EvaluatedValue>,
        span: Span,
    ) -> Result<Arc<EvaluatedValue>, SourceTypesError> {
        let mut packet = self.clone_evaluation_packet(original, span)?;
        self.prepare_evaluation_packet(&mut packet, span)?;
        let epoch = self.recency_moves.len();
        let value = self.read_evaluation_packet(&packet, span)?;
        let value = self.named_environment_value(value, false);
        let moves = &self.recency_moves;
        let value = self.application_effect.with_work(|work| {
            crate::sema::evaluated::transport_value_at(&value, moves, epoch, moves.len(), work)
        })?;
        self.prepare_evaluation_packet(&mut packet, span)?;
        let unchanged = self.application_effect.with_work(|work| {
            crate::sema::evaluated::same_birth_value(packet.value(), &value, work)
        })?;
        if !unchanged {
            packet.invalidate_current_source();
            packet.value = value;
        } else if original.current_epoch() == self.recency_moves.len() {
            return Ok(original.clone());
        }
        Ok(Arc::new(packet))
    }
    pub(super) fn finish_numeric_entry_arguments(
        &mut self,
        event: crate::sema::copy_contract::CopyCallEventId,
        args: &mut [EntryArgument],
    ) -> Result<(), SourceTypesError> {
        if args.iter().any(|argument| argument.value().ty == Ty::Never) {
            for argument in args.iter_mut() {
                if let Ty::NumericHole(id) = argument.value().ty {
                    let expected = self
                        .numeric_preference(id)?
                        .unwrap_or_else(|| Ty::Int("int".into()));
                    let mut packet =
                        self.clone_evaluation_packet(&argument.packet, argument.span)?;
                    self.select_numeric_packet(&mut packet, &expected, argument.span)?;
                    argument.packet = Arc::new(packet);
                    argument.heap = None;
                }
            }
            self.numeric.applications.remove(&event);
            Ok(())
        } else {
            let mut values = self.entry_values(args)?;
            self.finish_numeric_arguments(event, &mut values)
        }
    }
    /// Only generated values and formal probes may enter through this adapter.
    /// It supplies no observation, captured Source or invented evaluation token.
    pub(super) fn uncaptured_entry_arguments(
        &mut self,
        args: Vec<(ParameterMode, Value, Span)>,
    ) -> Result<Arc<Vec<EntryArgument>>, SourceTypesError> {
        let cost = args
            .len()
            .checked_mul(2)
            .and_then(|cost| cost.checked_add(1))
            .ok_or(SourceTypesError::BudgetExceeded)?;
        if !self.application_effect.admit(cost) {
            return Err(SourceTypesError::BudgetExceeded);
        }
        Ok(Arc::new(
            args.into_iter()
                .map(|(mode, value, span)| EntryArgument {
                    mode,
                    packet: Arc::new(EvaluatedValue::new(value, self.recency_moves.len())),
                    span,
                    heap: None,
                })
                .collect(),
        ))
    }

    pub(super) fn entry_values(
        &mut self,
        args: &[EntryArgument],
    ) -> Result<Vec<(ParameterMode, Value, Span)>, SourceTypesError> {
        if !self.application_effect.admit(args.len()) {
            return Err(SourceTypesError::BudgetExceeded);
        }
        args.iter()
            .map(|argument| {
                Ok((
                    argument.mode,
                    self.read_evaluation_packet(&argument.packet, argument.span)?,
                    argument.span,
                ))
            })
            .collect()
    }

    /// Freeze each actual target's inputs at its own entry epoch. Another
    /// target may have allocated or changed storage since the preceding entry.
    pub(super) fn freeze_entry_arguments(
        &mut self,
        args: &[EntryArgument],
    ) -> Result<Arc<Vec<EntryArgument>>, SourceTypesError> {
        if !self.application_effect.admit(1 + args.len()) {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let mut result = Vec::with_capacity(args.len());
        for argument in args {
            let packet = if argument.packet.current_epoch() == self.recency_moves.len() {
                argument.packet.clone()
            } else {
                let mut packet = self.clone_evaluation_packet(&argument.packet, argument.span)?;
                self.prepare_evaluation_packet(&mut packet, argument.span)?;
                Arc::new(packet)
            };
            let heap = Some(Arc::new(
                self.entry_heap_snapshot(packet.value(), packet.current_epoch())?,
            ));
            result.push(EntryArgument {
                mode: argument.mode,
                packet,
                span: argument.span,
                heap,
            });
        }
        Ok(Arc::new(result))
    }

    pub(in crate::sema::checker) fn entry_heap_snapshot(
        &mut self,
        value: &Value,
        epoch: usize,
    ) -> Result<CopyHeapSnapshot, SourceTypesError> {
        let heap = &self.heap;
        let fields = &self.fields;
        let lengths = &self.array_lengths;
        let fixed = &self.fixed_arrays;
        self.application_effect.with_work(|work| {
            charge(work, 1 + value.origins.nodes.len())?;
            let mut pending: Vec<_> = value.origins.nodes.iter().copied().collect();
            let mut reachable = BTreeSet::new();
            while let Some(origin) = pending.pop() {
                charge(
                    work,
                    2 + reachable.len().checked_ilog2().unwrap_or(0) as usize,
                )?;
                if !reachable.insert(origin) {
                    continue;
                }
                let node = heap
                    .nodes
                    .get(origin.0 as usize)
                    .ok_or(SourceTypesError::MissingNode)?;
                charge(work, node.fields.len())?;
                for children in node.fields.values() {
                    charge(work, children.len())?;
                    pending.extend(children);
                }
            }
            charge(work, reachable.len())?;
            let mut nodes = Vec::with_capacity(reachable.len());
            for origin in reachable {
                let fact = heap
                    .nodes
                    .get(origin.0 as usize)
                    .ok_or(SourceTypesError::MissingNode)?;
                charge(work, 4 + fact.fields.len() + fact.writable_roots.len())?;
                for (slot, children) in &fact.fields {
                    charge(work, slot_work(slot) + children.len())?;
                }
                let mut frozen_fields = Vec::new();
                charge(work, 2 + fields.len().checked_ilog2().unwrap_or(0) as usize)?;
                for ((parent, slot), child) in fields.range((origin, Slot::Field(String::new()))..)
                {
                    charge(work, 1)?;
                    if *parent != origin {
                        break;
                    }
                    charge(work, 1 + slot_work(slot))?;
                    let child = crate::sema::evaluated::transport_value_at(child, &[], 0, 0, work)?;
                    frozen_fields.push((slot.clone(), child));
                }
                nodes.push(CopyNode {
                    origin,
                    fact: fact.clone(),
                    fields: frozen_fields,
                    length: lengths.get(&origin).copied(),
                    fixed: fixed.contains(&origin),
                });
            }
            let mut relations = Vec::new();
            for (index, left) in nodes.iter().enumerate() {
                for right in &nodes[index..] {
                    charge(work, 1)?;
                    relations.push((
                        left.origin,
                        right.origin,
                        heap.relation(left.origin, right.origin),
                    ));
                }
            }
            Ok(CopyHeapSnapshot {
                allocation_epoch: epoch,
                nodes,
                relations,
            })
        })
    }
}
