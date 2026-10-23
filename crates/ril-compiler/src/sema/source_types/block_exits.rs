//! Temporary replay of a block's actual normal and abort-answer inputs.
//! Scope origins and original handler bodies select exits; cause parents only
//! identify their recorded composition, never an arbitrary equal value.
use super::SourceTypesError as Error;
use crate::hir::nodes as hir;
use crate::sema::{
    ExpressionFact,
    application_effect::{ActivationKind, EntryOrigin, EvaluationActivation, EvaluationRecord},
    evaluated::{charge_value_export, same_source_public_view, transport_value_at},
    facts::{CauseKind, Explanations, NodeId, Permission, ScopeId},
    model::{Ty, Value},
    scopes::{ScopeIndex, ScopeOrigin},
};
use ril_compiler_core::{diagnostic::CauseId, ids::ActivationEpochId};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) struct Inputs<'a> {
    pub(crate) hir: &'a hir::HirProgram,
    pub(crate) expressions: &'a [ExpressionFact],
    pub(crate) evaluations: &'a [EvaluationRecord],
    pub(crate) activations: &'a [EvaluationActivation],
    pub(crate) scopes: &'a ScopeIndex,
    pub(crate) explanations: &'a Explanations,
    pub(crate) history: &'a [(NodeId, NodeId)],
    pub(crate) open: Option<ActivationEpochId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Exit {
    pub(crate) observation: usize,
    /// Independent callers authenticate this operation with FrameIndex before
    /// consuming any Source selected by this query.
    pub(crate) operation: Option<ScopeId>,
}

fn charge(work: &mut usize, amount: usize) -> Result<(), Error> {
    *work = work.checked_sub(amount).ok_or(Error::BudgetExceeded)?;
    Ok(())
}

fn require(value: bool) -> Result<(), Error> {
    value.then_some(()).ok_or(Error::Unresolved)
}

impl Inputs<'_> {
    fn physical(
        &self,
        index: usize,
        work: &mut usize,
    ) -> Result<(&EvaluationRecord, &EvaluationActivation), Error> {
        charge(work, 3)?;
        let record = self.evaluations.get(index).ok_or(Error::MissingNode)?;
        let fact = self.expressions.get(index).ok_or(Error::MissingNode)?;
        let identity = record.identity.ok_or(Error::MissingNode)?;
        let activation = self
            .activations
            .get(identity.activation.0 as usize)
            .ok_or(Error::MissingNode)?;
        require(
            record.id.0 as usize == index
                && activation.id == identity.activation
                && activation.kind == ActivationKind::Expression
                && activation.result == Some(record.id)
                && activation.source == Some(identity.source)
                && fact.source_id == Some(identity.source)
                && activation.context == record.context
                && activation.scope == record.scope
                && record.allocation_epoch == fact.allocation_epoch
                && fact.allocation_epoch <= self.history.len()
                && activation.start_expression <= index,
        )?;
        match activation.end_expression {
            Some(end) => require(
                index < end && end <= self.evaluations.len() && end <= self.expressions.len(),
            )?,
            None => require(self.open == Some(activation.id))?,
        }
        Ok((record, activation))
    }

    fn within(
        &self,
        mut activation: ActivationEpochId,
        root: ActivationEpochId,
        work: &mut usize,
    ) -> Result<bool, Error> {
        let mut seen = BTreeSet::new();
        loop {
            charge(work, 2 + seen.len().checked_ilog2().unwrap_or(0) as usize)?;
            if activation == root {
                return Ok(true);
            }
            require(seen.insert(activation))?;
            let node = self
                .activations
                .get(activation.0 as usize)
                .filter(|node| node.id == activation)
                .ok_or(Error::MissingNode)?;
            let Some(parent) = node.parent else {
                return Ok(false);
            };
            activation = parent;
        }
    }

    fn cause(
        &self,
        cause: CauseId,
        kind: CauseKind,
        arity: usize,
        work: &mut usize,
    ) -> Result<&[CauseId], Error> {
        charge(work, 1 + arity)?;
        let node = self
            .explanations
            .causes
            .get(cause.0 as usize)
            .ok_or(Error::MissingNode)?;
        require(
            node.id == cause
                && self.explanations.kinds.get(cause.0 as usize) == Some(&kind)
                && node.parents.len() == arity,
        )?;
        Ok(&node.parents)
    }

    fn at_epoch(&self, index: usize, epoch: usize, work: &mut usize) -> Result<Value, Error> {
        let (record, _) = self.physical(index, work)?;
        transport_value_at(
            &self.expressions[index].value,
            self.history,
            record.allocation_epoch,
            epoch,
            work,
        )
    }

    /// Replay all actual recovery/abort inputs and their public join. A caller
    /// still checks each exit's Source graph and each operation's full origin.
    pub(crate) fn joined(
        &self,
        root: usize,
        tail: usize,
        work: &mut usize,
    ) -> Result<Vec<Exit>, Error> {
        let (root_record, root_activation) = self.physical(root, work)?;
        let (_, tail_activation) = self.physical(tail, work)?;
        require(tail_activation.parent == Some(root_activation.id))?;
        let source = root_record.identity.ok_or(Error::MissingNode)?.source;
        let hir::ExprKind::Block(block) =
            &self.hir.expression(source).ok_or(Error::MissingNode)?.kind
        else {
            return Err(Error::Unresolved);
        };
        charge(
            work,
            self.evaluations.len() + self.scopes.records().len() + block.statements.len() + 1,
        )?;
        let mut bodies =
            BTreeMap::<(ScopeId, ril_compiler_core::ids::ExprId), Option<usize>>::new();
        for (index, record) in self.evaluations.iter().enumerate() {
            let Some(identity) = record.identity else {
                continue;
            };
            charge(work, 2 + bodies.len().checked_ilog2().unwrap_or(0) as usize)?;
            bodies
                .entry((record.scope, identity.source))
                .and_modify(|entry| *entry = None)
                .or_insert(Some(index));
        }
        let mut candidates = Vec::new();
        for scope in self.scopes.records() {
            let ScopeOrigin::Operation(entry) = &scope.origin else {
                continue;
            };
            if !matches!(
                entry.origin,
                EntryOrigin::Generated { .. } | EntryOrigin::Application(_)
            ) {
                continue;
            }
            let Some(parent) = entry.parent else { continue };
            if !self.within(parent, root_activation.id, work)? {
                continue;
            }
            let body = entry.body.ok_or(Error::MissingNode)?;
            let original = self.hir.expression(body).ok_or(Error::MissingNode)?;
            let hir::LexicalOwner::HandlerArm { statement, index } = original.info.owner else {
                return Err(Error::Unresolved);
            };
            charge(
                work,
                block.statements.len() + 2 + bodies.len().checked_ilog2().unwrap_or(0) as usize,
            )?;
            if !block.statements.contains(&statement) {
                continue;
            }
            let hir::StmtKind::Handler(arms) = &self
                .hir
                .statement(statement)
                .ok_or(Error::MissingNode)?
                .kind
            else {
                return Err(Error::Unresolved);
            };
            require(arms.get(index as usize).is_some_and(|arm| arm.body == body))?;
            let observation = bodies
                .get(&(scope.id, body))
                .copied()
                .flatten()
                .ok_or(Error::MissingNode)?;
            let (record, activation) = self.physical(observation, work)?;
            require(
                record.context == entry.context
                    && activation.parent == Some(parent)
                    && entry.allocation_epoch <= record.allocation_epoch,
            )?;
            charge(work, candidates.len() + 1)?;
            candidates.push(Exit {
                observation,
                operation: Some(scope.id),
            });
        }
        let normal_cause = self.expressions[tail].value.cause;
        let mut cursor = self.expressions[root].value.cause;
        let mut joins = Vec::new();
        let mut seen = BTreeSet::new();
        let mut base_recovery = None;
        while cursor != normal_cause {
            charge(work, 2 + seen.len().checked_ilog2().unwrap_or(0) as usize)?;
            require(seen.insert(cursor.0))?;
            match self.explanations.kinds.get(cursor.0 as usize) {
                Some(CauseKind::BranchJoin) => {
                    let parents = self.cause(cursor, CauseKind::BranchJoin, 2, work)?;
                    charge(work, joins.len() + 1)?;
                    joins.push((cursor, parents[1]));
                    cursor = parents[0];
                }
                Some(CauseKind::Handler) => {
                    base_recovery = Some(cursor);
                    break;
                }
                _ => return Err(Error::Unresolved),
            }
        }
        let mut used = BTreeSet::new();
        let mut exits = Vec::new();
        let mut answer = if let Some(cause) = base_recovery {
            self.answer(
                cause,
                &candidates,
                root_record.allocation_epoch,
                &mut used,
                &mut exits,
                work,
            )?
        } else {
            let value = self.at_epoch(tail, root_record.allocation_epoch, work)?;
            if value.ty != Ty::Never || candidates.is_empty() {
                charge(work, 1)?;
                exits.push(Exit {
                    observation: tail,
                    operation: None,
                });
            }
            value
        };
        for (cause, recovery) in joins.into_iter().rev() {
            let recovered = self.answer(
                recovery,
                &candidates,
                root_record.allocation_epoch,
                &mut used,
                &mut exits,
                work,
            )?;
            if recovered.ty != Ty::Never && answer.ty != Ty::Never {
                let before = *work;
                charge_value_export(&recovered, work)?;
                charge_value_export(&answer, work)?;
                let size = before - *work;
                charge(work, size.checked_mul(size).ok_or(Error::BudgetExceeded)?)?;
                // Source-public fields do not depend on the choice ordinal;
                // heap correlation and duties remain their own receipt checks.
                answer = recovered.join(&answer, 0, cause);
            } else if answer.ty == Ty::Never {
                answer = recovered;
            }
            answer.cause = cause;
        }
        require(
            used.len() == candidates.len()
                && !exits.is_empty()
                && same_source_public_view(&answer, &self.expressions[root].value, work)?,
        )?;
        Ok(exits)
    }

    fn answer(
        &self,
        cause: CauseId,
        candidates: &[Exit],
        epoch: usize,
        used: &mut BTreeSet<usize>,
        exits: &mut Vec<Exit>,
        work: &mut usize,
    ) -> Result<Value, Error> {
        let parents = self.cause(cause, CauseKind::Handler, 1, work)?;
        charge(work, candidates.len())?;
        let mut matches = candidates
            .iter()
            .filter(|candidate| self.expressions[candidate.observation].value.cause == parents[0]);
        let selected = *matches.next().ok_or(Error::MissingNode)?;
        require(matches.next().is_none())?;
        charge(work, 2 + used.len().checked_ilog2().unwrap_or(0) as usize)?;
        require(used.insert(selected.observation))?;
        let mut value = self.at_epoch(selected.observation, epoch, work)?;
        // This is the ordinary nullary abort-answer reception. Non-nullary
        // operation loans require their separate retained reception evidence.
        let scope = selected
            .operation
            .and_then(|id| self.scopes.get(&id))
            .ok_or(Error::MissingNode)?;
        let ScopeOrigin::Operation(entry) = &scope.origin else {
            return Err(Error::Unresolved);
        };
        let body = entry.body.ok_or(Error::MissingNode)?;
        let hir::LexicalOwner::HandlerArm { statement, index } = self
            .hir
            .expression(body)
            .ok_or(Error::MissingNode)?
            .info
            .owner
        else {
            return Err(Error::Unresolved);
        };
        let hir::StmtKind::Handler(arms) = &self
            .hir
            .statement(statement)
            .ok_or(Error::MissingNode)?
            .kind
        else {
            return Err(Error::Unresolved);
        };
        require(
            arms.get(index as usize)
                .is_some_and(|arm| arm.parameters.is_empty()),
        )?;
        let mut pending = vec![hir::NodeId::Expr(body)];
        let mut seen = BTreeSet::new();
        while let Some(node) = pending.pop() {
            charge(work, 2 + seen.len().checked_ilog2().unwrap_or(0) as usize)?;
            if !seen.insert(node) {
                continue;
            }
            if let hir::NodeId::Expr(id) = node
                && matches!(
                    self.hir.expression(id).ok_or(Error::MissingNode)?.kind,
                    hir::ExprKind::Control { .. }
                )
            {
                return Err(Error::Unresolved);
            }
            let children =
                self.hir
                    .children_with_work(node, work)
                    .map_err(|error| match error {
                        hir::WalkError::Budget => Error::BudgetExceeded,
                        hir::WalkError::MissingNode(_) => Error::MissingNode,
                    })?;
            charge(work, pending.len() + children.len() + 1)?;
            pending.extend(children);
        }
        if value.temporary {
            value.permission = Permission::Read;
            value.construction = false;
        }
        value.cause = cause;
        if value.ty != Ty::Never {
            charge(work, exits.len() + 1)?;
            exits.push(selected);
        }
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::SemanticFacts;
    use ril_compiler_core::ids::BlockAnchor;

    fn inputs(facts: &SemanticFacts) -> Inputs<'_> {
        Inputs {
            hir: facts.semantic_hir.as_deref().unwrap(),
            expressions: &facts.expressions,
            evaluations: &facts.evaluations,
            activations: &facts.activations,
            scopes: &facts.scopes,
            explanations: &facts.explanations,
            history: &facts.allocation_history,
            open: None,
        }
    }

    fn fixture() -> (SemanticFacts, usize, usize, Vec<Exit>) {
        let verified = crate::Session::new(
            ril_test::case_bytes("tests/regressions/defaults.ril::local-budget").to_vec(),
        )
        .verify()
        .unwrap();
        let facts = verified.facts();
        let query = inputs(facts);
        for (root, record) in facts.evaluations.iter().enumerate() {
            if record.context.default_use.is_none() {
                continue;
            }
            let Some(identity) = record.identity else {
                continue;
            };
            if !matches!(
                query.hir.expression(identity.source).unwrap().kind,
                hir::ExprKind::Block(_)
            ) {
                continue;
            }
            let Some((_, source)) = crate::hir::blocks::BlockIndex::tail_from_hir(
                query.hir,
                BlockAnchor::ExpressionBody(identity.source),
                &mut 65536,
            )
            .unwrap() else {
                continue;
            };
            let Some((tail, _)) = facts.evaluations.iter().enumerate().find(|(_, child)| {
                child.identity.is_some_and(|id| {
                    id.source == source
                        && facts.activations[id.activation.0 as usize].parent
                            == Some(identity.activation)
                })
            }) else {
                continue;
            };
            if let Ok(exits) = query.joined(root, tail, &mut 65536)
                && exits.len() >= 2
                && exits.iter().any(|exit| exit.operation.is_some())
            {
                return (facts.clone(), root, tail, exits);
            }
        }
        panic!("the real default must join its normal and recovery answers")
    }

    #[test]
    fn actual_block_recovery_sources_replay_the_normal_and_handler_public_views() {
        let (facts, root, tail, exits) = fixture();
        assert!(
            exits
                .iter()
                .any(|exit| exit.observation == tail && exit.operation.is_none())
        );
        let source = facts.expressions[root].source_id.unwrap();
        let sources =
            crate::sema::record_bound_validation::OriginalOperandSources::new(&facts).unwrap();
        assert!(
            sources
                .observed_with_work(source, root, &mut 65536)
                .unwrap()
                .0
                .is_some()
        );
    }

    #[test]
    fn block_recovery_cannot_borrow_a_sibling_scope_body_or_cause() {
        let (facts, root, tail, exits) = fixture();
        let recovery = exits.iter().find(|exit| exit.operation.is_some()).unwrap();
        for mutation in 0..7 {
            let mut changed = facts.clone();
            match mutation {
                0 => {
                    changed.scopes.remove(&recovery.operation.unwrap());
                }
                1 => {
                    let ScopeOrigin::Operation(entry) = &mut changed
                        .scopes
                        .get_mut(recovery.operation.as_ref().unwrap())
                        .unwrap()
                        .origin
                    else {
                        unreachable!()
                    };
                    entry.body = changed.expressions[tail].source_id;
                }
                2 => {
                    let ScopeOrigin::Operation(entry) = &mut changed
                        .scopes
                        .get_mut(recovery.operation.as_ref().unwrap())
                        .unwrap()
                        .origin
                    else {
                        unreachable!()
                    };
                    entry.parent = changed.evaluations[root].identity.map(|id| id.activation);
                }
                3 => {
                    changed.explanations.causes[facts.expressions[root].value.cause.0 as usize]
                        .parents
                        .swap(0, 1);
                }
                4 => {
                    changed.expressions[recovery.observation]
                        .value
                        .corrupt_value(&mut 4_000_000)
                        .unwrap()
                        .ty = Ty::Str;
                }
                5 => {
                    changed.evaluations[recovery.observation].allocation_epoch += 1;
                }
                _ => {
                    // Erasing the join cause cannot erase the actually entered
                    // recovery frame and turn its normal tail into every exit.
                    let cause = changed.expressions[tail].value.cause;
                    changed.expressions[root]
                        .value
                        .corrupt_value(&mut 4_000_000)
                        .unwrap()
                        .cause = cause;
                }
            }
            assert!(
                inputs(&changed).joined(root, tail, &mut 65536).is_err(),
                "mutation {mutation}"
            );
        }
    }

    #[test]
    fn block_recovery_join_replay_uses_one_exact_shared_work_allowance() {
        let (facts, root, tail, expected) = fixture();
        let query = inputs(&facts);
        let mut work = 65536;
        assert_eq!(query.joined(root, tail, &mut work).unwrap(), expected);
        let cost = 65536 - work;
        let mut exact = cost;
        assert_eq!(query.joined(root, tail, &mut exact).unwrap(), expected);
        assert_eq!(exact, 0);
        for initial in [0, cost - 1] {
            assert!(query.joined(root, tail, &mut { initial }).is_err());
        }
    }
}
