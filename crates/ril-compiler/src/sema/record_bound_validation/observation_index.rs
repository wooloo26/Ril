//! Immutable lookup over genuine observation identities. Row order is not
//! physical evaluation order, and repeated source occurrences remain distinct.
use super::{Check, SemanticFacts, require};
use crate::sema::effect_identity::{InvocationContext, InvocationExpression};
use ril_compiler_core::ids::ExprId;
use std::{collections::BTreeMap, ops::Range};

const MAX_OBSERVATIONS: usize = 1_000_000;

#[derive(Debug)]
pub(super) struct ObservationIndex<'a> {
    by_expression: BTreeMap<usize, &'a InvocationExpression>,
    by_source: BTreeMap<(ExprId, InvocationContext), Vec<usize>>,
}

fn lookup_work(entries: usize) -> usize {
    entries.checked_ilog2().map_or(1, |log| log as usize + 1)
}

fn charge(work: &mut usize, cost: usize) -> Check {
    *work = work
        .checked_sub(cost)
        .ok_or_else(|| "Source observation lookup exceeds its work bound".to_owned())?;
    Ok(())
}

impl<'a> ObservationIndex<'a> {
    #[cfg(test)]
    pub(super) fn new(facts: &'a SemanticFacts) -> Check<Self> {
        Self::new_with_work(facts, &mut { MAX_OBSERVATIONS })
    }
    pub(super) fn new_with_work(facts: &'a SemanticFacts, work: &mut usize) -> Check<Self> {
        require(
            facts.expressions.len() <= MAX_OBSERVATIONS
                && facts.invocation_expressions.len() <= MAX_OBSERVATIONS,
            "Source observation index exceeds its arena bound",
        )?;
        let mut by_expression = BTreeMap::new();
        let mut by_source: BTreeMap<_, Vec<_>> = BTreeMap::new();
        for row in &facts.invocation_expressions {
            charge(
                work,
                3 + lookup_work(by_expression.len()) + lookup_work(by_source.len()),
            )?;
            let fact = facts.expressions.get(row.expression).ok_or_else(|| {
                "Source observation index has an out-of-arena expression".to_owned()
            })?;
            require(
                by_expression.insert(row.expression, row).is_none(),
                "Source observation index repeats a physical expression",
            )?;
            if let Some(source) = fact.source_id {
                require(
                    facts
                        .semantic_hir
                        .as_deref()
                        .is_some_and(|hir| hir.expression(source).is_some()),
                    "Source observation index has no owning HIR expression",
                )?;
                by_source
                    .entry((source, row.context))
                    .or_default()
                    .push(row.expression);
            }
        }
        for indices in by_source.values_mut() {
            charge(
                work,
                indices.len().saturating_mul(lookup_work(indices.len())),
            )?;
            indices.sort_unstable();
        }
        Ok(Self {
            by_expression,
            by_source,
        })
    }

    pub(super) fn row(
        &self,
        expression: usize,
        work: &mut usize,
    ) -> Check<&'a InvocationExpression> {
        charge(work, lookup_work(self.by_expression.len()))?;
        self.by_expression
            .get(&expression)
            .copied()
            .ok_or_else(|| "Source expression lost its actual observation context".to_owned())
    }

    /// Charge the bounded tree lookup and both binary searches. A caller that
    /// scans returned candidates must additionally charge those candidates.
    pub(super) fn range(
        &self,
        source: ExprId,
        context: InvocationContext,
        range: Range<usize>,
        work: &mut usize,
    ) -> Check<&[usize]> {
        require(
            range.start <= range.end,
            "Source observation interval is reversed",
        )?;
        charge(work, lookup_work(self.by_source.len()))?;
        let Some(indices) = self.by_source.get(&(source, context)) else {
            return Ok(&[]);
        };
        charge(work, 2 * lookup_work(indices.len()))?;
        let start = indices.partition_point(|index| *index < range.start);
        let end = indices.partition_point(|index| *index < range.end);
        Ok(&indices[start..end])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        hir::nodes::{HirProgram, InputOrigin},
        sema::{
            ExpressionFact,
            application_effect::{
                ActivationKind, EvaluationActivation, EvaluationRecord, OccurrenceIdentity,
            },
            facts::ScopeId,
            model::{Ty, Value},
        },
    };
    use ril_compiler_core::{
        diagnostic::CauseId,
        ids::{ActivationEpochId, CallableOwner, EvaluationOccurrenceId},
        source::{FileId, Span},
    };
    use ril_syntax::ast::{self, ExprKind, StmtKind};
    use std::sync::Arc;

    fn context() -> InvocationContext {
        InvocationContext {
            invocation: None,
            owner: Some(CallableOwner::Global),
            closure: None,
            closure_invocation: None,
            budget_validation: false,
            default_use: None,
        }
    }

    fn model(extra_tail: bool) -> (SemanticFacts, ast::Expr, ExprId) {
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 1,
        };
        let statement = |expression| ast::Stmt {
            hir_id: None,
            span,
            kind: StmtKind::Expr {
                expression,
                terminated: false,
            },
        };
        let mut program = ast::Program {
            statements: vec![statement(ast::Expr {
                hir_id: None,
                span,
                kind: ExprKind::Block(ast::Block {
                    span,
                    where_items: vec![],
                    statements: vec![statement(ast::Expr {
                        hir_id: None,
                        span,
                        kind: ExprKind::Tuple(vec![]),
                    })],
                }),
            })],
        };
        let hir = HirProgram::lower_identified(&mut program, InputOrigin::Source).unwrap();
        let StmtKind::Expr { expression, .. } = &program.statements[0].kind else {
            unreachable!()
        };
        let expression = expression.clone();
        let ExprKind::Block(block) = &expression.kind else {
            unreachable!()
        };
        let StmtKind::Expr {
            expression: tail, ..
        } = &block.statements[0].kind
        else {
            unreachable!()
        };
        let tail = tail.hir_id.unwrap();
        let root = expression.hir_id.unwrap();
        let mut facts = SemanticFacts {
            semantic_hir: Some(Arc::new(hir)),
            source_program: Some(Arc::new(program)),
            ..Default::default()
        };
        let mut sequence = vec![tail, root, tail];
        if extra_tail {
            sequence.push(tail);
        }
        sequence.push(root);
        for (index, source) in sequence.into_iter().enumerate() {
            facts.expressions.push(ExpressionFact {
                allocation_epoch: 0,
                source_id: Some(source),
                span,
                value: Value::scalar(Ty::Tuple(vec![]), None, CauseId(0)),
            });
            facts.invocation_expressions.push(InvocationExpression {
                expression: index,
                context: context(),
                argument_of: None,
            });
        }
        // Allocation is preorder; the corresponding value records are
        // postorder. Each repeated block owns its own direct tail activation.
        let last = facts.expressions.len() - 1;
        for (id, source, parent, start, result, end) in [
            (0, root, None, 0, 1, 2),
            (1, tail, Some(0), 0, 0, 1),
            (2, root, None, 2, last, last + 1),
            (3, tail, Some(2), 2, 2, 3),
        ] {
            facts.activations.push(EvaluationActivation {
                id: ActivationEpochId(id),
                parent: parent.map(ActivationEpochId),
                kind: ActivationKind::Expression,
                source: Some(source),
                scope: ScopeId(0),
                context: context(),
                start_expression: start,
                end_expression: Some(end),
                result: Some(EvaluationOccurrenceId(result as u32)),
            });
        }
        if extra_tail {
            facts.activations.push(EvaluationActivation {
                id: ActivationEpochId(4),
                parent: Some(ActivationEpochId(2)),
                kind: ActivationKind::Expression,
                source: Some(tail),
                scope: ScopeId(0),
                context: context(),
                start_expression: 3,
                end_expression: Some(4),
                result: Some(EvaluationOccurrenceId(3)),
            });
        }
        for (index, fact) in facts.expressions.iter().enumerate() {
            let activation = facts
                .activations
                .iter()
                .find(|activation| activation.result == Some(EvaluationOccurrenceId(index as u32)))
                .unwrap();
            facts.evaluations.push(EvaluationRecord {
                id: EvaluationOccurrenceId(index as u32),
                identity: Some(OccurrenceIdentity {
                    source: fact.source_id.unwrap(),
                    activation: activation.id,
                }),
                scope: ScopeId(0),
                context: context(),
                allocation_epoch: 0,
            });
        }
        (facts, expression, tail)
    }

    #[test]
    fn disordered_rows_keep_physical_ranges_and_complete_context_identity() {
        let (mut facts, expression, tail) = model(false);
        let mut other = context();
        other.budget_validation = true;
        facts.invocation_expressions[0].context = other;
        facts.invocation_expressions.reverse();
        let index = ObservationIndex::new(&facts).unwrap();
        let mut work = 4096;
        assert_eq!(index.row(0, &mut work).unwrap().context, other);
        assert_eq!(index.range(tail, context(), 0..4, &mut work).unwrap(), &[2]);
        assert_eq!(index.range(tail, other, 0..4, &mut work).unwrap(), &[0]);
        assert_eq!(
            index
                .range(expression.hir_id.unwrap(), context(), 0..3, &mut work)
                .unwrap(),
            &[1]
        );
        assert!(work < 4096);
        assert!(index.row(0, &mut 0).is_err());
        assert!(index.range(tail, context(), 0..4, &mut 0).is_err());
    }

    #[test]
    fn duplicate_and_outside_rows_cannot_enter_the_index() {
        let (facts, _, _) = model(false);
        assert!(ObservationIndex::new(&facts).is_ok());
        let mut duplicated = facts.clone();
        duplicated
            .invocation_expressions
            .push(duplicated.invocation_expressions[0].clone());
        assert!(
            ObservationIndex::new(&duplicated)
                .unwrap_err()
                .contains("repeats")
        );
        let mut outside = facts;
        outside.invocation_expressions[0].expression = outside.expressions.len();
        assert!(
            ObservationIndex::new(&outside)
                .unwrap_err()
                .contains("out-of-arena")
        );
    }

    fn key(
        facts: &SemanticFacts,
        expression: &ast::Expr,
        root: usize,
    ) -> Check<crate::sema::effect_identity::ArgumentKey> {
        let replay = super::super::Replay::new(facts)?;
        let sites = super::super::explicit_named::source_sites_base(facts)?;
        replay.original_observed_source_key(expression, root, context(), &sites)
    }

    #[test]
    fn repeated_equal_blocks_require_the_exact_root_and_one_child_in_that_round() {
        let (mut facts, expression, _) = model(false);
        facts.invocation_expressions.reverse();
        assert_eq!(
            key(&facts, &expression, 1).unwrap(),
            crate::sema::effect_identity::ArgumentKey::Tuple(vec![])
        );
        assert_eq!(
            key(&facts, &expression, 3).unwrap(),
            crate::sema::effect_identity::ArgumentKey::Tuple(vec![])
        );
        let replay = super::super::Replay::new(&facts).unwrap();
        let sites = super::super::explicit_named::source_sites_base(&facts).unwrap();
        assert!(
            replay
                .original_source_key(&expression, &facts.expressions[3].value, context(), &sites)
                .is_err(),
            "equal repeated roots cannot select an arbitrary matching occurrence"
        );
        let mut missing = facts;
        missing
            .invocation_expressions
            .retain(|row| row.expression != 2);
        assert!(
            key(&missing, &expression, 3).is_err(),
            "the first round cannot supply the missing second tail"
        );
        let (extra, expression, _) = model(true);
        assert!(
            key(&extra, &expression, 4).is_err(),
            "two candidate tails cannot select the last one"
        );
    }

    #[test]
    fn real_programs_replay_reordered_rows_but_reject_lost_or_duplicate_physical_keys() {
        use crate::sema::validate::solved_facts;
        for case in [
            "tests/regressions/evaluation-identity.ril::application-ordinary-complete-order",
            "tests/regressions/evaluation-identity.ril::application-pipeline-named-default",
            "tests/regressions/evaluation-identity.ril::generated-adapter-per-call",
            "tests/regressions/record-bounds.ril::write-scalar",
            "tests/regressions/record-bounds.ril::scoped-empty-inner-dimension",
        ] {
            for layout in ["pointer32", "pointer64"] {
                let source = ril_test::case_source(case);
                let verified = crate::Session::with_options(
                    source.as_bytes().to_vec(),
                    crate::CheckOptions {
                        target: layout.into(),
                        ..Default::default()
                    },
                )
                .verify()
                .unwrap_or_else(|outcome| panic!("{case} {layout}: {outcome:?}"));
                let mut facts = verified.facts().clone();
                solved_facts(&facts)
                    .unwrap_or_else(|issues| panic!("{case} {layout} control: {issues:?}"));
                facts.invocation_expressions.reverse();
                solved_facts(&facts)
                    .unwrap_or_else(|issues| panic!("{case} {layout} reversed: {issues:?}"));
                let expression = facts
                    .copy_call_events
                    .iter()
                    .find_map(|event| event.callee_expression)
                    .expect("real application must retain an actual callee key");
                let row = facts
                    .invocation_expressions
                    .iter()
                    .find(|row| row.expression == expression)
                    .unwrap()
                    .clone();
                let mut duplicate = facts.clone();
                duplicate.invocation_expressions.push(row);
                assert!(
                    solved_facts(&duplicate).is_err(),
                    "{case} {layout} duplicated key"
                );
                facts
                    .invocation_expressions
                    .retain(|row| row.expression != expression);
                assert!(
                    solved_facts(&facts).is_err(),
                    "{case} {layout} missing exact callee row"
                );
            }
        }
    }
}
