//! A uniform control-result type follows every checked branch emission.
//! This proves type coordinates, not which branch executed or its authority.
use crate::hir::nodes::{ExprKind, HirProgram};
use crate::sema::source_types::{
    SourceNode, SourceScalar, SourceSchema, SourceTypeQueries, SourceTypesError as Error,
    WorkLimit,
    projection_receipts::{ProjectionOccurrence, ProjectionReceipts},
};
use ril_compiler_core::ids::{EvaluationOccurrenceId, ExprId};

pub(crate) fn result_children(
    hir: &HirProgram,
    source: ExprId,
    work: &mut WorkLimit,
) -> Result<Option<Vec<ExprId>>, Error> {
    work.charge(1)?;
    Ok(
        match &hir.expression(source).ok_or(Error::MissingNode)?.kind {
            ExprKind::If {
                then_branch,
                else_branch: Some(other),
                ..
            }
            | ExprKind::IfLet {
                then_branch,
                else_branch: Some(other),
                ..
            } => Some(vec![*then_branch, *other]),
            ExprKind::Match {
                arms,
                type_match: false,
                ..
            } => {
                work.charge(arms.len())?;
                Some(arms.iter().map(|arm| arm.body).collect())
            }
            _ => None,
        },
    )
}

pub(crate) fn contributors(
    hir: &HirProgram,
    receipts: &ProjectionReceipts<'_>,
    root: EvaluationOccurrenceId,
    work: &mut WorkLimit,
) -> Result<Option<Vec<EvaluationOccurrenceId>>, Error> {
    work.charge(3)?;
    let record = receipts
        .evaluations
        .get(root.0 as usize)
        .ok_or(Error::MissingNode)?;
    let fact = receipts
        .expressions
        .get(root.0 as usize)
        .ok_or(Error::MissingNode)?;
    let Some(source) = fact.source_id else {
        return Ok(None);
    };
    let Some(children) = result_children(hir, source, work)? else {
        return Ok(None);
    };
    let identity = record.identity.ok_or(Error::MissingNode)?;
    if record.id != root || source != identity.source {
        return Err(Error::Unresolved);
    }
    let parent = ProjectionOccurrence {
        identity,
        context: record.context,
        cause: fact.value.cause,
    };
    let mut inputs = Vec::with_capacity(children.len());
    for child in children {
        inputs.push(receipts.child_observation(parent, child, work)?);
    }
    if inputs.is_empty() {
        return Err(Error::Unresolved);
    }
    Ok(Some(inputs))
}

pub(crate) fn never(schema: &SourceSchema, work: &mut WorkLimit) -> Result<bool, Error> {
    let (types, root) = schema.graph();
    let root = types.unalias(root, work)?;
    Ok(matches!(
        types.get(root)?,
        SourceNode::Scalar(SourceScalar::Never)
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn control_result_sources_require_every_original_child_occurrence() {
        let source = ril_test::case_bytes(
            "tests/regressions/stdlib-declarations.ril::generic-control-results-pointer64",
        );
        let program = crate::Session::new(source.to_vec()).verify().unwrap();
        let facts = program.facts();
        let hir = facts.semantic_hir.as_deref().unwrap();
        let mut checked = 0;
        for record in &facts.evaluations {
            let Some(identity) = record.identity else {
                continue;
            };
            if hir.expression(identity.source).unwrap().info.span.file.0 != 0
                || result_children(hir, identity.source, &mut WorkLimit::new(4096))
                    .unwrap()
                    .is_none()
            {
                continue;
            }
            let inputs = contributors(
                hir,
                &ProjectionReceipts::from_facts(facts),
                record.id,
                &mut WorkLimit::new(100_000),
            )
            .unwrap()
            .unwrap();
            assert_eq!(inputs.len(), 2);
            assert!(
                contributors(
                    hir,
                    &ProjectionReceipts::from_facts(facts),
                    record.id,
                    &mut WorkLimit::new(0)
                )
                .is_err()
            );
            for child in inputs {
                for mutation in 0..3 {
                    let mut changed = facts.clone();
                    let child_activation = changed.evaluations[child.0 as usize]
                        .identity
                        .unwrap()
                        .activation
                        .0 as usize;
                    match mutation {
                        0 => changed.activations[child_activation].parent = None,
                        1 => changed.activations[child_activation].result = None,
                        _ => changed.expressions[child.0 as usize].source_id = None,
                    }
                    assert!(
                        contributors(
                            hir,
                            &ProjectionReceipts::from_facts(&changed),
                            record.id,
                            &mut WorkLimit::new(100_000)
                        )
                        .is_err(),
                        "{:?}: child {child:?}, mutation {mutation}",
                        record.id
                    );
                }
            }
            let mut changed = facts.clone();
            changed.evaluations[record.id.0 as usize].id = EvaluationOccurrenceId(u32::MAX);
            assert!(
                contributors(
                    hir,
                    &ProjectionReceipts::from_facts(&changed),
                    record.id,
                    &mut WorkLimit::new(100_000)
                )
                .is_err()
            );
            checked += 1;
        }
        assert!(
            checked >= 3,
            "fixture lost its generic if/match/panic joins"
        );
    }
}
