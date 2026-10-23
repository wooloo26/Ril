//! A generated pattern read keeps its original PatternId and actual occurrence.
//! The temporary syntax below is a view of that existing HIR leaf, never a new
//! evaluation or a declaration inferred from the value's erased type.
use super::*;
use crate::hir::nodes as hir;
use crate::sema::application_effect::ActivationKind;
use ril_compiler_core::ids::ExprId;

fn literal_work(literal: &Literal) -> usize {
    match literal {
        Literal::Integer(text)
        | Literal::Float(text)
        | Literal::String(text)
        | Literal::RawString(text)
        | Literal::Bytes(text) => text.len().saturating_add(1),
        Literal::Bool(_) | Literal::Unit => 1,
    }
}

pub(super) fn expression(
    replay: &Replay<'_>,
    source: ExprId,
    observation: usize,
    work: &mut usize,
) -> Check<Expr> {
    source_scan_work(work, 8)?;
    let facts = replay.facts;
    let hir = facts
        .semantic_hir
        .as_deref()
        .ok_or("pattern Source has no original HIR")?;
    let expression = hir
        .expression(source)
        .ok_or("pattern Source expression is absent")?;
    let hir::NodeOrigin::Generated {
        generation,
        anchor: hir::NodeId::Pattern(anchor),
        kind: hir::GeneratedKind::PatternValue,
    } = expression.info.origin
    else {
        return Err("receiver input lost its original HIR expression".into());
    };
    let pattern = hir
        .pattern(anchor)
        .ok_or("pattern Source has no original PatternId")?;
    require(
        hir.generated_roots().get(generation as usize) == Some(&hir::NodeId::Expr(source))
            && expression.info.owner == pattern.info.owner,
        "pattern Source changed its generation or lexical owner",
    )?;
    let kind = match (&pattern.kind, &expression.kind) {
        (hir::PatternKind::Literal(original), hir::ExprKind::Literal(actual)) => {
            source_scan_work(
                work,
                literal_work(original).saturating_add(literal_work(actual)),
            )?;
            require(
                original == actual,
                "pattern Source literal differs from its original PatternId",
            )?;
            ExprKind::Literal(actual.clone())
        }
        (hir::PatternKind::Name(original), hir::ExprKind::Name(actual)) => {
            source_scan_work(work, original.len().saturating_add(actual.len()))?;
            require(
                original == actual,
                "pattern Source name differs from its original PatternId",
            )?;
            ExprKind::Name(actual.clone())
        }
        (
            hir::PatternKind::Constructor {
                path,
                arguments,
                parenthesized: false,
            },
            hir::ExprKind::Path(actual),
        ) if arguments.is_empty() => {
            source_scan_work(work, path.len().saturating_add(actual.len()))?;
            for name in path.iter().chain(actual) {
                source_scan_work(work, name.len())?;
            }
            require(
                path == actual,
                "pattern Source path differs from its original PatternId",
            )?;
            ExprKind::Path(actual.clone())
        }
        _ => return Err("receiver input has no original pattern value recipe".into()),
    };
    let fact = facts
        .expressions
        .get(observation)
        .ok_or("pattern Source has no physical value")?;
    let record = facts
        .evaluations
        .get(observation)
        .ok_or("pattern Source has no physical evaluation")?;
    let identity = record
        .identity
        .ok_or("pattern Source has no actual activation")?;
    let activation = facts
        .activations
        .get(identity.activation.0 as usize)
        .ok_or("pattern Source activation is absent")?;
    require(
        identity.source == source
            && fact.source_id == Some(source)
            && record.id.0 as usize == observation
            && activation.id == identity.activation
            && activation.source == Some(source)
            && activation.result == Some(record.id)
            && activation.kind == ActivationKind::Expression
            && activation.context == record.context
            && activation.scope == record.scope
            && activation.start_expression <= observation
            && activation.end_expression.is_some_and(|end| {
                observation < end
                    && end <= facts.expressions.len()
                    && end <= facts.evaluations.len()
            })
            && record.allocation_epoch == fact.allocation_epoch
            && fact.allocation_epoch <= facts.allocation_history.len(),
        "pattern Source borrowed another physical activation, context or epoch",
    )?;
    if matches!(
        &kind,
        ExprKind::Literal(Literal::Integer(_) | Literal::Float(_))
    ) {
        crate::sema::numeric_selection::validate_literal_in_query(
            facts,
            record.id,
            &replay.numeric_session,
            &replay.source_query,
            work,
        )
        .map_err(|error| format!("pattern numeric Source lost its actual selection: {error}"))?;
    }
    // This is a view of existing generated HIR. Ordinary source replay still
    // authenticates names/paths and their declaration; the recipe grants none.
    Ok(Expr {
        hir_id: Some(source),
        kind,
        span: expression.info.span,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    fn fixture(case: &str) -> SemanticFacts {
        crate::Session::new(ril_test::case_bytes(case).to_vec())
            .verify()
            .unwrap()
            .facts()
            .clone()
    }

    fn reads(facts: &SemanticFacts) -> Vec<(usize, ExprId)> {
        let hir = facts.semantic_hir.as_deref().unwrap();
        facts
            .expressions
            .iter()
            .enumerate()
            .filter_map(|(observation, fact)| {
                let source = fact.source_id?;
                let original = hir.expression(source)?;
                (matches!(
                    original.info.origin,
                    hir::NodeOrigin::Generated {
                        kind: hir::GeneratedKind::PatternValue,
                        ..
                    }
                ) && matches!(original.kind, hir::ExprKind::Literal(_)))
                .then_some((observation, source))
            })
            .collect()
    }

    #[test]
    fn generated_pattern_literals_supply_source_only_at_their_actual_occurrence() {
        for case in [
            "tests/regressions/closed-standard-data.ril::closed-constructors",
            "tests/regressions/catalog-types.ril::nested-constructor-patterns",
        ] {
            let facts = fixture(case);
            let sources = OriginalOperandSources::new(&facts).unwrap();
            let reads = reads(&facts);
            assert!(!reads.is_empty(), "{case}");
            for (observation, source) in reads {
                assert!(!sources.sites.expressions.contains_key(&source));
                let (schema, _) = sources
                    .observed_with_work(source, observation, &mut 65536)
                    .unwrap();
                assert!(schema.is_some(), "{case}: {source:?}");
                for mutation in 0..4 {
                    let mut changed = facts.clone();
                    match mutation {
                        0 => changed.evaluations[observation].identity = None,
                        1 => changed.evaluations[observation].allocation_epoch += 1,
                        2 => {
                            let id = changed.evaluations[observation]
                                .identity
                                .unwrap()
                                .activation;
                            changed.activations[id.0 as usize].result = None;
                        }
                        _ => changed.expressions[observation].source_id = None,
                    }
                    assert!(
                        OriginalOperandSources::new(&changed)
                            .and_then(|sources| sources.observed_with_work(
                                source,
                                observation,
                                &mut 65536
                            ))
                            .is_err(),
                        "{case}: mutation {mutation}"
                    );
                }
            }
        }
    }

    #[test]
    fn generated_pattern_literal_recipe_rejects_other_text_anchor_and_numeric_receipt_loss() {
        let facts = fixture("tests/regressions/closed-standard-data.ril::closed-constructors");
        let (observation, source) = reads(&facts)
            .into_iter()
            .find(|(_, source)| {
                matches!(
                    facts
                        .semantic_hir
                        .as_deref()
                        .unwrap()
                        .expression(*source)
                        .unwrap()
                        .kind,
                    hir::ExprKind::Literal(Literal::Integer(_))
                )
            })
            .unwrap();
        let generated = facts
            .semantic_hir
            .as_deref()
            .unwrap()
            .expression(source)
            .unwrap();
        let hir::NodeOrigin::Generated { anchor, .. } = generated.info.origin else {
            unreachable!()
        };
        let mut changed = facts.clone();
        changed.numeric_holes.clear();
        changed.numeric_uses.clear();
        changed.numeric_selections.clear();
        assert!(
            OriginalOperandSources::new(&changed)
                .and_then(|sources| sources.observed_with_work(source, observation, &mut 65536))
                .is_err()
        );
        for wrong_anchor in [anchor, hir::NodeId::Expr(source)] {
            let mut changed = facts.clone();
            let replacement = Expr {
                hir_id: None,
                span: generated.info.span,
                kind: ExprKind::Literal(Literal::Bytes("b\"different\"".into())),
            };
            let wrong = Arc::make_mut(changed.semantic_hir.as_mut().unwrap())
                .mint_generated_expr(
                    &replacement,
                    wrong_anchor,
                    hir::GeneratedKind::PatternValue,
                    generated.info.owner,
                    hir::HirLimits::default(),
                )
                .unwrap();
            let activation = changed.evaluations[observation].identity.as_mut().unwrap();
            activation.source = wrong;
            changed.activations[activation.activation.0 as usize].source = Some(wrong);
            changed.expressions[observation].source_id = Some(wrong);
            assert!(
                OriginalOperandSources::new(&changed)
                    .and_then(|sources| sources.observed_with_work(wrong, observation, &mut 65536))
                    .is_err()
            );
        }
    }

    #[test]
    fn generated_pattern_literal_admission_prepays_text_and_uses_exact_work() {
        let facts = fixture("tests/regressions/closed-standard-data.ril::closed-constructors");
        let (observation, source) = reads(&facts)
            .into_iter()
            .find(|(_, source)| {
                matches!(
                    facts
                        .semantic_hir
                        .as_deref()
                        .unwrap()
                        .expression(*source)
                        .unwrap()
                        .kind,
                    hir::ExprKind::Literal(Literal::Bytes(_))
                )
            })
            .unwrap();
        let replay = Replay::new(&facts).unwrap();
        let mut work = 65536;
        let expected = expression(&replay, source, observation, &mut work).unwrap();
        let cost = 65536 - work;
        let mut exact = cost;
        assert_eq!(
            expression(&replay, source, observation, &mut exact).unwrap(),
            expected
        );
        assert_eq!(exact, 0);
        for short in [0, cost - 1] {
            assert!(expression(&replay, source, observation, &mut { short }).is_err());
        }
        let sources = OriginalOperandSources::new(&facts).unwrap();
        assert!(
            sources
                .observed_with_work(source, observation, &mut 0)
                .is_err()
        );
    }

    #[test]
    fn generated_pattern_paths_keep_their_original_recipe_and_work() {
        let facts = fixture("tests/regressions/catalog-types.ril::catalog-constant-patterns");
        let hir = facts.semantic_hir.as_deref().unwrap();
        let mut count = 0;
        for (observation, fact) in facts.expressions.iter().enumerate() {
            let Some(source) = fact.source_id else {
                continue;
            };
            let original = hir.expression(source).unwrap();
            let hir::NodeOrigin::Generated {
                anchor,
                kind: hir::GeneratedKind::PatternValue,
                ..
            } = original.info.origin
            else {
                continue;
            };
            if !matches!(original.kind, hir::ExprKind::Path(_)) {
                continue;
            }
            count += 1;
            let replay = Replay::new(&facts).unwrap();
            let mut work = 65536;
            let expected = expression(&replay, source, observation, &mut work).unwrap();
            let cost = 65536 - work;
            let mut exact = cost;
            assert_eq!(
                expression(&replay, source, observation, &mut exact).unwrap(),
                expected
            );
            assert_eq!(exact, 0);
            assert!(expression(&replay, source, observation, &mut { cost - 1 }).is_err());

            let mut changed = facts.clone();
            let wrong = Arc::make_mut(changed.semantic_hir.as_mut().unwrap())
                .mint_generated_expr(
                    &Expr {
                        hir_id: None,
                        kind: ExprKind::Path(vec![
                            "Num".into(),
                            "NumError".into(),
                            "InvalidRadix".into(),
                        ]),
                        span: original.info.span,
                    },
                    anchor,
                    hir::GeneratedKind::PatternValue,
                    original.info.owner,
                    hir::HirLimits::default(),
                )
                .unwrap();
            let identity = changed.evaluations[observation].identity.as_mut().unwrap();
            identity.source = wrong;
            changed.activations[identity.activation.0 as usize].source = Some(wrong);
            changed.expressions[observation].source_id = Some(wrong);
            assert!(
                Replay::new(&changed)
                    .and_then(|replay| expression(&replay, wrong, observation, &mut 65536))
                    .is_err()
            );
        }
        assert!(count > 0, "generated path coverage");
    }
}
