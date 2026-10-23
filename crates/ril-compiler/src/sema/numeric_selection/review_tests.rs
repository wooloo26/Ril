//! Numeric receipts must explain the original physical evaluation, even when
//! another literal has the same value or all producer coordinates are changed.
use super::*;
use crate::{CheckOptions, Session, sema::SemanticFacts};

fn checked(case: &str, target: &str) -> SemanticFacts {
    let fixture = ril_test::case_by_id(case);
    let options = CheckOptions {
        target: target.into(),
        ..CheckOptions::default()
    };
    let session = if fixture.files.len() == 1 {
        Session::with_options(ril_test::case_bytes(case).to_vec(), options)
    } else {
        let directory = std::path::Path::new("numeric-review");
        Session::with_project(
            directory.join(&fixture.root),
            fixture
                .files
                .iter()
                .map(|file| crate::session::ProjectSource {
                    path: directory.join(&file.name),
                    bytes: file.bytes.clone(),
                })
                .collect(),
            options,
        )
        .unwrap_or_else(|failure| panic!("{case} project: {failure:?}"))
    };
    let program = session
        .verify()
        .unwrap_or_else(|failure| panic!("{case} on {target}: {failure:?}"));
    let facts = program.facts().clone();
    assert_eq!(validate(&facts, &mut 4_000_000), Ok(()));
    facts
}

fn rejects(facts: &SemanticFacts, change: &str) {
    assert!(
        validate(facts, &mut 4_000_000).is_err(),
        "numeric replay accepted {change}"
    );
}

#[test]
fn equal_sibling_literals_cannot_exchange_physical_numeric_receipts() {
    for target in ["pointer32", "pointer64"] {
        let baseline = checked(
            "tests/conformance/numeric.ril::sibling-literal-occurrences",
            target,
        );
        let (first, sibling) = baseline
            .numeric_uses
            .iter()
            .enumerate()
            .find_map(|(index, first)| {
                baseline.numeric_uses[index + 1..]
                    .iter()
                    .find(|second| first.site != second.site && first.exact == second.exact)
                    .map(|second| (first, second))
            })
            .expect("two different literal HIR nodes with identical exact values");
        let mut changed = baseline.clone();
        let selection = changed
            .numeric_selections
            .iter_mut()
            .find(|selection| selection.literal == first.id)
            .unwrap();
        selection.literal = sibling.id;
        selection.site = sibling.site;
        selection.birth = sibling.birth;
        rejects(&changed, "an equal sibling's calibrated selection");

        let mut changed = baseline.clone();
        changed.numeric_uses.clear();
        changed.numeric_holes.clear();
        changed.numeric_selections.clear();
        rejects(&changed, "all numeric arenas erased together");

        let mut changed = baseline.clone();
        changed.numeric_uses.clear();
        changed.numeric_holes.clear();
        changed.numeric_selections.clear();
        for fact in &mut changed.expressions {
            fact.value.corrupt_value(&mut 4_000_000).unwrap().numeric =
                NumericDependencies::default();
        }
        rejects(
            &changed,
            "all numeric arenas and selected expression dependencies erased together",
        );

        fn erase(value: &mut Value) {
            value.numeric = NumericDependencies::default();
            for child in [
                &mut value.option_payload,
                &mut value.result_payload,
                &mut value.result_success,
                &mut value.result_error,
                &mut value.variant_payload,
            ]
            .into_iter()
            .flatten()
            .chain(value.variant_witnesses.values_mut())
            {
                erase(child);
            }
        }
        let mut changed = baseline.clone();
        for usage in &baseline.numeric_uses {
            let activation = &mut changed.activations[usage.birth.occurrence.activation.0 as usize];
            assert_eq!(
                activation.kind,
                crate::sema::application_effect::ActivationKind::Expression
            );
            assert_eq!(
                activation.start_expression,
                activation.result.unwrap().0 as usize
            );
            activation.kind = crate::sema::application_effect::ActivationKind::Emission;
        }
        changed.numeric_uses.clear();
        changed.numeric_holes.clear();
        changed.numeric_selections.clear();
        for fact in &mut changed.expressions {
            erase(fact.value.corrupt_value(&mut 4_000_000).unwrap());
        }
        rejects(
            &changed,
            "all numeric evidence erased and real literal activations relabeled as emissions",
        );
    }
}

#[test]
fn repeated_defaults_cannot_reassign_a_hole_to_another_actual_activation() {
    for target in ["pointer32", "pointer64"] {
        let baseline = checked(
            "tests/conformance/numeric.ril::default-literal-occurrences",
            target,
        );
        let (first, later) = baseline
            .numeric_uses
            .iter()
            .enumerate()
            .find_map(|(index, first)| {
                baseline.numeric_uses[index + 1..]
                    .iter()
                    .find(|second| {
                        first.site == second.site
                            && first.birth.occurrence != second.birth.occurrence
                    })
                    .map(|second| (first, second))
            })
            .expect("one default literal evaluated in distinct activations");
        let mut changed = baseline.clone();
        changed.numeric_uses[first.id.0 as usize].birth = later.birth;
        changed.numeric_holes[first.hole.0 as usize].birth = later.birth;
        for selection in &mut changed.numeric_selections {
            if selection.literal == first.id {
                selection.birth = later.birth;
            }
        }
        rejects(&changed, "joint hole/use/selection birth replacement");
    }
}

#[test]
fn a_numeric_term_must_use_its_real_hir_operator_and_child_evaluations() {
    for target in ["pointer32", "pointer64"] {
        let baseline = checked(
            "tests/conformance/numeric.ril::deferred-arithmetic-safe",
            target,
        );
        let binary = baseline
            .numeric_holes
            .iter()
            .position(|hole| matches!(hole.term, NumericTerm::Binary { .. }))
            .expect("deferred binary arithmetic");
        let mut changed = baseline.clone();
        let NumericTerm::Binary { operator, .. } = &mut changed.numeric_holes[binary].term else {
            unreachable!()
        };
        *operator = "-".into();
        rejects(&changed, "another valid arithmetic operator");

        let mut changed = baseline.clone();
        let NumericTerm::Binary { left, right, .. } = &mut changed.numeric_holes[binary].term
        else {
            unreachable!()
        };
        *left = right.clone();
        rejects(
            &changed,
            "a calibrated sibling operand and all its projections",
        );
    }
}

#[test]
fn exact_encoding_layout_and_complete_resolution_are_independently_required() {
    let baseline = checked(
        "tests/conformance/numeric.ril::deferred-arithmetic-safe",
        "pointer32",
    );
    assert!(!baseline.numeric_selections.is_empty());
    let mut changed = baseline.clone();
    changed.numeric_selections[0].layout = TargetLayout::POINTER64;
    rejects(&changed, "a foreign target layout with unchanged spelling");

    let mut changed = baseline.clone();
    let selection = &mut changed.numeric_selections[0];
    selection.encoded = ExactLiteral::integer(
        "0",
        false,
        crate::numeric_literals::ParseLimit { max_bytes: 32 },
    )
    .unwrap()
    .select(selection.ty, selection.layout)
    .unwrap();
    rejects(
        &changed,
        "another valid encoding of the selected number type",
    );

    let mut changed = baseline.clone();
    changed.numeric_holes[0].state = NumericHoleState::Pending;
    rejects(&changed, "a removed committed resolution");

    assert!(matches!(
        validate(&baseline, &mut 0),
        Err(SourceTypesError::BudgetExceeded)
    ));
}

#[test]
fn selected_values_do_not_rewrite_the_historical_hole_or_its_other_metadata() {
    for target in ["pointer32", "pointer64"] {
        let baseline = checked(
            "tests/conformance/numeric.ril::deferred-arithmetic-safe",
            target,
        );
        let mut count = 0;
        for (ordinal, fact) in baseline.expressions.iter().enumerate() {
            let Ty::NumericHole(expected) = fact.value.ty else {
                continue;
            };
            count += 1;
            let (hole, resolution) = checked_resolution_at(
                &baseline,
                EvaluationOccurrenceId(ordinal as u32),
                &mut 4_000_000,
            )
            .unwrap()
            .expect("a complete actual hole resolution");
            assert_eq!(hole, expected);
            let mut selected = crate::sema::evaluated::transport_value_at(
                &fact.value,
                &baseline.allocation_history,
                fact.allocation_epoch,
                fact.allocation_epoch,
                &mut 4_000_000,
            )
            .unwrap();
            resolution.apply(&mut selected, &mut 4_000_000).unwrap();
            assert_eq!(selected.ty, resolution.value_type());
            assert_eq!(selected.constant, resolution.constant);
            selected.ty = fact.value.ty.clone();
            selected.constant = fact.value.constant.clone();
            selected.numeric = fact.value.numeric.clone();
            selected.unsuffixed_numeric = fact.value.unsuffixed_numeric;
            assert_eq!(
                crate::sema::evaluated::same_birth_value(&selected, &fact.value, &mut 4_000_000,),
                Ok(true)
            );
            assert_eq!(fact.value.ty, Ty::NumericHole(expected));
        }
        assert!(
            count > 0,
            "the original deferred emissions must remain inspectable"
        );
    }
}

#[test]
fn numeric_pattern_receipts_retain_their_original_pattern_id() {
    for target in ["pointer32", "pointer64"] {
        let baseline = checked(
            "tests/conformance/numeric.ril::pattern-literal-occurrences",
            target,
        );
        let first = baseline
            .numeric_uses
            .iter()
            .find(|usage| matches!(usage.site, NumericSite::Pattern(_)))
            .expect("an actual numeric pattern receipt");
        let other = baseline
            .numeric_uses
            .iter()
            .find(|usage| matches!(usage.site, NumericSite::Pattern(_)) && usage.site != first.site)
            .expect("a different original numeric pattern");
        let mut changed = baseline.clone();
        changed.numeric_uses[first.id.0 as usize].site = other.site;
        for selection in &mut changed.numeric_selections {
            if selection.literal == first.id {
                selection.site = other.site;
            }
        }
        rejects(
            &changed,
            "joint use/selection retargeting to another pattern",
        );
    }
}

#[test]
fn an_alias_pattern_cannot_reselect_its_type_by_calibrating_all_numeric_projections() {
    for target in ["pointer32", "pointer64"] {
        for (case, foreign_type) in [
            (
                "tests/conformance/numeric.ril::floating-alias-patterns",
                NumberType::F64,
            ),
            (
                "tests/conformance/numeric.ril::nested-alias-patterns",
                NumberType::I16,
            ),
            (
                "tests/conformance/numeric.ril::alias-pattern-range-safe",
                NumberType::I16,
            ),
            (
                "tests/conformance/numeric.ril::shadowed-alias-pattern-safe",
                NumberType::I16,
            ),
        ] {
            let baseline = checked(case, target);
            let usage = baseline
                .numeric_uses
                .iter()
                .find(|usage| matches!(usage.site, NumericSite::Pattern(_)))
                .unwrap();
            let selection_id = usage.selection.unwrap();
            let mut changed = baseline.clone();
            let selection = &mut changed.numeric_selections[selection_id.0 as usize];
            selection.ty = foreign_type;
            selection.encoded = usage.exact.select(foreign_type, selection.layout).unwrap();
            let NumericHoleState::Committed { resolution, .. } =
                &mut changed.numeric_holes[usage.hole.0 as usize].state
            else {
                unreachable!()
            };
            let resolution = Arc::make_mut(resolution);
            resolution.number_type = foreign_type;
            resolution.constant = super::encoded_constant(&selection.encoded);
            resolution.encoded = Some(selection.encoded.clone());
            for (fact, record) in changed.expressions.iter_mut().zip(&changed.evaluations) {
                if record.identity == Some(usage.birth.occurrence) {
                    resolution
                        .apply(fact.value.corrupt_value(&mut 4_000_000).unwrap(), &mut 4096)
                        .unwrap();
                }
            }
            rejects(
                &changed,
                "selection, resolution and generated pattern value consistently changed to a different scalar type",
            );
        }
    }
}

#[test]
fn committed_runtime_floats_require_occurrence_receipts_and_original_width_bits() {
    for target in ["pointer32", "pointer64"] {
        let baseline = checked(
            "tests/conformance/numeric.ril::external-const-floating-defaults",
            target,
        );
        let committed: Vec<_> = baseline
            .numeric_uses
            .iter()
            .filter(|usage| usage.exact.committed_float().is_some())
            .collect();
        assert!(
            !committed.is_empty(),
            "the fixture must execute fixed static carriers"
        );
        for usage in &committed {
            let mut changed = baseline.clone();
            let selection = &mut changed.numeric_selections[usage.selection.unwrap().0 as usize];
            selection.ty = if selection.ty == NumberType::F32 {
                NumberType::F64
            } else {
                NumberType::F32
            };
            rejects(&changed, "a committed float's width changed at runtime");
            let mut changed = baseline.clone();
            let selection = &mut changed.numeric_selections[usage.selection.unwrap().0 as usize];
            selection.encoded = ExactLiteral::decimal(
                "0.0f32",
                false,
                crate::numeric_literals::ParseLimit { max_bytes: 32 },
            )
            .unwrap()
            .select(NumberType::F32, selection.layout)
            .unwrap();
            if selection.encoded
                == baseline.numeric_selections[usage.selection.unwrap().0 as usize].encoded
            {
                selection.encoded = ExactLiteral::decimal(
                    "1.0f32",
                    false,
                    crate::numeric_literals::ParseLimit { max_bytes: 32 },
                )
                .unwrap()
                .select(NumberType::F32, selection.layout)
                .unwrap();
            }
            rejects(&changed, "a committed float's raw encoding changed");
        }
        let mut changed = baseline.clone();
        for usage in &committed {
            let activation = &mut changed.activations[usage.birth.occurrence.activation.0 as usize];
            let NumericSite::Expression {
                literal,
                immediate_minus,
            } = usage.site
            else {
                panic!("SDK defaults must retain their actual expression sites");
            };
            if let Some(minus) = immediate_minus {
                assert_eq!(usage.birth.occurrence.source, minus);
                let original = baseline
                    .semantic_hir
                    .as_deref()
                    .unwrap()
                    .expression(minus)
                    .unwrap();
                assert!(
                    matches!(&original.kind, crate::hir::nodes::ExprKind::Unary { operator, operand } if operator == "-" && *operand == literal)
                );
                let mut children = baseline.activations.iter().filter(|child| {
                    child.parent == Some(activation.id)
                        && child.source == Some(literal)
                        && child.kind == crate::sema::application_effect::ActivationKind::Emission
                });
                let child = children
                    .next()
                    .expect("the real atomic-minus operand emission");
                assert!(children.next().is_none());
                assert_eq!(child.start_expression, activation.start_expression);
                assert!(child.result.unwrap().0 < activation.result.unwrap().0);
            } else {
                assert_eq!(
                    activation.start_expression,
                    activation.result.unwrap().0 as usize
                );
            }
            activation.kind = crate::sema::application_effect::ActivationKind::Emission;
        }
        changed.numeric_uses.clear();
        changed.numeric_holes.clear();
        changed.numeric_selections.clear();
        fn erase(value: &mut Value) {
            value.numeric = NumericDependencies::default();
            for child in [
                &mut value.option_payload,
                &mut value.result_payload,
                &mut value.result_success,
                &mut value.result_error,
                &mut value.variant_payload,
            ]
            .into_iter()
            .flatten()
            .chain(value.variant_witnesses.values_mut())
            {
                erase(child);
            }
        }
        for fact in &mut changed.expressions {
            erase(fact.value.corrupt_value(&mut 4_000_000).unwrap());
        }
        for usage in &committed {
            let result = baseline.activations[usage.birth.occurrence.activation.0 as usize]
                .result
                .unwrap();
            assert!(
                super::replay::validate_observation_coverage(&changed, result, &mut 4_000_000)
                    .is_err(),
                "the committed carrier's own coverage must reject erased evidence independently of ordinary literals"
            );
        }
        rejects(
            &changed,
            "committed float receipts erased and their activations relabeled",
        );
    }
}

#[test]
fn actual_unary_nan_defaults_require_the_positive_canonical_result() {
    use crate::numeric_literals::{EncodedNumber, FloatFormat, ParseLimit};
    for target in ["pointer32", "pointer64"] {
        let baseline = checked(
            "tests/conformance/numeric.ril::external-const-floating-defaults",
            target,
        );
        let mut widths = BTreeSet::new();
        for usage in baseline.numeric_uses.iter().filter(|usage| {
            usage.exact.is_negative()
                && usage
                    .exact
                    .committed_float()
                    .is_some_and(|value| value.is_nan())
        }) {
            let raw = usage.exact.committed_float().unwrap();
            let (width, canonical, invalid) = match raw.format() {
                FloatFormat::F32 => (32, 0x7fc0_0000, "\0ril.float32:ffc00001"),
                FloatFormat::F64 => (64, 0x7ff8_0000_0000_0000, "\0ril.float64:fff8000000000001"),
            };
            widths.insert(width);
            let selection = &baseline.numeric_selections[usage.selection.unwrap().0 as usize];
            let EncodedNumber::Float(encoded) = selection.encoded else {
                panic!("a NaN default requires IEEE encoding")
            };
            assert_eq!(encoded.bits(), canonical);
            let mut changed = baseline.clone();
            let invalid = ExactLiteral::decimal(invalid, false, ParseLimit { max_bytes: 64 })
                .unwrap()
                .select(selection.ty, selection.layout)
                .unwrap();
            changed.numeric_selections[selection.id.0 as usize].encoded = invalid.clone();
            let NumericHoleState::Committed { resolution, .. } =
                &mut changed.numeric_holes[usage.hole.0 as usize].state
            else {
                unreachable!()
            };
            Arc::make_mut(resolution).encoded = Some(invalid);
            rejects(
                &changed,
                "a real unary NaN default's selection and complete resolution jointly replaced by signed payload bits",
            );
        }
        assert_eq!(
            widths,
            BTreeSet::from([32, 64]),
            "both SDK unary-default paths must really execute"
        );
    }
}

#[test]
fn computed_numeric_patterns_use_the_real_application_source() {
    for target in ["pointer32", "pointer64"] {
        for case in [
            "tests/stdlib/num.ril::int-parse-format",
            "tests/stdlib/num.ril::f32-parse-format",
            "tests/stdlib/num.ril::conversion-boundaries",
            "tests/stdlib/num.ril::numeric-callable-views",
        ] {
            let baseline = checked(case, target);
            let usage = baseline
                .numeric_uses
                .iter()
                .find(|usage| matches!(usage.site, NumericSite::Pattern(_)))
                .expect("an executed numeric pattern over a computed Result");
            if case.ends_with("::int-parse-format") {
                let mut changed = baseline.clone();
                let selection =
                    &mut changed.numeric_selections[usage.selection.unwrap().0 as usize];
                selection.ty = NumberType::F64;
                selection.encoded = usage.exact.select(selection.ty, selection.layout).unwrap();
                let NumericHoleState::Committed { resolution, .. } =
                    &mut changed.numeric_holes[usage.hole.0 as usize].state
                else {
                    unreachable!()
                };
                let resolution = Arc::make_mut(resolution);
                resolution.number_type = selection.ty;
                resolution.constant = super::encoded_constant(&selection.encoded);
                resolution.encoded = Some(selection.encoded.clone());
                for (fact, record) in changed.expressions.iter_mut().zip(&changed.evaluations) {
                    if record.identity == Some(usage.birth.occurrence) {
                        resolution
                            .apply(fact.value.corrupt_value(&mut 4_000_000).unwrap(), &mut 4096)
                            .unwrap();
                    }
                }
                rejects(
                    &changed,
                    "a computed int result's whole numeric selection calibrated to float",
                );
            }
            let mut changed = baseline.clone();
            changed.copy_call_events.clear();
            rejects(
                &changed,
                "the actual computed subject's application receipts removed",
            );
            let mut changed = baseline.clone();
            let count = changed.builtin_source_observations.len();
            changed.builtin_source_observations.retain(|row| {
                !matches!(
                    row.full_header,
                    crate::sema::builtin_sources::BuiltinDeclaration::Numeric(_)
                )
            });
            assert!(
                changed.builtin_source_observations.len() < count,
                "the fixture must execute a real canonical numeric SDK reference"
            );
            if case.ends_with("::numeric-callable-views") {
                let mut work = 4_000_000;
                let sources =
                    crate::sema::record_bound_validation::OriginalOperandSources::new_with_work(
                        &changed, &mut work,
                    )
                    .unwrap();
                for (name, expected) in [("parse", false), ("explicit_parse", true)] {
                    let event = changed
                        .copy_call_events
                        .iter()
                        .find(|event| {
                            event
                                .callee_expression
                                .and_then(|index| changed.expressions.get(index))
                                .and_then(|fact| fact.value.sources.first())
                                .and_then(|id| changed.bindings.get(*id))
                                .is_some_and(|binding| binding.name == name)
                        })
                        .expect("the original fixture must call each inferred/ascribed alias");
                    let query = sources.observed_with_work(
                        event.source_id.unwrap(),
                        event.result_expression.unwrap(),
                        &mut work,
                    );
                    if expected {
                        assert!(
                            query.is_ok_and(|(source, _)| source.is_some()),
                            "an original explicit callable header determines its result without the SDK body receipt"
                        );
                    } else {
                        assert!(
                            query.is_err(),
                            "an inferred callable view must independently authenticate its actual initializer's SDK declaration"
                        );
                    }
                }
            }
            rejects(
                &changed,
                &format!(
                    "the computed subject's original numeric SDK declarations removed for {case} on {target}"
                ),
            );
            if case.ends_with("::int-parse-format") {
                let declaration = baseline
                    .builtin_source_observations
                    .iter()
                    .find(|row| row.identity == "Num::parse_int")
                    .expect("a real parse_int reference");
                for mutation in 0..4 {
                    let mut changed = baseline.clone();
                    let value = changed.expressions[declaration.expression]
                        .value
                        .corrupt_value(&mut 4_000_000)
                        .unwrap();
                    if mutation == 0 || mutation == 3 {
                        value.callables = vec![crate::sema::model::Callable::Builtin(
                            "Num::parse_f32".into(),
                        )];
                    }
                    if mutation == 1 || mutation == 3 {
                        value.signature = Some(vec![]);
                    }
                    if mutation == 2 || mutation == 3 {
                        value.ty = Ty::Float("f32".into());
                    }
                    rejects(
                        &changed,
                        "a canonical parse_int reference with replaced callable/signature/runtime type metadata",
                    );
                }
            }
        }
    }
}

#[test]
fn repeated_numeric_sdk_references_require_the_exact_child_observation() {
    use crate::sema::source_types::WorkLimit;
    use crate::sema::{builtin_sources::BuiltinDeclaration, checker};
    use ril_compiler_core::numeric_builtins::NumericBuiltin;
    for target in ["pointer32", "pointer64"] {
        let baseline = checked("tests/stdlib/num.ril::repeated-numeric-conversion", target);
        let (actual, sibling) = baseline.builtin_source_observations.iter().enumerate().find_map(|(index, actual)| {
            if actual.full_header != BuiltinDeclaration::Numeric(NumericBuiltin::Convert) { return None; }
            baseline.builtin_source_observations[index + 1..].iter().find(|sibling| {
                sibling.full_header == actual.full_header && sibling.context == actual.context
                    && sibling.expression != actual.expression && sibling.cause != actual.cause
                    && baseline.expressions[sibling.expression].source_id == baseline.expressions[actual.expression].source_id
            }).map(|sibling| (actual, sibling))
        }).expect("the original loop must really execute the same numeric callee HIR twice in one context");
        let source = baseline.expressions[actual.expression].source_id.unwrap();
        let sites = crate::sema::record_bound_validation::source_sites_base_with_work(
            &baseline,
            &mut 4_000_000,
        )
        .unwrap();
        let syntax = sites.expressions[&source];
        let names = checker::BuiltinNameIndex::new_with_work(&baseline, &mut 4_000_000).unwrap();
        let usage = checker::CanonicalBuiltinUse {
            value: &baseline.expressions[actual.expression].value,
            actual: syntax,
            context: actual.context,
            observation: actual.expression,
        };
        assert_eq!(
            checker::original_numeric_builtin_declaration(
                &baseline,
                &usage,
                &names,
                &mut WorkLimit::new(4096)
            )
            .unwrap(),
            Some(NumericBuiltin::Convert)
        );
        for joint in [false, true] {
            let mut changed = baseline.clone();
            changed
                .builtin_source_observations
                .retain(|row| row.expression != actual.expression);
            if joint {
                changed.expressions[actual.expression].value =
                    baseline.expressions[sibling.expression].value.clone();
            }
            let names = checker::BuiltinNameIndex::new_with_work(&changed, &mut 4_000_000).unwrap();
            let usage = checker::CanonicalBuiltinUse {
                value: &changed.expressions[actual.expression].value,
                actual: syntax,
                context: actual.context,
                observation: actual.expression,
            };
            assert!(
                checker::original_numeric_builtin_declaration(
                    &changed,
                    &usage,
                    &names,
                    &mut WorkLimit::new(4096)
                )
                .is_err(),
                "a removed actual builtin receipt must not borrow its same-HIR sibling after cause/value calibration (joint={joint})"
            );
        }
        let changed = baseline.clone();
        assert!(
            checker::original_numeric_builtin_declaration(
                &changed,
                &usage,
                &names,
                &mut WorkLimit::new(4096)
            )
            .is_err(),
            "a lexical index from another facts snapshot cannot certify the new snapshot"
        );
    }
}

#[test]
fn repeated_queries_reuse_the_occurrence_index_without_reusing_validation_results() {
    let baseline = checked(
        "tests/conformance/numeric.ril::deferred-arithmetic-safe",
        "pointer32",
    );
    let observation = baseline
        .expressions
        .iter()
        .position(|fact| matches!(fact.value.ty, Ty::NumericHole(_)))
        .unwrap();
    let session = std::cell::RefCell::new(NumericReplaySession::default());
    let mut first = 4_000_000;
    assert!(
        super::checked_resolution_in_session(
            &baseline,
            EvaluationOccurrenceId(observation as u32),
            &session,
            &mut first
        )
        .unwrap()
        .is_some()
    );
    let mut second = 4_000_000;
    assert!(
        super::checked_resolution_in_session(
            &baseline,
            EvaluationOccurrenceId(observation as u32),
            &session,
            &mut second
        )
        .unwrap()
        .is_some()
    );
    assert!(
        second > first,
        "the second query must not rebuild complete arena indexes"
    );
    let mut changed = baseline.clone();
    let Ty::NumericHole(hole) = changed.expressions[observation].value.ty else {
        unreachable!()
    };
    let NumericHoleState::Committed { resolution, .. } =
        &mut changed.numeric_holes[hole.0 as usize].state
    else {
        unreachable!()
    };
    let resolution = Arc::make_mut(resolution);
    resolution.constant = Some(Constant::Integer(
        if resolution.constant == Some(Constant::Integer(0)) {
            1
        } else {
            0
        },
    ));
    assert!(
        super::checked_resolution_in_session(
            &changed,
            EvaluationOccurrenceId(observation as u32),
            &session,
            &mut 4_000_000
        )
        .is_err(),
        "an earlier successful query must not authorize a changed resolution"
    );
    assert!(
        super::checked_resolution_in_session(
            &baseline,
            EvaluationOccurrenceId(observation as u32),
            &session,
            &mut 0
        )
        .is_err()
    );
}
