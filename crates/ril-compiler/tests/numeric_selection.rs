use ril_compiler::{CheckOptions, CompilationOutcome, Session};
use ril_compiler_core::target::TargetLayout;
use ril_ir::core::{ExprKind, Literal, Statement};

#[test]
fn receiving_annotations_select_exact_literals_before_range_checks_and_core_encoding() {
    for (source, check) in [
        ("let value:f32=16777217", 0),
        ("let value:f64=1", 1),
        ("let value:u64=18446744073709551615", 2),
        (
            "let value:bigint=340282366920938463463374607431768211456",
            3,
        ),
        ("let value:f32=-0", 4),
        ("let value:f32=-16777217", 5),
        ("let value:f32=0X80000080000000000000000000000001", 6),
    ] {
        for (name, layout) in [
            ("pointer32", TargetLayout::POINTER32),
            ("pointer64", TargetLayout::POINTER64),
        ] {
            let program = Session::with_options(
                format!("fn example(){{{source}}}").into_bytes(),
                CheckOptions {
                    target: name.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap();
            assert!(!program.facts().numeric_selections.is_empty());
            assert!(program.facts().expressions.iter().all(|fact| !matches!(
                fact.value.ty,
                ril_compiler::sema::model::Ty::NumericHole(_)
            )));
            let core = ril_compiler::lower::lower_core_for(&program, layout).unwrap();
            let Statement::Bind { value, .. } = &core.functions[0].body.statements[0] else {
                panic!()
            };
            match (&value.kind, check) {
                (ExprKind::Literal(Literal::Float { value, bits: 32 }), 0) => {
                    assert_eq!(*value, 16_777_216.0)
                }
                (ExprKind::Literal(Literal::Float { value, bits: 64 }), 1) => {
                    assert_eq!(*value, 1.0)
                }
                (
                    ExprKind::Literal(Literal::Integer {
                        value,
                        bits: 64,
                        signed: false,
                    }),
                    2,
                ) => assert_eq!(*value, 18_446_744_073_709_551_615),
                (ExprKind::Literal(Literal::BigInteger(value)), 3) => {
                    assert_eq!(value, "340282366920938463463374607431768211456")
                }
                (ExprKind::Literal(Literal::Float { value, bits: 32 }), 4) => {
                    assert_eq!((*value as f32).to_bits(), 0x8000_0000)
                }
                (ExprKind::Literal(Literal::Float { value, bits: 32 }), 5) => {
                    assert_eq!(*value, -16_777_216.0)
                }
                (ExprKind::Literal(Literal::Float { value, bits: 32 }), 6) => {
                    assert_eq!((*value as f32).to_bits(), 0x7f00_0001)
                }
                _ => panic!("wrong Core representation for {source}: {value:?}"),
            }
        }
    }
}

#[test]
fn deferred_numeric_history_reaches_core_without_rewriting_its_original_observations() {
    use ril_compiler::sema::{model::Ty, numeric_selection::NumericHoleState};
    for (target, layout) in [
        ("pointer32", TargetLayout::POINTER32),
        ("pointer64", TargetLayout::POINTER64),
    ] {
        let program = Session::with_options(
            ril_test::case_bytes("tests/conformance/numeric.ril::deferred-arithmetic-safe")
                .to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap();
        let original: Vec<_> = program
            .facts()
            .expressions
            .iter()
            .enumerate()
            .filter_map(|(index, fact)| match fact.value.ty {
                Ty::NumericHole(id) => Some((index, id)),
                _ => None,
            })
            .collect();
        assert!(
            !original.is_empty(),
            "the deferred producer must remain observable"
        );
        for (_, id) in &original {
            assert!(matches!(
                &program.facts().numeric_holes[id.0 as usize].state,
                NumericHoleState::Committed { .. }
            ));
        }
        let core = ril_compiler::lower::lower_core_for(&program, layout).unwrap();
        for (index, id) in original {
            assert_eq!(
                program.facts().expressions[index].value.ty,
                Ty::NumericHole(id)
            );
        }
        let entry = core
            .functions
            .iter()
            .find(|function| function.name == "test_deferred_arithmetic_safe")
            .unwrap();
        let value = entry
            .body
            .statements
            .iter()
            .find_map(|statement| match statement {
                Statement::Bind {
                    pattern: ril_ir::core::Pattern::Name(name),
                    value,
                    ..
                } if name == "result" => Some(value),
                _ => None,
            })
            .expect("the actual numeric receiving binding");
        let ExprKind::Call { arguments, .. } = &value.kind else {
            panic!("missing original choose call: {value:?}")
        };
        let ExprKind::Binary { left, right, .. } = &arguments[0].value.kind else {
            panic!("missing deferred binary operation: {:?}", arguments[0])
        };
        for value in [left, right] {
            assert!(matches!(
                value.kind,
                ExprKind::Literal(Literal::Integer {
                    bits: 8,
                    signed: true,
                    ..
                })
            ));
        }
    }
}

#[test]
fn selection_cannot_change_suffixes_stored_values_or_unsigned_sign_rules() {
    for (source, code) in [
        ("let value:f32=1int", "E0301"),
        ("let first=1;let value:f32=first", "E0301"),
        ("let value:bigint=1u64", "E0301"),
        ("let value:f32=-0.0f64", "E0301"),
        ("let value:u64=-1", "E0326"),
        ("let value:i8=128", "E0326"),
    ] {
        let result = Session::new(format!("fn example(){{{source}}}").into_bytes()).check();
        assert!(
            matches!(&result,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code==code)),
            "{source}: {result:?}"
        );
    }
}

#[test]
fn expected_types_reach_fresh_aggregate_members_and_declared_results() {
    let source = r#"
fn answer()->f32{16777217}
fn early()->u64{return 18446744073709551615}
fn choose(flag:bool)->f32{if flag{16777217}else{ -16777217}}
fn example(){
    let array:[]f32=[16777217,1]
    let tuple:(f32,u64)=(16777217,18446744073709551615)
    let map:[int:f32]=[0:16777217]
    let record:{value:f32}=.{value:16777217}
    let block:f32={let untouched=1;16777217}
    assert(answer()==16777216.0f32 && early()==18446744073709551615u64)
    assert(choose(true)==16777216.0f32 && choose(false)==-16777216.0f32)
}
"#;
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    ril_compiler::lower::lower_core(&program).unwrap();
}
