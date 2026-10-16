use ril_compiler::{CheckOptions, CompilationOutcome, Session};
use std::num::NonZeroU64;

fn check(source: &str, budget: u64) -> CompilationOutcome {
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            static_budget: NonZeroU64::new(budget).unwrap(),
            ..Default::default()
        },
    )
    .check()
}
fn accepts(source: &str, budget: u64) {
    let result = check(source, budget);
    assert!(
        matches!(result, CompilationOutcome::Accepted { .. }),
        "{source}\n{result:?}"
    );
}
fn rejects(source: &str, code: &str) {
    let result = check(source, 100);
    assert!(
        matches!(&result,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code==code)),
        "{source}\n{result:?}"
    );
}

#[test]
fn binding_literals_are_selected_before_host_range_checks() {
    accepts(
        "meta let N:f32=18014399583223809\nmeta let _=assert(N==18014400656965632.0f32)",
        1,
    );
    accepts(
        "meta let N:f32=170141193601674033557522515689509748737\nmeta let _=assert(N==170141203742878835383357727663135391744.0f32)",
        1,
    );
    accepts(
        "meta let N:u64=18446744073709551615\nmeta let _=assert(N==18446744073709551615u64)",
        1,
    );
    accepts(
        "meta let N:bigint=340282366920938463463374607431768211456\nmeta let _=assert(N==340282366920938463463374607431768211456bigint)",
        1,
    );
    accepts(
        "meta let N:f64=340282366920938463463374607431768211456\nmeta let _=assert(N==340282366920938463463374607431768211456.0f64)",
        1,
    );
}

#[test]
fn signature_parameters_defaults_and_results_select_before_evaluation() {
    accepts(
        "meta fn value()->f32{16777217}\nmeta let _=assert(value()==16777216.0f32)",
        1,
    );
    accepts(
        "meta fn value()->f32{return 16777217}\nmeta let _=assert(value()==16777216.0f32)",
        1,
    );
    accepts(
        "meta fn value(input:f32=16777217)->f32{input}\nmeta let _=assert(value()==16777216.0f32)\nmeta let _=assert(value(input:16777219)==16777220.0f32)",
        1,
    );
    accepts(
        "meta fn value(first:u64,second:f32)->(u64,f32){(first,second)}\nmeta let N=value(second:16777217,first:18446744073709551615)\nmeta let _=assert(N==(18446744073709551615u64,16777216.0f32))",
        1,
    );
}

#[test]
fn fresh_aggregate_and_branch_leaves_inherit_their_actual_context() {
    accepts(
        "meta let N:[]f32=[16777217,-16777217]\nmeta let _=assert(N==[16777216.0f32,-16777216.0f32])",
        1,
    );
    accepts(
        "meta let N:(u64,f32)=(18446744073709551615,16777217)\nmeta let _=assert(N==(18446744073709551615u64,16777216.0f32))",
        1,
    );
    accepts(
        "type R={first:u64,second:f32}\nmeta let N=R.{first:18446744073709551615,second:16777217}\nmeta let _=assert(N.first==18446744073709551615u64 && N.second==16777216.0f32)",
        1,
    );
    accepts(
        "meta fn value(flag:bool)->f32{if flag{16777217}else{16777219}}\nmeta let _=assert(value(true)==16777216.0f32 && value(false)==16777220.0f32)",
        2,
    );
}

#[test]
fn rigid_peers_constrain_literals_without_retyping_committed_values() {
    accepts(
        "meta fn value()->f32{let stored=16777216.0f32;stored+1}\nmeta let _=assert(value()==16777216.0f32)",
        1,
    );
    accepts(
        "meta let N:f32=16777217+1\nmeta let _=assert(N==16777216.0f32)",
        1,
    );
    for source in [
        "meta let N:f32=1int",
        "meta let OLD=1\nmeta let N:f32=OLD",
        "meta fn value()->f32{let old=1;old}\nmeta let N=value()",
        "meta fn value(input:f32)->f32{input}\nmeta let OLD=1\nmeta let N=value(OLD)",
        "meta let OLD=[1]\nmeta let N:[]f32=OLD",
    ] {
        rejects(source, "E0301");
    }
}

#[test]
fn suffix_ranges_and_negative_zero_keep_the_selected_width() {
    accepts("meta let N:f32=-0\nmeta let _=assert(1.0f32/N < 0.0f32)", 1);
    accepts("meta let N:i8=-128\nmeta let _=assert(N == -128i8)", 1);
    rejects("meta let N:i8=128", "E0326");
    rejects("meta let N:u64=-1", "E0326");
    rejects("meta let N=18446744073709551615", "E0326");
    rejects("meta let N:f32=1.0f64", "E0301");
}

#[test]
fn constant_graphs_keep_selected_ieee_bits_and_integer_widths() {
    use ril_ir::{constants::ConstNodeKind, core::Literal};
    let source = "meta let ROOT:(f32,f32,f32,f64,u64,bigint)=(18014399583223809,170141193601674033557522515689509748737,-0,340282366920938463463374607431768211456,18446744073709551615,340282366920938463463374607431768211456)";
    for target in ["pointer32", "pointer64"] {
        let verified = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap();
        let core = ril_compiler::lower::lower_core(&verified).unwrap();
        let literals = core
            .constant_graphs
            .iter()
            .flat_map(|graph| &graph.nodes)
            .filter_map(|node| {
                if let ConstNodeKind::Literal(literal) = &node.kind {
                    Some(literal)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        let floats = literals
            .iter()
            .filter_map(|literal| {
                if let Literal::Float { value, bits } = literal {
                    Some((
                        *bits,
                        if *bits == 32 {
                            u64::from((*value as f32).to_bits())
                        } else {
                            value.to_bits()
                        },
                    ))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        assert_eq!(
            floats,
            vec![
                (32, 0x5a800001),
                (32, 0x7f000001),
                (32, 0x80000000),
                (64, 0x47f0000000000000)
            ]
        );
        assert!(literals.iter().any(|literal| matches!(
            literal,
            Literal::Integer {
                value: 18446744073709551615,
                bits: 64,
                signed: false
            }
        )));
        assert!(literals.iter().any(|literal|matches!(literal,Literal::BigInteger(value)if value=="340282366920938463463374607431768211456")));
    }
}

#[test]
fn target_int_defaulting_is_independent_of_host_integer_width() {
    for (target, accepted) in [("pointer32", false), ("pointer64", true)] {
        let result = Session::with_options(
            b"meta let N=2147483648".to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .check();
        assert_eq!(
            matches!(result, CompilationOutcome::Accepted { .. }),
            accepted,
            "{result:?}"
        );
        if !accepted {
            assert!(
                matches!(result,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0326"))
            );
        }
        let result = Session::with_options(
            b"meta let N:u64=18446744073709551615".to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .check();
        assert!(
            matches!(result, CompilationOutcome::Accepted { .. }),
            "{result:?}"
        );
    }
}

#[test]
fn annotations_have_real_roots_and_nested_annotations_do_not_refill() {
    let source = "meta fn shape()->[2]int{[1,2]}\nmeta fn initialize()->[2]f32{[16777217,16777219]}\nmeta let N:[len(shape())]f32=initialize()\nmeta let _=assert(N==[16777216.0f32,16777220.0f32])";
    accepts(source, 1);
    let source = "meta fn shape()->[2]int{[1,2]}\nmeta fn initialize()->[2]f32{[16777217,16777219]}\nmeta fn run()->f32{let values:[len(shape())]f32=initialize();values[0]}\nmeta let N=run()";
    let result = check(source, 2);
    assert!(
        matches!(result,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0811"))
    );
    accepts(source, 3);
    rejects(
        "meta fn shape()->[2]int{assert(false);[1,2]}\nmeta let N:[len(shape())]f32={let failed=1/0;[1,2]}",
        "E0830",
    );
}

#[test]
fn generic_late_context_is_incomplete_and_never_retypes_a_completed_call() {
    let source = "meta fn identity<T>(value:T)->T{value}\nmeta let N:f32=identity(16777217)";
    assert!(matches!(
        check(source, 100),
        CompilationOutcome::NotImplemented { .. }
    ));
    rejects(
        "meta fn identity<T>(value:T)->T{value}\nmeta let OLD=identity(1)\nmeta let N:f32=OLD",
        "E0301",
    );
    rejects(
        "meta fn identity<T>(value:T)->T{value}\nmeta let N:f32=identity(1int)",
        "E0301",
    );
    rejects(
        "meta fn identity<T>(value:T)->T{value}\nmeta let OLD=1\nmeta let N:f32=identity(OLD)",
        "E0301",
    );
}

#[test]
fn aliases_callable_views_and_captured_bindings_keep_selected_types() {
    accepts(
        "type Wide=u64\nmeta fn take(value:Wide)->Wide{value}\nmeta let _=assert(take(18446744073709551615)==18446744073709551615u64)",
        1,
    );
    accepts(
        "meta fn run()->f32{let value:f32=16777217;helper() where meta fn helper()->f32{value}}\nmeta let _=assert(run()==16777216.0f32)",
        2,
    );
    accepts(
        "meta fn take(value:f32)->f32{value}\nmeta let RENAMED:fn(other:f32)->f32=take\nmeta let _=assert(RENAMED(other:16777217)==16777216.0f32)",
        1,
    );
    accepts(
        "meta let _=assert((\\value:f32->value)(16777217)==16777216.0f32)",
        1,
    );
    accepts(
        "meta fn run()->f32{let stored=1.0f32;let result=(stored+16777217)+1;result}\nmeta let _=assert(run()==16777216.0f32)",
        1,
    );
}

#[test]
fn nonfinite_type_arguments_have_portable_identity_across_pool_order_and_edits() {
    for prefix in [
        "",
        "meta let UNRELATED:[]f32=[1,2]\nmeta let INFINITY=1.0/0.0\n",
    ] {
        accepts(
            &format!(
                "{prefix}type Token<value:f64>(int)\nmeta let _=assert(type<Token<(0.0/0.0)>>==type<Token<(0.0/0.0)>>)\nmeta let _=assert(type<Token<0.0>>!=type<Token<-0.0>>)"
            ),
            100,
        );
    }
    let first = "type Token<value:f64>(int)\nmeta let _=assert(type<Token<(0.0/0.0)>>==type<Token<(0.0/0.0)>>)";
    let mut session = Session::new(first.as_bytes().to_vec());
    assert!(session.verify().is_ok());
    session.update(format!("meta let UNRELATED=(1.0/0.0,2)\n{first}").into_bytes());
    assert!(session.verify().is_ok());
    accepts(
        "eff Sample<value:f64>{get()->int}\nfn example()->int{with Sample<(0.0/0.0)>::get()->resume 7;Sample<(0.0/0.0)>::get()}",
        100,
    );
}

#[test]
fn owned_source_cannot_forge_a_committed_float_in_values_or_type_computations() {
    use ril_syntax::ast::{ExprKind, Literal, StmtKind, TypeKind};
    let mut program = ril_syntax::parse("meta let VALUE=1.0").program;
    let StmtKind::Binding(binding) = &mut program.statements[0].kind else {
        panic!()
    };
    binding.value.kind = ExprKind::Literal(Literal::Float("\0ril.float32:3f800000".into()));
    assert!(
        ril_syntax::validate_program(&program)
            .iter()
            .any(|diagnostic| diagnostic.code == "E0111")
    );
    let result = ril_compiler::sema::analyze(&program, ril_compiler_core::source::FileId(0));
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E0111")
    );
    let mut program = ril_syntax::parse("type Holder<n:f64>(int)\ntype Actual=Holder<1.0>").program;
    let StmtKind::Type(declaration) = &mut program.statements[1].kind else {
        panic!()
    };
    let TypeKind::Name { arguments, .. } = &mut declaration.value.as_mut().unwrap().kind else {
        panic!()
    };
    let TypeKind::Computation(value) = &mut arguments[0].kind else {
        panic!()
    };
    value.kind = ExprKind::Literal(Literal::Float("\0ril.float64:3ff0000000000000".into()));
    assert!(
        ril_syntax::validate_program(&program)
            .iter()
            .any(|diagnostic| diagnostic.code == "E0111")
    );
}

#[test]
fn foreign_instances_serialize_portable_normalized_float_arguments() {
    use ril_compiler::session::ProjectSource;
    use ril_ir::foreign::{StaticArgumentValue, StaticValue};
    for prefix in ["", "meta let UNRELATED=(1.0/0.0,2.0/0.0)\n"] {
        let session=Session::with_project("virtual/main.ril".into(),vec![
            ProjectSource{path:"virtual/main.ril".into(),bytes:format!("use api\n{prefix}fn entry(){{assert(Api::number<(0.0/0.0)>()==0);assert(Api::number<(0.0/0.0)>()==0);assert(Api::number<-0.0>()==0)}}").into_bytes()},
            ProjectSource{path:"virtual/api.d.ril".into(),bytes:b"pub fn number<n:f64>()->int".to_vec()},
        ],CheckOptions::default()).unwrap();
        let verified = session.verify().unwrap();
        let core = ril_compiler::lower::lower_core(&verified).unwrap();
        assert_eq!(core.external_functions.len(), 2);
        let values = core
            .external_functions
            .iter()
            .map(|function| &function.static_arguments[0].value)
            .collect::<Vec<_>>();
        assert!(values.iter().any(|value| matches!(
            value,
            StaticArgumentValue::Value {
                value: StaticValue::Float {
                    bits: 64,
                    raw: 0x7ff8000000000000
                },
                ..
            }
        )));
        assert!(values.iter().any(|value| matches!(
            value,
            StaticArgumentValue::Value {
                value: StaticValue::Float {
                    bits: 64,
                    raw: 0x8000000000000000
                },
                ..
            }
        )));
    }
}
