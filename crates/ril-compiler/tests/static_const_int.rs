use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn session(source: &str, target: &str) -> Session {
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
}

#[test]
fn scalar_const_selection_forwarding_shadow_capture_and_type_mix_check_both_layouts() {
    let source = include_str!("fixtures/static_const_int.ril");
    for target in ["pointer32", "pointer64"] {
        let verified = session(source, target).verify().unwrap();
        ril_compiler::lower::lower_core(&verified).unwrap();
    }
}

#[test]
fn missing_and_wrong_sort_scalar_values_are_rejected() {
    for target in ["pointer32", "pointer64"] {
        for (expression, code) in [
            ("size()", "E0344"),
            ("size<\"wrong\">()", "E0323"),
            ("size<1.5>()", "E0323"),
        ] {
            let source = format!("meta fn size<n:int>()->int{{n}}\nmeta let ANSWER={expression}");
            let outcome = session(&source, target).check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic| diagnostic.code==code)),
                "{source}\n{target}: {outcome:?}"
            );
        }
    }
}

#[test]
fn scalar_const_never_authorizes_dependent_dimensions_even_with_closed_actual_values() {
    for target in ["pointer32", "pointer64"] {
        for source in [
            "meta fn sized<n:int>()->[n]int{[1,2]}\nmeta let ANSWER=sized<2>()",
            "meta fn sized<n:int>()->[]int{let values:[n]int=[1,2];values}\nmeta let ANSWER=sized<2>()",
            "type Vec<n:int>=[n]int\nmeta fn sized<n:int>()->Vec<n>{[1,2]}\nmeta let ANSWER=sized<2>()",
        ] {
            let outcome = session(source, target).check();
            assert!(
                matches!(&outcome, CompilationOutcome::NotImplemented { .. }),
                "{source}\n{target}: {outcome:?}"
            );
        }
    }
}

#[test]
fn other_meta_value_sorts_and_unresolved_recursive_const_forwarding_remain_unproved() {
    for source in [
        "meta fn value<n:f64>()->int{1}\nmeta let ANSWER=value<1.0>()",
        "meta fn recurse<n:int>()->int{if n==0{0}else{recurse<n>()}}",
    ] {
        let outcome = session(source, "pointer64").check();
        assert!(
            matches!(&outcome, CompilationOutcome::NotImplemented { .. }),
            "{source}\n{outcome:?}"
        );
    }
}

#[test]
fn target_int_range_stays_independent_of_host_pointer_width() {
    let source = "meta fn size<n:int>()->int{n}\nmeta let ANSWER=size<2147483648>()";
    let narrow = session(source, "pointer32").check();
    assert!(
        matches!(&narrow, CompilationOutcome::Rejected{diagnostics} if !diagnostics.is_empty()),
        "{narrow:?}"
    );
    session(source, "pointer64").verify().unwrap();
}

#[test]
fn old_data_float_and_aggregate_const_normalization_keeps_its_own_sort_rules() {
    let source = r#"
type Token<value:f64>(int)
type Maybe<value:?int>(int)
meta let _=assert(type<Token<0.0>>!=type<Token<-0.0>>)
meta let _=assert(type<Maybe<Some(1)>>==type<Maybe<Some(0x1)>>)
"#;
    for target in ["pointer32", "pointer64"] {
        session(source, target).verify().unwrap();
    }
}
