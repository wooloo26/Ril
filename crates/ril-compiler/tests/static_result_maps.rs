use ril_compiler::{CheckOptions, CompilationOutcome, Session};

#[test]
fn exact_lookup_and_absence_preserve_real_producers_on_both_layouts() {
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            include_bytes!("fixtures/static_result_map_lookup.ril").to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap();
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

#[test]
fn map_presence_absence_and_overwrite_do_not_inspect_business_results() {
    for source in [
        "meta let _={let pending:Result<int,str>=Ok(7);let values=[\"key\":pending];assert(values[\"key\"] is Some(_))}",
        "meta let _={let pending:Result<int,str>=Ok(7);let values=[\"key\":pending];assert(values[\"other\"] is None)}",
        "meta let _={let first:Result<int,str>=Ok(7);let second:Result<int,str>=Ok(9);let values=[\"key\":first,\"key\":second];match values[\"key\"]{Some(selected)->assert(selected is Ok(9)),None->()}}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected {diagnostics}
            if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720")),
            "{source}\n{outcome:?}"
        );
    }
}

#[test]
fn a_universal_map_cannot_borrow_an_actual_finite_input_as_its_member_proof() {
    let source = "meta fn lookup(values:[str:Result<int,str>])->?Result<int,str>{values[\"key\"]}\nmeta let _={let pending:Result<int,str>=Ok(7);let result=lookup([\"key\":pending]);match result{Some(value)->assert(value is Ok(_)),None->()}}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::NotImplemented { .. }),
        "{outcome:?}"
    );
}

#[test]
fn a_concrete_two_producer_model_agrees_for_every_finite_lookup_and_alias_case() {
    use std::collections::{BTreeMap, BTreeSet};
    let mut checked = 0;
    for alias in [false, true] {
        for first_key in ["a", "b"] {
            for second_key in ["a", "b"] {
                let second_id = usize::from(!alias);
                let mut concrete = BTreeMap::new();
                concrete.insert(first_key, 0usize);
                concrete.insert(second_key, second_id);
                let producers = BTreeSet::from([0usize, second_id]);
                for first_lookup in ["a", "b", "absent"] {
                    for second_lookup in ["a", "b", "absent"] {
                        for inspection_mask in 0..4 {
                            let mut inspected = BTreeSet::new();
                            let mut actions = String::new();
                            for (ordinal, key) in [first_lookup, second_lookup].iter().enumerate() {
                                if inspection_mask & (1 << ordinal) != 0 {
                                    inspected.extend(concrete.get(key).copied());
                                    actions.push_str(&format!(
                                        "match values[\"{key}\"]{{Some(inner)->assert(inner is Ok(_)|Err(_)),None->()}};"
                                    ));
                                } else {
                                    actions.push_str(&format!(
                                        "assert(values[\"{key}\"] is Some(_)|None);"
                                    ));
                                }
                            }
                            let second = if alias { "first" } else { "Ok(7)" };
                            let source = format!(
                                "meta let _={{let first:Result<int,str>=Ok(7);let second:Result<int,str>={second};let values=[\"{first_key}\":first,\"{second_key}\":second];{actions}()}}"
                            );
                            let outcome = Session::new(source.as_bytes().to_vec()).check();
                            if producers.is_subset(&inspected) {
                                assert!(
                                    matches!(&outcome, CompilationOutcome::Accepted { .. }),
                                    "{source}\n{outcome:?}"
                                );
                            } else {
                                assert!(
                                    matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                                    if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
                                    "{source}\n{outcome:?}"
                                );
                            }
                            checked += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(checked, 288);
}
