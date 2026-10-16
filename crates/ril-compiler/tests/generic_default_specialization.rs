use ril_compiler::Session;
use ril_compiler::sema::default_uses::DefaultOrigin;

#[test]
fn default_slots_preserve_exact_application_and_evaluation_identities() {
    for source in [
        ril_test::case_source("tests/regressions/defaults.ril::scalars-and-order"),
        ril_test::case_source("tests/regressions/defaults.ril::local-handler"),
        ril_test::case_source("tests/regressions/defaults.ril::local-budget"),
        ril_test::case_source("tests/regressions/defaults.ril::retained-closure"),
        ril_test::case_source("tests/regressions/defaults.ril::transitive"),
    ] {
        let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
        let core = ril_compiler::lower::lower_core(&verified).unwrap();
        assert!(!core.provenance.specializations.is_empty());
        for instance in &core.provenance.specializations {
            for slot in &instance.defaults {
                assert!(!slot.applications.is_empty());
                for id in &slot.evaluations {
                    let usage = &verified.facts().default_uses[id.0 as usize];
                    let DefaultOrigin::Call(event) = usage.origin else {
                        panic!("probe published")
                    };
                    assert!(slot.applications.iter().any(|item| item.0 == event.0));
                    assert_eq!(usage.target, Some(instance.template));
                    assert_eq!(usage.parameter, slot.parameter);
                    assert!(usage.entered.iter().all(|entered| {
                        instance.invocations.iter().any(|call| call.0 == entered.0)
                    }));
                }
            }
        }
        ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    }
}

#[test]
fn supplied_only_slot_prunes_only_its_private_instances_fallback() {
    let source = ril_test::case_source("tests/regressions/defaults.ril::supplied-only");
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert_eq!(core.provenance.specializations.len(), 2);
    let mut omitted = 0;
    let mut supplied = 0;
    for instance in &core.provenance.specializations {
        let function = core
            .functions
            .iter()
            .find(|function| function.definition == instance.definition)
            .unwrap();
        let slot = &instance.defaults[0];
        assert_eq!(slot.parameter, 1);
        if slot.evaluations.is_empty() {
            supplied += 1;
            assert!(function.parameters[1].default.is_none());
        } else {
            omitted += 1;
            assert!(function.parameters[1].default.is_some());
        }
    }
    assert_eq!((omitted, supplied), (1, 1));
}

#[test]
fn an_early_default_exit_cannot_borrow_an_entered_instances_body_certificate() {
    let source = r#"
eff Mark<T>{touch()}
fn selected<T>(witness:T,stop:bool,value:int=if stop{panic("default")}else{7})->int @Mark<T>{Mark<T>::touch();value}
fn call(stop:bool)->int @Mark<int>{selected(0,stop)}
fn main(){with Mark<int>::touch()->resume();assert(call(false)==7);call(true)}
"#;
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    assert!(verified.facts().default_uses.iter().any(|usage| matches!(
        usage.origin,
        DefaultOrigin::Call(_)
    ) && !usage.evaluation_complete
        && usage.entered.is_empty()));
    let failure = ril_compiler::lower::lower_core(&verified).unwrap_err();
    assert!(
        failure
            .detail
            .contains("no completed body-entry certificate"),
        "{failure:?}"
    );
}
