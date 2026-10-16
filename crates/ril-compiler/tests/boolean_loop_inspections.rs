use ril_compiler::{CompilationOutcome, Session};

fn accepts(source: &str) {
    let session = Session::new(source.as_bytes().to_vec());
    let verified = session
        .verify()
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
    ril_compiler::lower::lower_core(&verified).unwrap();
}

#[test]
fn boolean_loops_with_no_result_inspection_do_not_request_a_result_family() {
    accepts("fn example(){for [1,2] as value {assert(value>0 && value<3)}}");
    accepts(
        "fn example(){for [1,2] as value {let selected=value==1 || value==2;assert(selected && true)}}",
    );
    accepts(
        "meta let VALUES=[4]\nfn example() &{VALUES}{for [1] as value {assert(VALUES[0]==4 && value==1)}}",
    );
}

#[test]
fn already_covered_inspections_need_no_new_loop_replay_certificate() {
    accepts(
        "fn example(){let result=Ok(7);assert(result is Ok(7));for [1,2] as value {assert(value>0 && value<3)}}",
    );
}

#[test]
fn empty_or_stale_evidence_does_not_discharge_a_later_result() {
    for source in [
        "fn bad(){for [1,2] as value {let result=Ok(value);let ignored=true || result is Ok(_);()}}",
        "fn bad(){var result:Result<int,str>=Ok(1);let old=result is Ok(1);for [1] as value {result=Ok(value);assert(old)}}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            !matches!(outcome, CompilationOutcome::Accepted { .. }),
            "{source}\n{outcome:?}"
        );
    }
}
