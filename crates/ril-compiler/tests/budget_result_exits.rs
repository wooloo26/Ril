use ril_compiler::{CompilationOutcome, Session};

#[derive(Clone, Copy)]
enum Exit {
    Pending,
    Inspected,
    Panic,
}

fn oracle(entry_inspected: bool, normal: Exit, recovery: Exit) -> bool {
    // One pre-existing producer must be covered on every continuing trace.
    // This trace model contains no checker flags or FlowSnapshot operations.
    [normal, recovery]
        .into_iter()
        .all(|exit| entry_inspected || !matches!(exit, Exit::Pending))
}

fn require_verdict(source: &str, allowed: bool) {
    let outcome = Session::new(source.as_bytes().to_vec()).verify();
    if allowed {
        assert!(outcome.is_ok(), "{source}: {outcome:?}");
    } else {
        assert!(
            matches!(&outcome,Err(CompilationOutcome::Rejected{diagnostics})if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720")),
            "{source}: {outcome:?}"
        );
    }
}

#[test]
fn every_normal_recovery_and_panic_trace_matches_the_independent_coverage_model() {
    for entry in [false, true] {
        for normal in [Exit::Pending, Exit::Inspected, Exit::Panic] {
            for recovery in [Exit::Pending, Exit::Inspected, Exit::Panic] {
                let body = |exit| match exit {
                    Exit::Pending => "()",
                    Exit::Inspected => "assert(result is Err(_))",
                    Exit::Panic => "panic(\"exit\")",
                };
                let source = format!(
                    "fn dummy(){{}}\nfn example(limit:int){{(\\->{{let result:Result<int,str>=Err(\"old\");{}{{with Div::exhausted()->{{{}}};Div::budget(limit,\\->{{dummy();{}}})}}}})()}}",
                    if entry {
                        "assert(result is Err(_));"
                    } else {
                        ""
                    },
                    body(recovery),
                    body(normal)
                );
                require_verdict(&source, oracle(entry, normal, recovery));
            }
        }
    }
}

#[test]
fn normal_action_inspection_cannot_cover_an_earlier_exhaustion_exit() {
    let source = r#"fn dummy(){}
fn example(){(\->{
    let result:Result<int,str>=Err("uninspected")
    {with Div::exhausted()->();Div::budget(1,\->{dummy();assert(result is Err(_))})}
})()}"#;
    let outcome = Session::new(source.as_bytes().to_vec()).verify();
    match outcome {
        Err(CompilationOutcome::Rejected { diagnostics })
            if diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0720") =>
        {
            assert!(
                diagnostics
                    .iter()
                    .flat_map(|diagnostic| &diagnostic.causes)
                    .any(|cause| cause.description.contains("exhaustion starts at entry")),
                "{diagnostics:?}"
            );
        }
        Ok(_) => panic!("wrong acceptance: the exhaustion path never inspects result"),
        other => panic!("unexpected result: {other:?}"),
    }
}

#[test]
fn returned_results_keep_distinct_normal_and_recovery_producers() {
    let prefix = "fn produce(limit:int)->Result<int,str>{with Div::exhausted()->Err(\"fuel\");Div::budget(limit,\\->Ok(7))}";
    require_verdict(
        &format!(
            "{prefix}\nfn example(){{let result=produce(0);assert(result is Err(_));let other=produce(100);assert(other is Ok(_))}}"
        ),
        true,
    );
    for allowance in [0, 1, 100] {
        require_verdict(
            &format!("{prefix}\nfn example(){{let result=produce({allowance})}}"),
            false,
        );
    }
}

#[test]
fn an_existing_producer_returned_by_both_exits_remains_the_callers_duty() {
    let prefix = "fn forward(value:Result<int,str>,limit:int)->Result<int,str>{with Div::exhausted()->value;Div::budget(limit,\\->value)}";
    require_verdict(
        &format!(
            "{prefix}\nfn example(){{let result:Result<int,str>=Ok(7);let alias=forward(result,0);assert(alias is Ok(_))}}"
        ),
        true,
    );
    require_verdict(
        &format!(
            "{prefix}\nfn example(){{let result:Result<int,str>=Ok(7);let alias=forward(result,0)}}"
        ),
        false,
    );
}

#[test]
fn nested_passive_carriers_transport_each_result_without_inspecting_it() {
    let prefix = "fn produce(limit:int)->{values:[]Result<int,str>}{with Div::exhausted()->.{values:[Err(\"fuel\")]};Div::budget(limit,\\->.{values:[Ok(7)]})}";
    require_verdict(
        &format!(
            "{prefix}\nfn example(){{let result=produce(0);assert(result.values[0] is Err(_));let other=produce(100);assert(other.values[0] is Ok(_))}}"
        ),
        true,
    );
    require_verdict(
        &format!("{prefix}\nfn example(){{let result=produce(0)}}"),
        false,
    );
}

#[test]
fn checking_one_exact_member_never_discharges_an_independent_sibling() {
    let prefix = "fn produce(limit:int)->{values:[]Result<int,str>}{with Div::exhausted()->.{values:[Err(\"one\"),Err(\"two\")]};Div::budget(limit,\\->.{values:[Ok(1),Ok(2)]})}";
    require_verdict(
        &format!(
            "{prefix}\nfn example(){{let result=produce(100);assert(result.values[0] is Ok(_))}}"
        ),
        false,
    );
    require_verdict(
        &format!(
            "{prefix}\nfn example(){{let result=produce(100);assert(result.values[0] is Ok(_));assert(result.values[1] is Ok(_))}}"
        ),
        true,
    );
}

#[test]
fn conditional_original_aliases_and_unknown_indices_cannot_borrow_member_presence() {
    require_verdict(
        "fn example(flag:bool){let first:Result<int,str>=Ok(1);let second:Result<int,str>=Err(\"other\");let selected=if flag{[first]}else{[second]};assert(selected[0] is Ok(_))}",
        false,
    );
    require_verdict(
        "fn example(index:int){let values:[]Result<int,str>=[Ok(1),Ok(2)];assert(values[index] is Ok(_))}",
        false,
    );
}

#[test]
fn recovery_inspection_is_not_awarded_to_the_normal_path() {
    require_verdict(
        "fn dummy(){}\nfn example(){(\\->{let result:Result<int,str>=Ok(7);{with Div::exhausted()->{assert(result is Ok(_));()};Div::budget(100,dummy)}})()}",
        false,
    );
}
