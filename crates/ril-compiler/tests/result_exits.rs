use ril_compiler::{CompilationOutcome, Session};

fn accepted(source: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{source}: {outcome:?}"
    );
}

fn incomplete_or_rejected(source: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    let checked = match &outcome {
        CompilationOutcome::Rejected { diagnostics } => diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E0720"),
        CompilationOutcome::NotImplemented { reason } => {
            matches!(reason.stage, ril_compiler_core::phase::Stage::Provenance)
                && reason.detail.contains("Result")
        }
        _ => false,
    };
    assert!(
        checked,
        "uncovered exit needs a Result diagnostic or explicit incomplete proof: {source}: {outcome:?}"
    );
}

#[test]
fn inspected_iteration_families_have_checked_loop_exits() {
    // Propagation selects one terminal iteration. The inspected Err wrapper
    // remains that return path's carrier; no outstanding family crosses a
    // backedge and no copy metadata is discarded.
    accepted(
        "fn read(flag:bool)->Result<int,str>{if flag{Ok(1)}else{Err(\"failed\")}}\nfn example(flag:bool)->Result<(),str>{loop{let number=read(flag)?;assert(number==1);if flag{last}};Ok()}",
    );
    accepted(
        "fn read(flag:bool)->Result<int,str>{if flag{Ok(1)}else{Err(\"failed\")}}\nfn example(flag:bool)->Result<(),str>{loop{let number=read(flag)?;assert(number==1);if flag{last}};Ok()}\nfn calls(){assert(example(true) is Ok());assert(example(false) is Err(\"failed\"))}",
    );
    accepted(
        "fn read(flag:bool)->Result<int,str>{if flag{Ok(1)}else{Err(\"failed\")}}\nfn example(flag:bool){loop{let pending=read(flag);assert(pending is Ok(_)|Err(_));if flag{last}}}",
    );
    accepted(
        "fn example(flag:bool)->int{let pending:Result<int,str>=Ok(1);match flag{true->{assert(pending is Ok(_));return 1},false->{assert(pending is Ok(_));2}}}",
    );
}

#[test]
fn result_exits_cannot_borrow_a_later_or_different_branch_inspection() {
    incomplete_or_rejected(
        "fn example(flag:bool)->int{let pending:Result<int,str>=Ok(1);if flag{return 1};assert(pending is Ok(_));0}",
    );
    incomplete_or_rejected(
        "fn read()->Result<int,str>{Ok(1)}\nfn example(flag:bool){loop{let pending=read();if flag{assert(pending is Ok(_));last}else{last}}}",
    );
    incomplete_or_rejected(
        "fn read()->Result<int,str>{Ok(1)}\nfn example(){var index=0;loop{let pending=read();if index==0{assert(pending is Ok(_))};index+=1;if index>=2{last}}}",
    );
}

#[test]
fn result_exit_certificates_are_owned_by_the_actual_invocation() {
    accepted(
        "fn read()->Result<int,str>{Ok(1)}\nfn consume(check:bool)->int{let pending=read();if check{assert(pending is Ok(_));return 1};assert(pending is Ok(_));2}\nfn example(){assert(consume(true)==1);assert(consume(false)==2)}",
    );
    incomplete_or_rejected(
        "fn read()->Result<int,str>{Ok(1)}\nfn consume(check:bool)->int{let pending=read();if check{assert(pending is Ok(_));return 1};return 2}\nfn example(){assert(consume(true)==1);assert(consume(false)==2)}",
    );
}

#[test]
fn complete_record_carriers_copy_result_duties_without_consuming_the_source() {
    let copy =
        "fn copied(source:{result:Result<int,str>})->{result:Result<int,str>}{clone(source)}";
    accepted(&format!(
        "{copy}\nfn example(){{let source=.{{result:Ok(1)}};let duplicated=copied(source);assert(source.result is Ok(1));assert(duplicated.result is Ok(1))}}"
    ));
    incomplete_or_rejected(&format!(
        "{copy}\nfn example(){{let source=.{{result:Ok(1)}};let duplicated=copied(source);assert(duplicated.result is Ok(1))}}"
    ));
    incomplete_or_rejected(&format!(
        "{copy}\nfn example(){{let source=.{{result:Ok(1)}};let first=copied(source);let second=copied(source);assert(source.result is Ok(1));assert(first.result is Ok(1));let _=second}}"
    ));
}

#[test]
fn copied_tuple_and_record_aliases_share_only_their_own_result_families() {
    for (ty, source, first, second) in [
        (
            "({result:Result<int,str>},{result:Result<int,str>})",
            "(shared,shared)",
            ".0.result",
            ".1.result",
        ),
        (
            "{left:{result:Result<int,str>},right:{result:Result<int,str>}}",
            ".{left:shared,right:shared}",
            ".left.result",
            ".right.result",
        ),
    ] {
        let copy = format!("fn copied(source:{ty})->{ty}{{clone(source)}}");
        accepted(&format!(
            "{copy}\nfn example(){{let shared=.{{result:Ok(1)}};let source={source};let duplicated=copied(source);assert(source{first} is Ok(1));assert(duplicated{second} is Ok(1))}}"
        ));
        incomplete_or_rejected(&format!(
            "{copy}\nfn example(){{let shared=.{{result:Ok(1)}};let source={source};let duplicated=copied(source);assert(duplicated{first} is Ok(1));assert(duplicated{second} is Ok(1))}}"
        ));
        incomplete_or_rejected(&format!(
            "{copy}\nfn example(){{let shared=.{{result:Ok(1)}};let source={source};let one=copied(source);let two=copied(source);assert(source{first} is Ok(1));assert(one{second} is Ok(1));let _=two}}"
        ));
    }
}
