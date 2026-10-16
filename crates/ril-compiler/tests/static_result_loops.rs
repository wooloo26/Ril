use ril_compiler::{CompilationOutcome, Session};

fn accepts(source: &str) {
    let session = Session::new(source.as_bytes().to_vec());
    let outcome = session.check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{source}\n{outcome:?}"
    );
    let verified = session.verify().unwrap();
    ril_compiler::lower::lower_core(&verified).unwrap();
}

fn rejects(source: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
        "{source}\n{outcome:?}"
    );
}

#[test]
fn last_values_transfer_the_same_producer_and_body_tails_do_not() {
    accepts("meta let _={let value=loop {last Ok(7)};assert(value is Ok(7))}");
    accepts(
        "meta fn make()->Result<int,str>{loop {last Ok(7)}}\nmeta let _=assert(make() is Ok(7))",
    );
    accepts("meta let _=loop {let value=Ok(7);assert(value is Ok(7));last}");
    rejects("meta let _=loop {let value=Ok(7);last}");
    rejects("meta let _={let value=Ok(7);loop {last};()}");
}

#[test]
fn finite_array_iterations_preserve_members_aliases_and_next_paths() {
    accepts("meta let _=for [Ok(1),Ok(2)] as value {assert(value is Ok(_))}");
    accepts("meta let _={let value=Ok(7);for [value,value] as item {assert(item is Ok(7))}}");
    accepts(
        "meta let _=for [true,false] as flag {let value=Ok(7);assert(value is Ok(7));if flag {next}}",
    );
    rejects(
        "meta let _=for [true,false] as flag {let value=Ok(7);if flag {next};assert(value is Ok(7))}",
    );
    rejects("meta let _=for [Ok(1),Ok(2)] as value {assert(value is Ok(_));last}");
    accepts(
        "meta let _={let values=[Ok(1),Ok(2)];for values as value {assert(value is Ok(_));last};assert(values[1] is Ok(2))}",
    );
}

#[test]
fn zero_iterations_and_symbolic_conditions_remain_possible() {
    rejects(
        "meta fn checked(flag:bool){let value=Ok(7);while flag {assert(value is Ok(7));last};()}",
    );
    rejects("meta let _={let value=Ok(7);for [] as item {assert(value is Ok(7))};()}");
    accepts(
        "meta fn checked(flag:bool){let value=Ok(7);while flag {assert(value is Ok(7));last};assert(value is Ok(7))}",
    );
    accepts(
        "meta fn checked(flag:bool){let value=Ok(7);loop {if flag {assert(value is Ok(7));last}else {next}}}",
    );
    rejects("meta fn checked(flag:bool){let value=Ok(7);loop {if flag {last}else {next}}}");
}

#[test]
fn return_and_abnormal_paths_do_not_turn_into_loop_continuations() {
    accepts(
        "meta fn make()->Result<int,str>{for [1] as item {return Ok(7)};Err(\"empty\")}\nmeta let _=assert(make() is Ok(7))",
    );
    accepts(
        "meta fn checked(flag:bool){let value=Ok(7);loop {if flag {assert(false)}else {assert(value is Ok(7));last}}}",
    );
    rejects(
        "meta fn checked(flag:bool){let value=Ok(7);loop {if flag {return}else {assert(value is Ok(7));last}}}",
    );
    accepts(
        "meta let _={let value=loop {while {last Ok(7)} {};last Err(\"unreachable\")};assert(value is Ok(7))}",
    );
}

#[test]
fn ranges_and_maps_keep_finite_iteration_order_and_overwritten_duties() {
    accepts("meta let _=for 1..=3 as item {let value=Ok(item);assert(value is Ok(_))}");
    accepts("meta let _=for -1..=1 as item {let value=Ok(item);assert(value is Ok(_))}");
    accepts("meta let _=for 254u8..=255u8 as item {let value=Ok(item);assert(value is Ok(_))}");
    accepts(
        "meta let _=loop {let value:Result<u64,str>=Ok(18446744073709551615);assert(value is Ok(18446744073709551615u64));last}",
    );
    accepts("meta let _=for 3..1 as item {let value=Ok(item);()}");
    accepts("meta let _=for [\"a\":Ok(1),\"b\":Ok(2)] as (key,value) {assert(value is Ok(_))}");
    rejects("meta let _=for [\"a\":Ok(1),\"a\":Ok(2)] as (key,value) {assert(value is Ok(_))}");
}

#[test]
fn iteration_bindings_and_inner_loops_restore_the_outer_environment() {
    accepts(
        "meta let _={let value=Ok(7);for [Ok(1)] as value {assert(value is Ok(1))};assert(value is Ok(7))}",
    );
    accepts(
        "meta let _={let flag=false;for [true] as flag {loop {last};assert(flag)};let value=Ok(7);if !flag {assert(value is Ok(7))};()}",
    );
    rejects("meta let _={let value=Ok(7);for [Ok(1)] as value {assert(value is Ok(1))};()}");
    accepts(
        "meta let _=loop {for [1] as item {loop {last};next};let value=Ok(7);assert(value is Ok(7));last}",
    );
}

#[test]
fn unknown_collection_quantification_does_not_borrow_an_actual_call_receipt() {
    let source = "meta fn read(values:[]Result<int,str>){for values as value {assert(value is Ok(_))}}\nmeta let _=read([Ok(7)])";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::NotImplemented { .. }),
        "{outcome:?}"
    );
}

#[test]
fn floating_context_cannot_supply_an_unrounded_integer_branch_proof() {
    for setup in [
        "let rounded:f32=16777217;",
        "let numbers:[1]f32=[16777217];let rounded=numbers[0];",
        "let numbers:(f32,int)=(16777217,0);let rounded=numbers.0;",
        "let record=R.{number:16777217};let rounded=record.number;",
        "let rounded=round();",
        "let call=\\->{let number:f32=16777217;number};let rounded=call();",
        "let call:fn()->f32=round;let rounded=call();",
    ] {
        for suffix in [
            "loop {if rounded==16777216 {last}else {assert(value is Ok(7));last}}",
            "if rounded==16777216 {}else {assert(value is Ok(7))}",
        ] {
            let source = format!(
                "type R={{number:f32}}\nmeta fn round()->f32{{16777217}}\nmeta fn checked(){{let value=Ok(7);{setup}{suffix}}}"
            );
            let outcome = Session::new(source.as_bytes().to_vec()).check();
            assert!(
                matches!(outcome, CompilationOutcome::NotImplemented { .. }),
                "{source}\n{outcome:?}"
            );
        }
    }
}

#[test]
fn a_small_model_covers_every_finite_iteration_exit() {
    for length in 0..=3 {
        for early in [false, true] {
            for inspect in [false, true] {
                let items = (0..length)
                    .map(|value| format!("Ok({value})"))
                    .collect::<Vec<_>>()
                    .join(",");
                let source = format!(
                    "meta let _={{let values:[]Result<int,str>=[{items}];for values as value {{{}{}}}}}",
                    if inspect {
                        "assert(value is Ok(_));"
                    } else {
                        ""
                    },
                    if early { "last" } else { "()" }
                );
                let safe = length == 0 || inspect && (!early || length == 1);
                if safe {
                    accepts(&source);
                } else {
                    rejects(&source);
                }
            }
        }
    }
}

#[test]
fn finite_call_chains_have_a_separate_proof_stack_limit() {
    fn chain(length: usize) -> String {
        let mut source =
            "meta fn checked(){let value=Ok(7);step0();assert(value is Ok(7))}\n".to_owned();
        for index in 0..length {
            source.push_str(&format!(
                "meta fn step{index}(){{{}}}\n",
                if index + 1 == length {
                    "()".to_owned()
                } else {
                    format!("step{}()", index + 1)
                }
            ));
        }
        source
    }
    accepts(&chain(8));
    let source = chain(96);
    let parsed = ril_syntax::parse(&source);
    assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
    let evaluation = ril_compiler::static_eval::evaluate(
        &parsed.program,
        ril_compiler_core::target::TargetLayout::POINTER64,
    );
    assert!(
        evaluation.unsupported.iter().any(|failure| failure
            .description
            .contains("static Result proof exceeds its traversal stack allowance")),
        "{:?}",
        evaluation.unsupported
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(outcome, CompilationOutcome::NotImplemented { .. }),
        "{outcome:?}"
    );
}
