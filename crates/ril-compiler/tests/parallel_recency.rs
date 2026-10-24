use ril_compiler::{CompilationOutcome, Session};

const PREFIX: &str = "use ril/parallel\ntype Cell={mut value:int,mut other:int}\nfn cell()->Cell{Cell.{value:0,other:0}}\nfn separate()->Cell{Cell.{value:0,other:0}}\n";

fn check(body: &str) -> CompilationOutcome {
    Session::new(format!("{PREFIX}fn example(){{for [0,1] as index{{{body}}}}}").into_bytes())
        .check()
}

#[test]
fn unrelated_allocations_cannot_hide_a_parallel_alias_before_or_after_the_write() {
    let first = "shared.value+=1";
    for left in [
        first,
        "let unused=cell();shared.value+=1",
        "shared.value+=1;let unused=cell()",
    ] {
        for right in [
            first,
            "let unused=cell();shared.value+=1",
            "shared.value+=1;let unused=cell()",
        ] {
            let result = check(&format!(
                "let mut shared=cell();let _=Parallel::join(\\->{{{left}}},\\->{{{right}}})"
            ));
            assert!(
                matches!(&result, CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0619")),
                "{left} / {right}: {result:?}"
            );
        }
    }
}

#[test]
fn unrelated_allocations_preserve_proven_distinct_objects_and_distinct_slots() {
    for body in [
        "let mut left=cell();let mut right=separate();let _=Parallel::join(\\->{left.value+=1},\\->{let unused=cell();right.value+=1})",
        "let mut left=cell();let mut right=separate();let _=Parallel::join(\\->{left.value+=1;let unused=cell()},\\->{right.value+=1})",
        "let mut shared=cell();let _=Parallel::join(\\->{shared.value+=1},\\->{let unused=cell();shared.other+=1})",
        "let mut shared=cell();let _=Parallel::join(\\->{shared.value+=1;let unused=cell()},\\->{shared.other+=1})",
    ] {
        let result = check(body);
        assert!(
            matches!(result, CompilationOutcome::Accepted { .. }),
            "{body}: {result:?}"
        );
    }
}

#[test]
fn pure_callbacks_keep_the_ownership_of_their_observed_local_writes() {
    let result = check(
        "let values=Parallel::map([1,2],\\n->{let mut local=cell();local.value+=1;let unused=cell();n});assert(values==[1,2])",
    );
    assert!(
        matches!(result, CompilationOutcome::Accepted { .. }),
        "{result:?}"
    );
}

#[test]
fn join3_keeps_prior_accesses_across_multiple_allocations_and_nested_callbacks() {
    for body in [
        "let mut shared=cell();let _=Parallel::join3(\\->{shared.value+=1},\\->{let unused=cell()},\\->{shared.value+=1})",
        "let mut shared=cell();let _=Parallel::join(\\->{let _=Parallel::join(\\->{shared.value+=1},\\->{let unused=cell()})},\\->{shared.value+=1})",
    ] {
        let result = check(body);
        assert!(
            matches!(&result, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0619")),
            "{body}: {result:?}"
        );
    }
}

#[test]
fn verified_and_core_accesses_keep_historical_origins_after_later_allocations() {
    let source = format!(
        "{PREFIX}fn example(){{for [0,1] as index{{let mut shared=cell();let _=Parallel::join(\\->{{shared.value+=1}},\\->{{shared.other+=1}});let unused=cell()}}}}"
    );
    let verified = Session::new(source.into_bytes()).verify().unwrap();
    let _core = ril_compiler::lower::lower_core(&verified).unwrap();
    let facts = verified.facts();
    assert!(!facts.parallel_boundaries.is_empty());
}
