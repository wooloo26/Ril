use ril_compiler::{CompilationOutcome, Session};

const PREFIX: &str = "type Cell={mut value:int}\ntype Action=fn()->() &mut &closure\nfn make(^mut cell:Cell)->Action &^mut &capture{\\->{cell.value+=1}}\n";

#[test]
fn returned_shared_closures_end_only_their_maker_borrows() {
    for body in [
        "let mut first=make(^mut cell);let mut second=make(^mut cell);first();second()",
        "let mut first=make(^mut cell);let mut second=^mut first;first();cell.value+=1;second()",
        "let mut first={make(^mut cell)};let mut second={make(^mut cell)};first();second()",
        "let mut pair=(make(^mut cell),make(^mut cell));pair.0();pair.1()",
    ] {
        let source = format!("{PREFIX}fn example(){{let mut cell=Cell.{{value:0}};{body}}}");
        let result = Session::new(source.into_bytes()).check();
        assert!(
            matches!(result, CompilationOutcome::Accepted { .. }),
            "{body}: {result:?}"
        );
    }
    let source = format!(
        "{PREFIX}fn example(flag:bool){{let mut cell=Cell.{{value:0}};let mut first=if flag{{make(^mut cell)}}else{{make(^mut cell)}};let mut second=make(^mut cell);first();second()}}"
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
}

#[test]
fn active_parameter_and_independent_captured_authority_still_conflict() {
    let source = format!(
        "{PREFIX}fn apply(mut target:Cell,mut action:Action)&mut{{target.value+=1;action()}}\nfn example(){{let mut cell=Cell.{{value:0}};let mut action=make(^mut cell);apply(mut cell,mut action)}}"
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0523")),
        "{outcome:?}"
    );
    let source = format!(
        "{PREFIX}fn tick(mut cell:Cell)&mut{{cell.value+=1}}\nfn apply(mut target:Cell,mut action:Action)&mut{{tick(mut target);action()}}\nfn example(){{let mut cell=Cell.{{value:0}};let mut action=make(^mut cell);apply(mut cell,mut action)}}"
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0523")),
        "{outcome:?}"
    );
}

#[test]
fn ending_a_borrow_does_not_extend_temporary_writer_or_erase_result_duties() {
    for (index, source) in [
        "type Cell={mut value:int}\ntype Action=fn()->() &mut &closure\nfn bad(mut cell:Cell)->Action &capture{\\->{cell.value+=1}}\nfn example(){let mut cell=Cell.{value:0};let mut action=bad(mut cell);action()}",
        "type Cell={mut value:int}\ntype Action=fn()->() &mut &closure\nfn bad(^mut cell:Cell)->Action &^mut &capture{let pending:Result<int,str>=Err(\"lost\");\\->{cell.value+=1}}\nfn example(){let mut cell=Cell.{value:0};let mut action=bad(^mut cell);action()}",
    ].into_iter().enumerate() {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        if index == 0 {
            assert!(matches!(&outcome, CompilationOutcome::NotImplemented{reason} if reason.detail.contains("temporary parameter loan")), "{source}: {outcome:?}");
        } else {
            assert!(matches!(&outcome, CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic| diagnostic.code=="E0720")), "{source}: {outcome:?}");
        }
    }
}

#[test]
fn separately_borrowed_environments_and_parallel_branches_keep_alias_conflicts() {
    let source = format!(
        "{PREFIX}fn apply(mut first:Action,mut second:Action)&mut{{first();second()}}\nfn example(){{let mut left=Cell.{{value:0}};let mut right=Cell.{{value:0}};let mut first=make(^mut left);let mut second=make(^mut right);apply(mut first,mut second)}}"
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
    let source = format!(
        "{PREFIX}fn apply(mut first:Action,mut second:Action)&mut{{first();second()}}\nfn example(){{let mut cell=Cell.{{value:0}};let mut first=make(^mut cell);let mut second=make(^mut cell);apply(mut first,mut second)}}"
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0523")),
        "{outcome:?}"
    );
    let source = format!(
        "use ril/parallel\n{PREFIX}fn example(){{let mut cell=Cell.{{value:0}};let mut first=make(^mut cell);let mut second=make(^mut cell);let _=Parallel::join(\\->{{first()}},\\->{{second()}})}}"
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0619")),
        "{outcome:?}"
    );
}

#[test]
fn loan_ends_keep_exact_invocation_sources_in_core_and_reject_damaged_evidence() {
    use ril_compiler::sema::{
        facts::{Participant, ScopeId},
        invocation_loans as domain,
    };
    let source = format!(
        "{PREFIX}fn example(){{let mut cell=Cell.{{value:0}};let mut first=make(^mut cell);let mut second=make(^mut cell);first();second()}}"
    );
    let verified = Session::new(source.into_bytes()).verify().unwrap();
    let facts = verified.facts();
    domain::validate(facts).unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert_eq!(
        facts.invocation_loan_ends.len(),
        core.provenance.invocation_loan_ends.len()
    );
    assert_eq!(
        facts.invocation_loan_starts.len(),
        core.provenance.invocation_loan_starts.len()
    );
    let ended: std::collections::BTreeSet<_> = facts
        .invocation_loan_ends
        .iter()
        .flat_map(|end| end.loans.keys().copied())
        .collect();
    for closure in &facts.closures {
        for binding in &closure.captures {
            assert!(facts.bindings[*binding].value.participants.iter().all(
                |participant| !matches!(participant,Participant::Loan(loan) if ended.contains(loan))
            ));
        }
    }
    let mut damaged = facts.clone();
    damaged.invocation_loan_ends.pop();
    assert!(domain::validate(&damaged).is_err());
    let mut damaged = facts.clone();
    damaged.invocation_loan_ends[0].activation = ScopeId(0);
    assert!(domain::validate(&damaged).is_err());
    let mut damaged = facts.clone();
    damaged.invocation_loan_starts[0].parameter = u32::MAX;
    assert!(domain::validate(&damaged).is_err());
    let mut damaged = facts.clone();
    let end = damaged.invocation_loan_ends.last_mut().unwrap();
    let loan = *end.loans.keys().next().unwrap();
    end.loans.insert(loan, [Participant::Loan(loan)].into());
    assert!(domain::validate(&damaged).is_err());
    let mut damaged = facts.clone();
    damaged.invocation_loan_starts.clear();
    damaged.invocation_loan_ends.clear();
    assert!(
        domain::validate(&damaged).is_err(),
        "missing all receipts cannot authorize mutable actual invocations"
    );
}
