use ril_compiler::{CompilationOutcome, Session};

#[test]
fn owned_source_ast_verification_cannot_bypass_syntax_role_validation() {
    let parsed = ril_syntax::parse("fn example(){let BAD=1}");
    assert!(
        parsed
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E0101")
    );
    let result = Session::new(vec![]).verify_program(&parsed.program);
    assert!(
        matches!(result, Err(CompilationOutcome::Rejected { ref diagnostics }) if diagnostics.iter().any(|diagnostic|diagnostic.code == "E0101"))
    );
    let outcome =
        ril_compiler::sema::analyze(&parsed.program, ril_compiler_core::source::FileId(0));
    assert!(outcome.program.is_none());
    assert!(
        outcome
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E0101")
    );
}

#[test]
fn public_semantic_analysis_cannot_bypass_static_verification() {
    for source in [
        "meta let FAILED=assert(false)",
        "meta fn wrong()->int @Fiber{1}",
        "type WithId<R>={id:int,..R}\ntype Duplicate=WithId<{id:int}>",
    ] {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let analyzed =
            ril_compiler::sema::analyze(&parsed.program, ril_compiler_core::source::FileId(0));
        assert!(
            analyzed.program.is_none(),
            "{source} bypassed the static verification boundary"
        );
        assert!(Session::new(source.as_bytes().to_vec()).verify().is_err());
    }
    let source = "meta fn answer()->int{42}\nfn example(){}";
    let parsed = ril_syntax::parse(source);
    let program =
        ril_compiler::sema::analyze(&parsed.program, ril_compiler_core::source::FileId(0))
            .program
            .unwrap();
    assert_eq!(program.resolved_source().statements.len(), 2);
    assert_eq!(program.static_definitions().len(), 1);
    assert!(!program.static_termination().is_empty());
    assert_eq!(program.syntax().statements.len(), 1);
}

#[test]
fn every_public_session_verifier_resolves_user_names_before_granting_a_certificate() {
    let source = "type Prelude{Some(int)}\nfn example(value:Prelude){assert(value is Some(_))}";
    let session = Session::new(source.as_bytes().to_vec());
    let parsed = ril_syntax::parse(source);
    assert!(parsed.is_ok());
    for result in [session.verify(), session.verify_program(&parsed.program)] {
        let Err(CompilationOutcome::Rejected { diagnostics }) = result else {
            panic!("a user constructor was accepted as the standard Option constructor");
        };
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0301")
        );
    }
}
#[test]
fn source_and_owned_ast_verification_keep_distinct_standard_and_user_tags() {
    let source = "type Prelude{Some(int)}\npub fn example(){let user=Prelude::Some(1);assert(user is Prelude::Some(_));let optional:?int=Some(2);assert(optional is Some(_))}";
    let session = Session::new(source.as_bytes().to_vec());
    let parsed = ril_syntax::parse(source);
    assert!(parsed.is_ok());
    for verified in [
        session.verify().unwrap(),
        session.verify_program(&parsed.program).unwrap(),
    ] {
        let core = ril_compiler::lower::lower_core(&verified).unwrap();
        let user = core
            .constructors
            .iter()
            .find(|constructor| constructor.name.ends_with("::Some"))
            .unwrap();
        assert_ne!(user.tag, "Some");
        assert_ne!(user.tag, "Prelude::Some");
    }
}

#[test]
fn a_draft_capturing_callable_cannot_receive_a_verification_certificate() {
    let source = r#"
type Holder={mut count:int, read:fn()->int}
fn example(){
    let original=Holder.{count:0,read:\->0}
    let changed=original |> derive \mut draft->{
        draft.read=\->{draft.count+=1;draft.count}
    }
}
"#;
    let parsed = ril_syntax::parse(source);
    assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
    // This is a safety oracle, not a claim of a complete source diagnostic:
    // unresolved captured-loan storage must not become a verified program.
    assert!(Session::new(source.as_bytes().to_vec()).verify().is_err());
}

#[test]
fn executable_result_contract_uses_transparent_types_even_when_the_body_never_returns() {
    let options = ril_compiler::CheckOptions {
        unit: ril_compiler::UnitKind::Executable,
        ..Default::default()
    };
    for source in [
        "pub fn main()->int{loop{}}",
        "type Done(())\npub fn main()->Done{Done()}",
    ] {
        let outcome = Session::with_options(source.as_bytes().to_vec(), options.clone()).check();
        assert!(
            matches!(outcome,CompilationOutcome::Rejected{ref diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0904")),
            "{outcome:?}"
        );
    }
    let source = "type Done=()\ntype Message=str\ntype Outcome=Result<Done,Message>\npub fn main()->Outcome{Ok()}";
    assert!(matches!(
        Session::with_options(source.as_bytes().to_vec(), options).check(),
        CompilationOutcome::Accepted { .. }
    ));
}
