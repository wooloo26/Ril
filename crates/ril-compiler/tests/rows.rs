use ril_compiler::{CompilationOutcome, Session};
use ril_compiler_core::{source::FileId, target::TargetLayout};
use ril_syntax::ast::{StmtKind, TypeKind};

#[test]
fn nested_row_aliases_keep_unknown_tails_and_close_only_for_complete_arguments() {
    let source = "type Inner<R>={id:int,..R}\ntype Outer<R>={flag:bool,..Inner<R>}\nfn example<R>(value:Outer<R>){}";
    let parsed = ril_syntax::parse(source);
    assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
    let evaluated = ril_compiler::static_eval::evaluate(&parsed.program, TargetLayout::POINTER64);
    assert!(
        evaluated.diagnostics.is_empty(),
        "{:?}",
        evaluated.diagnostics
    );
    let StmtKind::Function(function) = &evaluated.program.statements[2].kind else {
        panic!()
    };
    assert!(
        matches!(&function.parameters[0].ty.as_ref().unwrap().kind,TypeKind::Name {path,arguments} if path==&["Outer"] && arguments.len()==1 && matches!(&arguments[0].kind,TypeKind::Name {path,arguments} if path==&["R"] && arguments.is_empty()))
    );
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );

    let source = "type Inner<R>={id:int,..R}\ntype Outer<R>={flag:bool,..Inner<R>}\ntype Actual=Outer<{mut name:str}>\nfn read(value:Actual)->str{value.name}\nfn example(){let mut item:Actual=.{flag:true,id:1,name:\"Ada\"};item.name=\"Grace\";assert(read(item)==\"Grace\")}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
}

#[test]
fn closed_row_ascription_preserves_stored_reference_permissions() {
    let source = "type Cell={mut value:int}\ntype WithId<R>={id:int,..R}\ntype Actual=WithId<{child:Cell}>\nfn example(){let mut cell=Cell.{value:0};let view observed=cell;let mut wrapped:Actual=.{id:1,child:observed};wrapped.child.value+=1}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome,CompilationOutcome::Rejected {ref diagnostics} if diagnostics.iter().any(|diagnostic| matches!(diagnostic.code.as_str(),"E0520"|"E0522"))),
        "{outcome:?}"
    );
}

#[test]
fn real_row_alias_corpus_cases_are_checked_without_rewriting_expectations() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests");
    let cases = ril_test::discover_cases(&root).unwrap();
    let mut checked = 0;
    for case in cases.into_iter().filter(|case| {
        case.bundle == "tests/conformance/records.ril"
            && matches!(
                case.name.as_str(),
                "accept-overlapping-row" | "reject-overlapping-row"
            )
    }) {
        let source = case
            .files
            .iter()
            .find(|file| file.name == case.root)
            .unwrap();
        let source = std::str::from_utf8(&source.bytes).unwrap();
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        if case.meta.mode == ril_test::Mode::CheckFail {
            assert!(
                matches!(&outcome,CompilationOutcome::Rejected {diagnostics} if case.errors.iter().all(|expected|diagnostics.iter().any(|actual|&actual.code==expected))),
                "{}: {outcome:?}",
                case.id
            );
        } else {
            assert!(
                matches!(outcome, CompilationOutcome::Accepted { .. }),
                "{}: {outcome:?}",
                case.id
            );
        }
        let parsed = ril_syntax::parse(source);
        let public = ril_compiler::sema::analyze(&parsed.program, FileId(0));
        assert_eq!(
            public.program.is_some(),
            case.meta.mode == ril_test::Mode::CheckPass,
            "{}: {:?} {:?}",
            case.id,
            public.diagnostics,
            public.unsupported
        );
        checked += 1;
    }
    assert_eq!(checked, 2);
}
