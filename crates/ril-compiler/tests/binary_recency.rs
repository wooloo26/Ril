use ril_compiler::{CompilationOutcome, Session};

fn compare(body: &str, aliases: bool) -> CompilationOutcome {
    let right = if aliases { "shared" } else { "other" };
    Session::new(format!(
        "type Cell={{mut value:int}}\nfn cell()->Cell{{Cell.{{value:0}}}}\nfn independent()->Cell{{Cell.{{value:0}}}}\nfn compare(left:Cell,mut right:Cell)->bool &mut{{{body}}}\nfn example(){{for [0,1] as index{{let mut shared=cell();let mut other=independent();other.value=2;let result=compare(shared,mut {right});shared.value=3}}}}"
    ).into_bytes()).check()
}

#[test]
fn left_equality_operand_keeps_its_origin_when_right_evaluation_allocates() {
    for body in [
        "left=={right.value+=1;cell()}",
        "left!={right.value+=1;cell()}",
        "left=={let unused=cell();right.value+=1;cell()}",
    ] {
        let result = compare(body, true);
        assert!(
            matches!(&result, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0524")),
            "{body}: {result:?}"
        );
        let result = compare(body, false);
        assert!(
            matches!(&result, CompilationOutcome::Accepted { .. }),
            "{body}: {result:?}"
        );
    }
}
