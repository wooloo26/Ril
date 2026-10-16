use ril_compiler::{CompilationOutcome, Session};

#[test]
fn sibling_field_conditionals_keep_independent_type_constraints() {
    for source in [
        "type Pair={written:int,error:?str}\nfn value(flag:bool)->Pair{let count=if flag{1}else{2};.{written:count,error:if flag{Some(\"bad\")}else{None}}}",
        "type Pair={written:int,error:?str}\nfn value(flag:bool)->Pair{if flag{return .{written:0,error:None}};let count=if flag{1}else{2};.{written:count,error:if flag{Some(\"bad\")}else{None}}}",
        "type Pair={written:int,error:?str}\nfn value(flag:bool)->Pair{if flag{return .{written:0,error:None}};let count=if flag{1}else{2};let error=if flag{Some(\"bad\")}else{None};.{written:count,error:error}}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome, CompilationOutcome::Accepted { .. }),
            "{source}: {outcome:?}"
        );
    }
}

#[test]
fn independent_field_constraints_still_reject_a_wrong_field_type() {
    let source = "type Pair={written:int,error:?str}\nfn value(flag:bool)->Pair{if flag{return .{written:0,error:None}};let count=if flag{\"bad\"}else{\"worse\"};let error=if flag{Some(\"bad\")}else{None};.{written:count,error:error}}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic| diagnostic.code=="E0301")),
        "{outcome:?}"
    );
}
