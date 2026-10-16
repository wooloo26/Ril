use ril_compiler::{CompilationOutcome, Session};

#[test]
fn cyclic_clone_elements_keep_one_invariant_collection_type() {
    let source = "type Node={mut value:int,mut following:?Node}\nfn example(){let mut original=Node.{value:0,following:None};original.following=Some(^mut original);let mut copies:[]Node=[];let mut copied=^mut clone(original);copied.value+=1;copies !>Array::push(^mut copied)}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
}

#[test]
fn recursive_collection_equivalence_checks_fields_beyond_the_cycle() {
    let source = "type Node={mut value:int,mut following:?Node}\ntype Other={mut value:str,mut following:?Other}\nfn example(){let mut other=Other.{value:\"bad\",following:None};other.following=Some(^mut other);let mut copies:[]Node=[];copies !>Array::push(^mut other)}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic| diagnostic.code=="E0301")),
        "{outcome:?}"
    );
}

#[test]
fn recursive_collection_equivalence_does_not_change_field_authority() {
    let source = "type Node={mut value:int,mut following:?Node}\ntype Other={value:int,mut following:?Other}\nfn example(){let mut other=Other.{value:1,following:None};other.following=Some(^mut other);let mut copies:[]Node=[];copies !>Array::push(^mut other)}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic| diagnostic.code=="E0301")),
        "{outcome:?}"
    );
}
