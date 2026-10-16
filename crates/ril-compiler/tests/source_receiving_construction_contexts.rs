use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn check(source: &str, positive: bool) {
    for layout in ["pointer32", "pointer64"] {
        let session = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: layout.into(),
                ..Default::default()
            },
        );
        if positive {
            let program = session
                .verify()
                .unwrap_or_else(|outcome| panic!("{layout}: {source}\n{outcome:?}"));
            ril_compiler::lower::lower_core(&program).unwrap();
        } else {
            let outcome = session.check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
                "{layout}: {source}\n{outcome:?}"
            );
        }
    }
}

#[test]
fn literal_members_receive_before_their_container_types_freeze() {
    for source in [
        "fn example(){let values:[2][0][3]int=[[],[]]}",
        "fn example(){let pair:([0][2]int,[0][3]int)=([],[])}",
        "type Holder={item:[0][2]int}\nfn example(){let value=Holder.{item:[]}}",
        "fn example(){let value:{mut item:[0][2]int}=.{item:[]}}",
        "fn example(){let callback:fn([2]int)->int=\\values->values[0]}",
    ] {
        check(source, true);
    }
}

#[test]
fn a_new_container_cannot_retype_its_stored_children() {
    for source in [
        "fn example(){let old:[0][3]int=[];let values:[1][0][2]int=[old]}",
        "fn example(){let old:[0][3]int=[];let pair:([0][2]int,())=(old,())}",
        "type Holder={item:[0][2]int}\nfn example(){let old:[0][3]int=[];let value=Holder.{item:old}}",
        "fn example(){let old:[0][3]int=[];let value:{mut item:[0][2]int}=.{item:old}}",
    ] {
        check(source, false);
    }
}

#[test]
fn return_annotations_keep_the_namespace_before_the_body() {
    check(
        "type Items=[0][2]int\nfn correct()->Items{[] where type Items=[0][3]int}",
        true,
    );
    check(
        "type Items=[0][2]int\nfn wrong()->Items{let value:Items=[];value where type Items=[0][3]int}",
        false,
    );
}
