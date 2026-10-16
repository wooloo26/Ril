use ril_compiler::{CompilationOutcome, Session};

const PREFIX: &str = "type Cell={mut value:int}\nfn cell()->Cell{Cell.{value:0}}\nfn independent()->Cell{Cell.{value:0}}\n";

fn check_case(declaration: &str, body: &str, aliases: bool, code: &str) {
    let body = body.replace("TARGET", if aliases { "shared" } else { "other" });
    let source = format!(
        "{PREFIX}{declaration}\nfn example(){{for [0,1] as index{{let mut shared=cell();let mut other=independent();{body}}}}}"
    );
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    if aliases {
        assert!(
            matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code==code)),
            "{source}: {outcome:?}"
        );
    } else {
        assert!(
            matches!(&outcome, CompilationOutcome::Accepted { .. }),
            "{source}: {outcome:?}"
        );
    }
}

#[test]
fn explicit_and_pipeline_arguments_keep_earlier_origins_across_later_evaluation() {
    for body in [
        "both(mut shared,{let unused=cell();1},mut TARGET)",
        "shared !> both({let unused=cell();1},mut TARGET)",
    ] {
        for aliases in [true, false] {
            check_case(
                "fn both(mut left:Cell,unused:int,mut right:Cell)&mut{left.value+=1;right.value+=1}",
                body,
                aliases,
                "E0523",
            );
        }
    }
}

#[test]
fn fresh_container_members_keep_their_actual_aliases_until_publication() {
    for body in [
        "let mut pair=^mut (^mut shared,{let unused=cell();^mut TARGET});both(mut pair.0,mut pair.1)",
        "let mut pair=^mut .{left:^mut shared,right:{let unused=cell();^mut TARGET}};both(mut pair.left,mut pair.right)",
        "let mut pair=^mut [^mut shared,{let unused=cell();^mut TARGET}];both(mut pair[0],mut pair[1])",
    ] {
        for aliases in [true, false] {
            check_case(
                "fn both(mut left:Cell,mut right:Cell)&mut{left.value+=1;right.value+=1}",
                body,
                aliases,
                "E0523",
            );
        }
    }
    // Map lookup deliberately joins every possible stored value. Keep this
    // alias rejection and use separate maps for the independent-root control.
    let map = "let mut pair=^mut [0:^mut shared,1:{let unused=cell();^mut TARGET}];let mut left=^mut (pair[0] ?? panic(\"key\"));let mut right=^mut (pair[1] ?? panic(\"key\"));both(mut left,mut right)";
    let declaration = "fn both(mut left:Cell,mut right:Cell)&mut{left.value+=1;right.value+=1}";
    check_case(declaration, map, true, "E0523");
    check_case(
        declaration,
        "let mut first=^mut [0:^mut shared];let mut second=^mut [0:{let unused=cell();^mut TARGET}];let mut left=^mut (first[0] ?? panic(\"key\"));let mut right=^mut (second[0] ?? panic(\"key\"));both(mut left,mut right)",
        false,
        "E0523",
    );
}

#[test]
fn omitted_defaults_cannot_move_supplied_arguments_out_of_their_borrow_checks() {
    for aliases in [true, false] {
        check_case(
            "fn both(left:Cell,mut right:Cell,padding:int={let unused=cell();1})&mut{let observed=left.value;right.value+=1}",
            "shared.value+=0;both(shared,mut TARGET)",
            aliases,
            "E0524",
        );
    }
}

#[test]
fn capturing_callee_keeps_its_environment_across_argument_evaluation() {
    let declaration = "type Reader=fn(mut Cell,int)->int &mut &closure\nfn make(source:Cell)->Reader &capture{\\mut target:Cell,padding:int->{let observed=source.value;target.value+=1;observed}}";
    for padding in ["1", "{make(cell());1}"] {
        for aliases in [true, false] {
            check_case(
                declaration,
                &format!(
                    "shared.value+=0;other.value+=0;let view action=make(shared);let result=action(mut TARGET,{padding})"
                ),
                aliases,
                "E0524",
            );
        }
    }
}

#[test]
fn index_receiver_keeps_its_origin_while_the_index_is_evaluated() {
    for aliases in [true, false] {
        check_case(
            "fn both(mut left:Cell,mut right:Cell)&mut{left.value+=1;right.value+=1}",
            "let mut items=^mut [^mut shared];both(mut items[{let unused=cell();0}],mut TARGET)",
            aliases,
            "E0523",
        );
    }
}

#[test]
fn closure_loans_preserve_derived_paths_scalar_copies_and_sequential_sharing() {
    for source in [
        "type Cell={mut value:int}\nfn use_formal(mut cell:Cell)&mut{(\\->{cell.value+=1})()}\nfn example(){let mut cell=Cell.{value:0};use_formal(mut cell)}",
        "type Cell={mut value:int}\nfn example(){let mut cell=Cell.{value:0};let copied=cell.value;let action=\\mut target:Cell->{target.value+=copied};action(mut cell)}",
        "type Cell={mut value:int}\nfn touch(^mut cell:Cell)->Cell &^mut{cell.value+=1;^mut cell}\nfn example(){let mut cell=Cell.{value:0};touch(^mut cell);touch(^mut cell);}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome, CompilationOutcome::Accepted { .. }),
            "{source}: {outcome:?}"
        );
    }
}

#[test]
fn assignment_right_hand_side_keeps_its_origins_during_target_evaluation() {
    for aliases in [true, false] {
        check_case(
            "fn both(mut left:Cell,mut right:Cell)&mut{left.value+=1;right.value+=1}",
            "let mut slots=[Cell.{value:0}];slots[{let unused=cell();0}]=^mut shared;both(mut slots[0],mut TARGET)",
            aliases,
            "E0523",
        );
    }
}

#[test]
fn branch_results_keep_their_saved_origin_relations() {
    let declaration = "fn choose(flag:bool,^mut selected:Cell)->Cell &^mut{if flag{^mut selected}else{let unused=cell();^mut selected}}\nfn both(mut left:Cell,mut right:Cell)&mut{left.value+=1;right.value+=1}";
    for aliases in [true, false] {
        check_case(
            declaration,
            "let mut selected=choose(index==0,^mut shared);both(mut selected,mut TARGET)",
            aliases,
            "E0523",
        );
    }
}

#[test]
fn match_recycling_keeps_its_explicit_missing_transport_boundary() {
    let source = format!(
        "{PREFIX}\nfn choose(flag:bool,^mut selected:Cell)->Cell &^mut{{match flag{{true->^mut selected,false->{{let unused=cell();^mut selected}}}}}}\nfn example(){{for [0,1] as index{{let mut shared=cell();let mut result=choose(index==0,^mut shared);result.value+=1}}}}"
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(outcome, CompilationOutcome::NotImplemented { .. }),
        "{outcome:?}"
    );
}
