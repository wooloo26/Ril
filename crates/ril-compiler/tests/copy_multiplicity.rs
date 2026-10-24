use ril_compiler::{CompilationOutcome, Session};

const PREFIX: &str = "use ril/parallel\ntype Cell={mut count:int}\ntype Holder={mut child:Cell}\n";

fn conflict(body: &str) {
    let source = format!("{PREFIX}{body}");
    let result = Session::new(source.into_bytes()).check();
    assert!(
        matches!(&result, CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0619")),
        "{result:?}"
    );
}
fn accepted(body: &str) {
    let source = format!("{PREFIX}{body}");
    let result = Session::new(source.into_bytes()).check();
    assert!(
        matches!(result, CompilationOutcome::Accepted { .. }),
        "{result:?}"
    );
}

#[test]
fn summary_array_members_cannot_strongly_erase_another_elements_old_child() {
    conflict(
        "fn bad(items:[]Holder){let mut copied=^mut clone(items);let view observed=copied[1].child;copied[0].child=Cell.{count:0};let mut remaining=^mut copied[1].child;let _=Parallel::join(\\->{remaining.count+=1},\\->observed.count)}",
    );
}

#[test]
fn possibly_aliased_tuple_members_receive_the_same_possible_field_write() {
    conflict(
        "fn bad(items:(Holder,Holder)){let mut copied=^mut clone(items);copied.0.child=Cell.{count:0};let view observed=copied.0.child;let mut remaining=^mut copied.1.child;let _=Parallel::join(\\->{remaining.count+=1},\\->observed.count)}",
    );
}

#[test]
fn map_and_nested_collection_families_preserve_unselected_member_aliases() {
    conflict(
        "fn bad(items:[str:Holder]){let mut copied=^mut clone(items);let mut selected=^mut (copied[\"first\"] ?? panic(\"missing\"));let view observed=(copied[\"second\"] ?? panic(\"missing\")).child;selected.child=Cell.{count:0};let mut remaining=^mut (copied[\"second\"] ?? panic(\"missing\")).child;let _=Parallel::join(\\->{remaining.count+=1},\\->observed.count)}",
    );
    conflict(
        "fn bad(items:[]{group:[]Holder}){let mut copied=^mut clone(items);let view observed=copied[1].group[1].child;copied[0].group[0].child=Cell.{count:0};let mut remaining=^mut copied[1].group[1].child;let _=Parallel::join(\\->{remaining.count+=1},\\->observed.count)}",
    );
}

#[test]
fn exact_single_member_and_known_disjoint_objects_keep_strong_updates() {
    accepted(
        "fn good(items:[1]Holder){let mut copied=^mut clone(items);let view observed=copied[0].child;copied[0].child=Cell.{count:0};let mut current=^mut copied[0].child;current.count+=1;assert(observed.count==observed.count)}",
    );
    accepted(
        "fn good(){let items=(Holder.{child:Cell.{count:1}},Holder.{child:Cell.{count:2}});let mut copied=^mut clone(items);let view observed=copied.1.child;copied.0.child=Cell.{count:0};let mut current=^mut copied.0.child;let _=Parallel::join(\\->{current.count+=1},\\->observed.count)}",
    );
}

#[test]
fn core_origins_report_collection_and_row_family_multiplicity() {
    use ril_compiler_core::source::FileId;
    let source = "fn keep<R>(items:[]{..R})->[]{..R}{items}";
    let parsed = ril_syntax::parse(source);
    let analyzed = ril_compiler::sema::analyze(&parsed.program, FileId(0));
    let verified = analyzed.program.as_ref().expect("row family transport");
    let _core = ril_compiler::lower::lower_core(verified).expect("typed provenance");
}

#[test]
fn possible_retention_cannot_waive_an_overwritten_uninspected_result() {
    let source = "type Box={mut result:Result<int,str>}\nfn overwrite(^mut pair:(Box,Box),replacement:Result<int,str>)->Box &mut{let mut a=^mut pair.0;assert(replacement is Ok(_)|Err(_));a.result=replacement;pair.1}\nfn example(flag:bool){let mut left=Box.{result:Err(\"lost\")};let mut right=Box.{result:Ok(2)};assert(right.result is Ok(_)|Err(_));let mut selected=if flag{(^mut left,^mut left)}else{(^mut left,^mut right)};let view output=overwrite(^mut selected,Ok(3));assert(output.result is Ok(_)|Err(_))}";
    let result = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&result, CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720")),
        "{result:?}"
    );
}

#[test]
fn every_old_and_new_result_must_be_checked_before_a_possible_alias_update() {
    let source = "type Box={mut result:Result<int,str>}\nfn overwrite(^mut pair:(Box,Box),replacement:Result<int,str>)->Box &mut{let mut a=^mut pair.0;assert(a.result is Ok(_)|Err(_));assert(pair.1.result is Ok(_)|Err(_));assert(replacement is Ok(_)|Err(_));a.result=replacement;pair.1}\nfn example(flag:bool){let mut left=Box.{result:Err(\"old\")};let mut right=Box.{result:Ok(2)};assert(right.result is Ok(_)|Err(_));let mut selected=if flag{(^mut left,^mut left)}else{(^mut left,^mut right)};let view output=overwrite(^mut selected,Ok(3));assert(output.result is Ok(_)|Err(_))}";
    let result = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(result, CompilationOutcome::Accepted { .. }),
        "{result:?}"
    );
}

#[test]
fn symbolic_pending_result_replacement_keeps_an_explicit_incomplete_proof() {
    // A conservatism oracle, not a language-negative diagnostic assertion:
    // no concrete caller proves which old wrapper remains in outside storage.
    let source = "type Box={mut result:Result<int,str>}\nfn overwrite(^mut pair:(Box,Box),replacement:Result<int,str>)->Box &mut{let mut a=^mut pair.0;assert(replacement is Ok(_)|Err(_));a.result=replacement;pair.1}";
    let result = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&result, CompilationOutcome::NotImplemented{reason} if reason.detail.contains("Result-bearing storage")),
        "{result:?}"
    );
}

#[test]
fn a_possible_alias_cannot_hide_new_scoped_authority_in_an_escaping_holder() {
    let source = "type Guard={on_close:fn()->()}\ntype Holder={mut resource:Guard}\nfn store(^mut pair:(Holder,Holder))->Holder &^mut{let scoped guard=Guard.{on_close:\\->()};let mut a=^mut pair.0;a.resource=guard;pair.1}";
    let result = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&result, CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0604")),
        "{result:?}"
    );
}
