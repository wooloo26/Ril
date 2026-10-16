use ril_compiler::{CheckOptions, CompilationOutcome, Session};
use std::num::NonZeroU64;

fn check(source: &str, budget: u64) -> CompilationOutcome {
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            static_budget: NonZeroU64::new(budget).unwrap(),
            ..Default::default()
        },
    )
    .check()
}
fn accepts(source: &str, budget: u64) {
    let result = check(source, budget);
    assert!(
        matches!(&result, CompilationOutcome::Accepted { .. }),
        "{source}\n{result:?}"
    );
}
fn rejects(source: &str, code: &str, budget: u64) {
    let result = check(source, budget);
    assert!(
        matches!(&result,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code==code)),
        "{source}\n{result:?}"
    );
}

#[test]
fn defaults_and_labels_use_one_positional_slot_plan() {
    accepts(
        "meta fn pair(first:int=1,second:int=2)->int{first*10+second}\nmeta let _=assert(pair()==12)\nmeta let _=assert(pair(second:9,3)==39)\nmeta let _=assert(pair(first:3,9)==39)\nmeta let _=assert(pair(second:9)==19)",
        100,
    );
    accepts(
        "meta fn choose(value:int=7)->int{value}\nmeta fn invoke()->int{let alias=choose;alias()}\nmeta let _=assert(invoke()==7)",
        100,
    );
    accepts(
        "meta fn choose<T>(first:T,second:T=first)->T{second}\nmeta let _=assert(choose(second:7,first:9)==7)\nmeta let _=assert(choose(\"value\")==\"value\")",
        100,
    );
    accepts(
        "meta let _=assert((\\value:int=7->value)()==7)\nmeta let _=assert((\\first:int,second:int->first*10+second)(second:9,first:3)==39)",
        100,
    );
}

#[test]
fn invalid_labels_duplicates_and_missing_slots_keep_their_specific_diagnostics() {
    let prefix = "meta fn pair(first:int,second:int=2)->int{first+second}\n";
    for (call, code) in [
        ("pair(other:1)", "E0339"),
        ("pair(1,first:2)", "E0325"),
        ("pair()", "E0314"),
        ("pair(1,2,3)", "E0314"),
    ] {
        rejects(&format!("{prefix}meta let VALUE={call}"), code, 100);
    }
}

#[test]
fn default_declarations_remain_universally_checked_and_telescopic() {
    rejects(
        "meta fn wrong(value:int=\"bad\")->int{value}\nmeta let VALUE=wrong(1)",
        "E0301",
        100,
    );
    rejects(
        "meta fn wrong(first:int=second,second:int=2)->int{first}\nmeta let VALUE=wrong(1,2)",
        "E0408",
        100,
    );
    rejects(
        "meta fn wrong(value:int=value)->int{value}\nmeta let VALUE=wrong(1)",
        "E0408",
        100,
    );
    accepts(
        "meta fn fine(value:int={let value=7;value})->int{value}\nmeta let _=assert(fine()==7)",
        100,
    );
}

#[test]
fn evaluation_order_is_callee_then_written_explicit_values_then_ordered_defaults() {
    let prefix = "meta fn fail_assert()->int{assert(false);0}\nmeta fn fail_divide()->int{1/0}\nmeta fn pair(first:int=fail_assert(),second:int=fail_divide())->int{first+second}\n";
    rejects(
        &format!("{prefix}meta let VALUE=pair(second:fail_assert(),first:fail_divide())"),
        "E0830",
        100,
    );
    rejects(
        &format!("{prefix}meta let VALUE=pair(second:fail_divide())"),
        "E0831",
        100,
    );
    rejects(&format!("{prefix}meta let VALUE=pair()"), "E0830", 100);
    rejects(
        &format!("{prefix}meta let VALUE=({{assert(false);\\value:int->value}})(fail_divide())"),
        "E0830",
        100,
    );
    accepts(
        &format!("{prefix}meta let _=assert(pair(second:2,first:1)==3)"),
        1,
    );
}

#[test]
fn defaults_finish_before_the_body_entry_charge_and_are_never_evaluated_twice() {
    let source = "meta fn one()->int{1}\nmeta fn pair(first:int,second:int=first)->int{first+second}\nmeta let _=assert(pair(first:one())==2)";
    rejects(source, "E0811", 1);
    accepts(source, 2);
    let source = "meta fn fail()->int{assert(false);0}\nmeta fn take(value:int=fail())->int{value}\nmeta let VALUE=take()";
    rejects(source, "E0830", 1);
}

#[test]
fn a_default_return_exits_its_callable_without_entering_its_body() {
    let source = "meta fn take(value:int={return 7})->int{99}\nmeta fn caller()->int{take()+1}\nmeta let _=assert(caller()==8)";
    accepts(source, 1);
    accepts(
        "meta fn take(value:int=(\\->{return 7})())->int{value+1}\nmeta let _=assert(take()==8)",
        2,
    );
    rejects(
        "meta fn wrong(value:int={return \"wrong\"})->int{0}\nmeta let VALUE=wrong(1)",
        "E0301",
        100,
    );
}

#[test]
fn default_factory_helpers_keep_their_declaration_environment() {
    accepts(
        "meta fn make(value:int)->fn()->int{read where meta fn read()->int{choose()};meta fn choose(selected:int=sibling())->int{selected};meta fn sibling()->int{value}}\nmeta fn observe()->int{let first=make(7);let second=make(9);assert(first()==7);assert(second()==9);first()}\nmeta let _=assert(observe()==7)",
        100,
    );
}

#[test]
fn typed_callable_interfaces_replace_labels_and_erase_source_defaults() {
    accepts(
        "meta fn choose(value:int=7)->int{value}\nmeta fn invoke()->int{let renamed:fn(other:int)->int=choose;renamed(other:9)}\nmeta let _=assert(invoke()==9)",
        100,
    );
    rejects(
        "meta fn choose(value:int=7)->int{value}\nmeta fn invoke()->int{let renamed:fn(other:int)->int=choose;renamed()}",
        "E0314",
        100,
    );
    rejects(
        "meta fn choose(value:int=7)->int{value}\nmeta fn invoke()->int{let renamed:fn(other:int)->int=choose;renamed(value:9)}",
        "E0339",
        100,
    );
}

#[test]
fn typed_parameters_returns_globals_and_container_members_keep_destination_interfaces() {
    let prefix = "meta fn choose(value:int=7)->int{value}\n";
    for body in [
        "meta fn call(callback:fn(other:int)->int)->int{callback(other:9)}\nmeta let _=assert(call(choose)==9)",
        "meta fn make()->fn(other:int)->int{choose}\nmeta let CHOSEN=make()\nmeta let _=assert(CHOSEN(other:9)==9)",
        "meta let CHOSEN:fn(other:int)->int=choose\nmeta let _=assert(CHOSEN(other:9)==9)",
        "type Holder={call:fn(other:int)->int}\nmeta fn call()->int{let holder=Holder.{call:choose};holder.call(other:9)}\nmeta let _=assert(call()==9)",
        "meta fn call()->int{let original=[choose];let typed:[]fn(other:int)->int=original;assert(original[0]()==7);typed[0](other:9)}\nmeta let _=assert(call()==9)",
        "meta fn call()->int{let typed:?fn(other:int)->int=Some(choose);match typed{Some(callback)->callback(other:9),None->0}}\nmeta let _=assert(call()==9)",
        "meta fn call()->int{let typed:Option<fn(other:int)->int>=Some(choose);match typed{Some(callback)->callback(other:9),None->0}}\nmeta let _=assert(call()==9)",
    ] {
        accepts(&format!("{prefix}{body}"), 100);
    }
    rejects(
        &format!(
            "{prefix}meta fn call()->int{{let typed:[]fn(other:int)->int=[choose];typed[0]()}}"
        ),
        "E0314",
        100,
    );
}

#[test]
fn omitted_reference_defaults_preserve_alias_identity() {
    use ril_compiler::sema::facts::Slot;
    let source =
        "meta fn pair<T>(first:T,second:T=first)->(T,T){(first,second)}\nmeta let ROOT=pair([1,2])";
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = program.facts();
    let root = facts
        .bindings
        .iter()
        .find(|binding| binding.name == "ROOT")
        .unwrap()
        .value
        .origins
        .nodes
        .first()
        .unwrap();
    assert_eq!(
        facts.fields[&(*root, Slot::Tuple(0))].origins,
        facts.fields[&(*root, Slot::Tuple(1))].origins
    );
}

#[test]
fn callable_views_add_no_entry_and_keep_the_meta_type_token_boundary() {
    accepts(
        "meta fn choose(value:int=7)->int{value}\nmeta let CHOSEN:fn(other:int)->int=choose\nmeta let _=assert(CHOSEN(other:9)==9)",
        1,
    );
    accepts(
        "type Make=\\T->{let factory:fn()->type<T>=\\->type<T>;factory()}\ntype Number=Make<int>\nmeta let _=assert(type<Number>==type<int>)",
        2,
    );
    rejects(
        "meta fn wrong(value:int={return type<int>})->int{0}\nmeta let VALUE=wrong(1)",
        "E0812",
        100,
    );
}

#[test]
fn helpers_inside_defaults_have_the_earlier_parameters_lexical_environment() {
    accepts(
        "meta fn choose(value:int,selected:int={read() where meta fn read()->int{value}})->int{selected}\nmeta let _=assert(choose(7)==7)\nmeta let _=assert(choose(9)==9)",
        100,
    );
    rejects(
        "meta fn outer(value:int)->int{choose() where meta fn choose(value:int={read() where meta fn read()->int{value}})->int{value}}\nmeta let VALUE=outer(7)",
        "E0408",
        100,
    );
}

#[test]
fn hoisted_helpers_capture_the_destination_callable_interface() {
    accepts(
        "meta fn choose(value:int=7)->int{value}\nmeta fn call()->int{let renamed:fn(other:int)->int=choose;helper() where meta fn helper()->int{renamed(other:9)}}\nmeta let _=assert(call()==9)",
        100,
    );
    rejects(
        "meta fn choose(value:int=7)->int{value}\nmeta fn call()->int{let renamed:fn(other:int)->int=choose;helper() where meta fn helper()->int{renamed()}}",
        "E0314",
        100,
    );
}

#[test]
fn callable_branch_interfaces_must_all_admit_the_application() {
    accepts(
        "meta fn first(value:int=7)->int{value}\nmeta fn second(value:int=9)->int{value}\nmeta fn select(flag:bool)->int{let selected=if flag{first}else{second};selected()}\nmeta let _=assert(select(true)==7 && select(false)==9)",
        100,
    );
    rejects(
        "meta fn first(value:int=7)->int{value}\nmeta fn second(value:int)->int{value}\nmeta fn select(flag:bool)->int{let selected=if flag{first}else{second};selected()}\nmeta let VALUE=select(true)",
        "E0314",
        100,
    );
    rejects(
        "meta fn first(value:int)->int{value}\nmeta fn second(other:int)->int{other}\nmeta fn select(flag:bool)->int{let selected=if flag{first}else{second};selected(value:7)}\nmeta let VALUE=select(true)",
        "E0339",
        100,
    );
}

#[test]
fn returns_from_callee_or_explicit_arguments_stay_in_the_enclosing_callable() {
    accepts(
        "meta fn take(value:int)->int{99}\nmeta fn caller()->int{take({return 7});100}\nmeta let _=assert(caller()==7)",
        1,
    );
    accepts(
        "meta fn caller()->int{({return 7;\\value:int->value})(1/0);100}\nmeta let _=assert(caller()==7)",
        1,
    );
}
