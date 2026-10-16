use ril_compiler::{CompilationOutcome, Session};

fn accepted(source: &str) {
    let verified = Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    ril_compiler::lower::lower_core(&verified).unwrap();
}
fn rejected(source: &str, code: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code==code)),
        "{source}: {outcome:?}"
    );
}

#[test]
fn original_host_result_callback_has_only_independently_checked_local_producers() {
    accepted(include_str!("fixtures/repeated_host_results.ril"));
    for source in [
        "use ril/io\nfn read_number(number:int)->int @Fiber{let result=Io::stdin_read(0);assert(result is Ok(_) | Err(_));number}\nfn example() @Fiber{let _=Array::map([1,2],read_number)}",
        "use ril/random\nfn read_number(number:int)->int @Fiber{let result=Random::entropy(0);assert(result is Ok(_) | Err(_));number}\nfn example() @Fiber{let _=Array::map([1,2],read_number)}",
        "fn checked(number:int)->int{let result:Result<int,str>=Ok(number);let alias=result;assert(alias is Ok(_));number}\nfn example(){let _=Array::map([1,2],checked)}",
    ] {
        accepted(source);
    }
}

#[test]
fn each_callback_normal_exit_still_requires_its_actual_result_inspections() {
    for check in [
        "",
        "assert(result is _)",
        "if number==1{assert(result is Ok(_) | Err(_))}",
    ] {
        rejected(
            &format!(
                "use ril/io\nfn read_number(number:int)->int @Fiber{{let result=Io::stdin_read(0);{check};number}}\nfn example() @Fiber{{let _=Array::map([1,2],read_number)}}"
            ),
            "E0720",
        );
    }
    rejected(
        "fn bad(number:int)->int{let outer:Result<Result<int,str>,str>=Ok(Ok(number));assert(outer is Ok(_));number}\nfn example(){let _=Array::map([1,2],bad)}",
        "E0720",
    );
}

#[test]
fn finished_factory_frames_remain_observable_through_returned_captures() {
    accepted(
        r#"
type Action=fn(int)->int &closure
fn make(base:int)->Action &capture{\number->base+number}
fn example(){let action=make(3);assert(Array::map([1,2],action)==[4,5])}
"#,
    );
    accepted(
        r#"
type Action=fn(int)->int &closure
fn make(base:int)->Action &capture{action where fn action(number:int)->int &{closure,base}{base+number}}
fn example(){let action=make(3);assert(Array::map([1,2],action)==[4,5])}
"#,
    );
    accepted(
        r#"
type Action=fn(int)->int &mut &closure
fn make(base:int)->Action &capture{var count=base;count+=0;\number->{count+=number;count}}
fn example(){let mut action=make(0);let values=Array::map([1,2],mut action)}
"#,
    );
    accepted(
        r#"
eff Read{get()->int}
type Reader=fn()->int &closure
fn make()->Reader &capture{let base=3;with Read::get()->resume base;\->Read::get()}
fn example(){let reader=make();let action=\number:int->reader()+number;assert(Array::map([1,2],action)==[4,5])}
"#,
    );
    accepted(
        r#"
type Guard={mut on_close:fn()->()}
type Action=fn(int)->int &mut &closure
fn make(base:int)->Action &capture{var count=base;count+=0;\number->{count+=0;{let scoped mut guard=Guard.{on_close:\->{count+=1}}};count+number}}
fn example(){let mut action=make(0);let values=Array::map([1,2],mut action)}
"#,
    );
}

#[test]
fn reference_transitions_and_escaping_results_do_not_become_iteration_proofs() {
    for source in [
        r#"type Cell={value:int}
type Action=fn(int)->int &mut &closure
fn make()->Action &^mut &capture{var current=Cell.{value:0};current=Cell.{value:1};\number->{current=Cell.{value:number};current.value}}
fn example(){let mut action=make();let values=Array::map([1,2],mut action)}"#,
        r#"type Cell={value:int}
type Action=fn(int)->int &mut &closure
fn make(base:Cell)->Action &^mut &capture{var current=base;current=base;\number->{current=Cell.{value:number};current.value}}
fn example(){let mut action=make(Cell.{value:0});let values=Array::map([1,2],mut action)}"#,
        r#"eff Read{get()->int}
type Reader=fn()->int &mut &closure
fn make()->Reader &^mut &capture{var current=[0];current=[1];with Read::get()->{current=[2];resume current[0]};\->Read::get()}
fn example(){let mut reader=make();let mut action=\number:int->reader()+number;let values=Array::map([1,2],mut action)}"#,
        r#"type Cell={value:int}
type Guard={mut on_close:fn()->()}
type Action=fn(int)->int &mut &closure
fn make()->Action &^mut &capture{var current=Cell.{value:0};current=Cell.{value:1};\number->{current=current;{let scoped mut guard=Guard.{on_close:\->{current=Cell.{value:number}}}};number}}
fn example(){let mut action=make();let values=Array::map([1,2],mut action)}"#,
        r#"fn make(number:int)->Result<int,str>{Ok(number)}
fn example(){let results=Array::map([1,2],make);assert(results[0] is Ok(_));assert(results[1] is Ok(_))}"#,
        r#"fn example(){var saved:?Result<int,str>=None;saved=None;let mut action=\number:int->{saved=Some(Ok(number));number};let _=Array::map([1,2],mut action);match saved{Some(result)->assert(result is Ok(_)),None->()}}"#,
    ] {
        let result = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&result,CompilationOutcome::NotImplemented{reason} if reason.detail.contains("repeated callback") || reason.detail.contains("traversal Result"))
                || matches!(&result,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720")),
            "{source}: {result:?}"
        );
    }
}
