//! End-to-end source compilation tests. These execute linked native programs.
use std::{fs, process::Command};

#[test]
fn generic_record_rows_preserve_runtime_spreads_and_closed_fields() {
    executes(
        r#"
fn stamp<R>(item: {..R}) -> {stamp: int, ..R} { .{stamp: 7, ..item} }
pub fn test_native() {
    let item = stamp(.{id: 1, name: "Ada"})
    assert(item.id == 1 && item.name == "Ada" && item.stamp == 7)
    let {stamp: mark, ..rest} = item
    assert(mark == 7 && rest.id == 1 && rest.name == "Ada")
}
"#,
    );
}

fn executes(source: &str) {
    let report = execution(source);
    assert_eq!(report["runtime"], "returned-unit", "{report}");
    assert_eq!(report["exit"], 0, "{report}");
}

fn execution(source: &str) -> serde_json::Value {
    execution_project(source, &[])
}

fn execution_project(source: &str, modules: &[(&str, &str)]) -> serde_json::Value {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("native.ril");
    fs::write(&input, source).unwrap();
    for (name, contents) in modules {
        fs::write(temp.path().join(name), contents).unwrap();
    }
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&input)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["status"], "executed", "{report}");
    report
}

#[test]
fn scalar_cells_in_escaping_closures_remain_shared() {
    executes(
        r#"
type Step = fn() -> int &closure
fn make_step() -> Step &capture { var count = 0; \-> { count += 1; count } }
pub fn test_native() {
    let mut step = make_step()
    assert(step() == 1 && step() == 2)
}
"#,
    );
}

#[test]
fn structural_patterns_and_lazy_optional_fallbacks() {
    executes(
        r#"
use ril/result
pub fn test_native() {
    match Some(2) { Some(n) -> assert(n == 2), None -> panic("wrong branch") }
    assert((Some(3) ?? panic("eager fallback")) == 3)
    assert((None ?? 5) == 5)
    let expected = 2
    assert(Some(2) is Some(expected))
    assert(!(Some(3) is Some(expected)))
}
"#,
    );
}

#[test]
fn lazy_result_fallback_invokes_native_callback_with_error() {
    executes(
        r#"
use ril/result
pub fn test_native() {
    let recovered = Err("error") ?? \error -> { assert(error == "error"); 7 }
    assert(recovered == 7)
}
"#,
    );
}

#[test]
fn intermediate_reference_survives_gc_during_a_later_block_operand() {
    executes(
        r#"
type Cell = { mut value: int }
fn fresh() -> Cell { Cell.{ value: 42 } }
pub fn test_native() {
    let values = [fresh(), {
        let mut garbage = []
        var index = 0
        while index < 5000 { garbage !> Array::push(index); index += 1 }
        Cell.{ value: len(garbage) }
    }]
    assert(values[0].value == 42 && values[1].value == 5000)
}
"#,
    );
}

#[test]
fn derive_preserves_input_and_internal_child_aliases() {
    executes(
        r#"
type Cell = { mut value: int }
pub fn test_native() {
    let shared = Cell.{ value: 1 }
    let base = .{ left: shared, right: shared }
    let changed = base |> derive \mut draft -> { draft.left.value += 1 }
    assert(base.left.value == 1 && shared.value == 1)
    assert(changed.left.value == 2 && changed.right.value == 2)
}
"#,
    );
}

#[test]
fn record_members_evaluate_in_source_order_and_explicit_fields_override_spreads() {
    executes(
        r#"
var trace = 0
fn mark(value:int)->int &{mut trace} { trace = trace * 10 + value; value }
fn spread()->{value:int} &{mut trace} { let value=mark(2); .{value:value} }
pub fn test_native() &{mut trace} {
    let record = .{value:mark(1), ..spread(), final_value:mark(3)}
    assert(trace == 123)
    assert(record.value == 1 && record.final_value == 3)
}
"#,
    );
}

#[test]
fn computed_patterns_capture_expected_values_and_skip_later_components() {
    executes(
        r#"
pub fn test_native() {
    let expected = 3
    let test = \value -> { value is Some(expected + 1) }
    assert(test(Some(4)) && !test(Some(5)))
    assert((1, 2) is (1, 1 + 1))
    assert(!((1, 2) is (9, panic("skipped expected component"))))
    assert(3 is 1..=3 && !(3 is 1..3))
    match 3 { 1..3 -> panic("half-open bound"), 3..=3 -> (), _ -> panic("range missing") }
}
"#,
    );
}

#[test]
fn for_cursor_reads_later_element_replacements() {
    executes(
        r#"
pub fn test_native() {
    let mut array = [1, 2]
    var total = 0
    for array as value {
        total += value
        array[1] = 7
    }
    assert(total == 8)
    let mut mapping = ["first": 1, "second": 2]
    var combined = 0
    for mapping as (key, value) {
        combined += value
        mapping["second"] = 7
        assert(key == "first" || key == "second")
    }
    assert(combined == 8)
    var range_total = 0
    for 1..=3 as value { range_total += value }
    assert(range_total == 6)
}
"#,
    );
}

#[test]
fn scoped_cleanups_use_current_callbacks_in_lifo_order_on_every_normal_exit() {
    executes(
        r#"
type Guard = { mut on_close: fn() -> () }
var trace = 0
fn mark(value:int) &{mut trace} { trace = trace * 10 + value }
fn early() -> int &{mut trace} {
    let scoped mut guard = Guard.{on_close: \-> mark(6)}
    return 9
}
pub fn test_native() &{mut trace} {
    {
        let scoped mut first = Guard.{on_close: \-> mark(1)}
        let scoped mut second = Guard.{on_close: \-> mark(2)}
        second.on_close = \-> mark(3)
    }
    assert(trace == 31)
    for 0..3 as index {
        let scoped mut guard = Guard.{on_close: \-> mark(index + 4)}
        if index == 0 { next }
        if index == 2 { last }
    }
    assert(trace == 31456)
    assert(early() == 9 && trace == 314566)
}
"#,
    );
}

#[test]
fn scoped_cleanup_preserves_the_primary_panic() {
    let report = execution(
        r#"
type Guard = {on_close:fn()->()}
pub fn test_native() {
    let scoped guard=Guard.{on_close:\->assert(true)}
    panic("primary panic")
}
"#,
    );
    assert_eq!(report["runtime"], "language-panic", "{report}");
    assert_eq!(report["message"], "primary panic", "{report}");
}

#[test]
fn a_cleanup_panic_during_unwinding_is_reported_as_a_double_fault() {
    let report = execution(
        r#"
type Guard = {on_close:fn()->()}
pub fn test_native() {
    let scoped guard=Guard.{on_close:\->panic("cleanup panic")}
    panic("primary panic")
}
"#,
    );
    assert_eq!(report["runtime"], "double-fault", "{report}");
}

#[test]
fn unit_and_tuple_constructor_payloads_have_equivalent_native_patterns() {
    executes(
        r#"
pub fn test_native() {
    let first:Result<(int,str),str>=Ok(7,"seven")
    assert(first is Ok((7,"seven")))
    match first {Ok((number,text))->assert(number==7&&text=="seven"),Err(_)->panic("wrong tag")}
    let second:Result<(int,str),str>=Ok((8,"eight"))
    assert(second is Ok(8,"eight"))
    match second {Ok(number,text)->assert(number==8&&text=="eight"),Err(_)->panic("wrong tag")}
    let unit:Result<(),str>=Ok()
    assert(unit is Ok())
    match unit {Ok()->(),Err(_)->panic("wrong tag")}
}
"#,
    );
}

#[test]
fn native_effect_requests_resume_through_a_transitive_caller_and_reenter_the_handler() {
    executes(
        r#"
eff Read { get() -> int }
fn twice() -> int @Read { Read::get() + Read::get() }
pub fn test_native() {
    with Read::get() -> resume 21
    assert(twice() == 42)
}
"#,
    );
}

#[test]
fn native_effect_abort_returns_the_delimited_block_answer() {
    executes(
        r#"
eff Stop { now() -> int }
fn request() -> int @Stop { Stop::now() }
pub fn test_native() {
    let value = {
        with Stop::now() -> 7
        request() + 100
    }
    assert(value == 7)
}
"#,
    );
}

#[test]
fn native_handler_arms_use_outer_handlers_and_keep_shared_scalar_cells() {
    executes(
        r#"
eff Read { get() -> int }
fn pair() -> int @Read { Read::get() + Read::get() }
pub fn test_native() {
    {
        with Read::get() -> resume 10
        {
            with Read::get() -> { let outer = Read::get(); resume (outer + 1) }
            assert(Read::get() == 11)
        }
    }
    var count = 0
    with Read::get() -> { count += 1; resume count }
    assert(pair() == 3 && count == 2)
}
"#,
    );
}

#[test]
fn native_effect_loop_keeps_a_constant_native_stack_and_roots_its_cells() {
    executes(
        r#"
eff Read { get() -> int }
type Cell = { mut value:int }
pub fn test_native() {
    var index = 0
    let mut result = Cell.{value:0}
    with Read::get() -> resume 1
    while index < 5000 {
        result.value += Read::get()
        index += 1
    }
    assert(result.value == 5000 && index == 5000)
}
"#,
    );
}

#[test]
fn native_effect_handler_parameters_and_nested_bindings_have_distinct_cells() {
    executes(
        r#"
eff Echo { get(int) -> int }
pub fn test_native() {
    let value = 1
    {
        let value = 2
        with Echo::get(value) -> resume (value + 1)
        assert(Echo::get(4) == 5 && value == 2)
    }
    assert(value == 1)
}
"#,
    );
}

#[test]
fn native_mutable_operation_preserves_the_callers_storage_identity() {
    executes(
        r#"
type Cell = {mut value:int}
eff Edit { apply(mut Cell) -> () &mut }
fn advance(mut cell:Cell) &mut {
    with Edit::apply(mut item) -> { item.value += 1; resume () }
    Edit::apply(mut cell)
}
pub fn test_native() {
    let mut cell = Cell.{value:0}
    advance(mut cell)
    assert(cell.value == 1)
}
"#,
    );
}

#[test]
fn native_cps_callable_created_outside_a_handler_uses_its_invocation_handler() {
    executes(
        r#"
eff Read { get() -> int }
pub fn test_native() {
    let action = \-> Read::get()
    with Read::get() -> resume 7
    assert(action() == 7)
}
"#,
    );
}

#[test]
fn native_escaping_cps_closure_keeps_its_mutable_capture_cell() {
    executes(
        r#"
eff Read { get() -> int }
type Step = fn() -> int @Read &closure
fn make() -> Step &capture {
    var count = 0
    \-> {count += 1; Read::get() + count}
}
pub fn test_native() {
    let mut step = make()
    with Read::get() -> resume 10
    assert(step() == 11 && step() == 12)
}
"#,
    );
}

#[test]
fn a_shared_callback_callsite_keeps_distinct_effect_operation_identities() {
    executes(
        r#"
eff First { get() -> int }
eff Second { get() -> int }
fn apply(action:fn()->int)->int {action()}
pub fn test_native() {
    with {First::get()->resume 11,Second::get()->resume 22}
    assert(apply(First::get)==11)
    assert(apply(Second::get)==22)
}
"#,
    );
}

#[test]
fn typed_nominal_and_sum_constructor_values_execute_with_outer_tuple_equivalence() {
    executes(
        r#"
type UserId(int)
type Choice {Pair(int,str),Empty}
pub fn test_native() {
    let make_id=UserId
    let id=make_id(7)
    assert(inner(id)==7)
    let make_pair=Choice::Pair
    let pair=make_pair(7,"seven")
    assert(pair is Choice::Pair((7,"seven")))
    match pair {
        Choice::Pair(number,text)->assert(number==7&&text=="seven"),
        Choice::Empty->panic("wrong branch"),
    }
}
"#,
    );
}

#[test]
fn native_cps_match_binds_payloads_and_runs_guards_after_an_operation() {
    executes(
        r#"
eff Read { get() -> ?int }
pub fn test_native() {
    with Read::get() -> resume Some(3)
    let answer=match Read::get() {
        Some(number) if number>2 -> number+4,
        None -> 0,
        _ -> 1,
    }
    assert(answer==7)
}
"#,
    );
}

#[test]
fn mutually_exclusive_handler_match_arms_each_resume_once() {
    executes(
        r#"
eff ReadAt { get(int) -> int }
pub fn test_native() {
    with ReadAt::get(index) -> match index {0 -> resume 1, _ -> resume 2}
    assert(ReadAt::get(0)==1 && ReadAt::get(1)==2)
}
"#,
    );
}

#[test]
fn named_callables_capture_storage_from_farther_named_layers() {
    executes(
        r#"
fn outer_layer() -> int {
    var count = 0
    middle()
    where
        fn middle() -> int &{closure, mut count} {
            inner()
            where
                fn inner() -> int &{closure outer_layer, mut count} {
                    count += 1
                    count
                }
        }
}
pub fn test_native() { assert(outer_layer() == 1) }
"#,
    );
}

#[test]
fn named_callables_capture_separate_anonymous_layers() {
    executes(
        r#"
pub fn test_native() {
    let run = \-> {
        var x = 0
        let mut nested = \-> {
            var y = 0
            leaf()
            where
                fn leaf() -> int &{closure, mut x} &{closure, mut y} {
                    x += 1
                    y += 1
                    x + y
                }
        }
        nested()
    }
    assert(run() == 2)
}
"#,
    );
}

#[test]
fn escaped_named_callables_keep_their_declaring_cell_alive() {
    executes(
        r#"
type Step = fn() -> int &closure
fn make() -> Step &capture {
    var count = 0
    step
    where fn step() -> int &{closure,mut count} { count += 1; count }
}
pub fn test_native() {
    let mut step=make()
    assert(step()==1 && step()==2)
}
"#,
    );
}

#[test]
fn mutually_recursive_named_callables_use_the_hoisted_cells() {
    executes(
        r#"
fn parity(value:int) -> bool {
    even(value)
    where
        fn even(value:int) -> bool {
            if value==0 {true} else {odd(value-1)}
        }
        fn odd(value:int) -> bool {
            if value==0 {false} else {even(value-1)}
        }
}
pub fn test_native() { assert(parity(10) && !parity(9)) }
"#,
    );
}

#[test]
fn dynamic_labels_use_the_ascribed_signature_and_preserve_written_evaluation_order() {
    executes(
        r#"
type Cell={mut value:int}
fn identity(value:int=1)->int{value}
fn advance(mut cell:Cell)->int &mut{cell.value+=1;cell.value}
fn combine(first:int,second:int)->int{first*10+second}
pub fn test_native(){
    let direct_alias=identity
    let renamed:fn(other:int)->int=identity
    let unnamed:fn(int)->int=identity
    assert(direct_alias()==1 && direct_alias(value:2)==2)
    assert(renamed(other:3)==3 && renamed(4)==4 && unnamed(5)==5)
    let mut counter=Cell.{value:0}
    let action:fn(a:int,b:int)->int=combine
    assert(action(b:advance(mut counter),a:advance(mut counter))==21)
}
"#,
    );
}

#[test]
fn cps_dynamic_labels_reorder_using_the_checked_callsite_signature() {
    executes(
        r#"
eff Read{get()->int}
fn pair(first:int,second:int)->int @Read{Read::get()+first*10+second}
pub fn test_native(){
    let action:fn(left:int,right:int)->int @Read=pair
    with Read::get()->resume 100
    assert(action(right:1,left:2)==121)
}
"#,
    );
}

#[test]
fn scoped_cps_resume_keeps_arm_resources_until_the_resumed_body_finishes() {
    executes(
        r#"
eff Read{get()->int}
type Guard={on_close:fn()->()}
var trace=0
fn close_body() &{mut trace}{trace=trace*10+1}
fn close_arm() &{mut trace}{trace=trace*10+2}
fn request()->int @Read &{mut trace}{
    let scoped guard=Guard.{on_close:close_body}
    Read::get()
}
pub fn test_native() &{mut trace}{
    let answer={
        with Read::get()->{
            let scoped guard=Guard.{on_close:close_arm}
            resume 7
        }
        request()
    }
    assert(answer==7 && trace==12)
}
"#,
    );
}

#[test]
fn scoped_cps_abort_closes_the_arm_before_the_abandoned_body() {
    executes(
        r#"
eff Stop{now()->int}
type Guard={on_close:fn()->()}
var trace=0
fn close_body() &{mut trace}{trace=trace*10+1}
fn close_arm() &{mut trace}{trace=trace*10+2}
fn request()->int @Stop &{mut trace}{
    let scoped guard=Guard.{on_close:close_body}
    Stop::now()+100
}
pub fn test_native() &{mut trace}{
    let answer={
        with Stop::now()->{
            let scoped guard=Guard.{on_close:close_arm}
            7
        }
        request()
    }
    assert(answer==7 && trace==21)
}
"#,
    );
}

#[test]
fn scoped_cps_return_next_and_last_leave_their_lexical_scopes() {
    executes(
        r#"
eff Read{get()->int}
type Guard={mut on_close:fn()->()}
var trace=0
fn mark(value:int) &{mut trace}{trace=trace*10+value}
fn close_loop() &{mut trace}{mark(1)}
fn close_replaced() &{mut trace}{mark(2)}
fn close_return() &{mut trace}{mark(3)}
fn early()->int &{mut trace}{
    let scoped mut guard=Guard.{on_close:close_return}
    with Read::get()->resume 0
    Read::get()
    return 9
}
pub fn test_native() &{mut trace}{
    {
        with Read::get()->resume 1
        var index=0
        while index<3 {
            let scoped mut guard=Guard.{on_close:close_loop}
            index+=Read::get()
            if index==1 {next}
            guard.on_close=close_replaced
            if index==3 {last}
        }
    }
    assert(trace==122)
    assert(early()==9 && trace==1223)
}
"#,
    );
}

#[test]
fn cleanup_callbacks_with_local_handlers_execute_natively() {
    executes(
        r#"
eff Read{get()->()}
type Guard={on_close:fn()->()}
fn cleanup(){with Read::get()->resume (); Read::get()}
pub fn test_native(){let scoped guard=Guard.{on_close:cleanup}}
"#,
    );
}

#[test]
fn scoped_cps_panic_unwinds_the_resumed_body_before_the_deferred_arm() {
    let report = execution(
        r#"
eff Read{get()->()}
type Guard={on_close:fn()->()}
var trace=0
fn close_body() &{mut trace}{assert(trace==0);trace=1}
fn close_arm() &{mut trace}{assert(trace==1);trace=2}
fn request() @Read &{mut trace}{
    let scoped guard=Guard.{on_close:close_body}
    Read::get()
    panic("resumed body panic")
}

pub fn test_native() &{mut trace}{
    with Read::get()->{
        let scoped guard=Guard.{on_close:close_arm}
        resume ()
    }
    request()
}
"#,
    );
    assert_eq!(report["runtime"], "language-panic", "{report}");
    assert_eq!(report["message"], "resumed body panic", "{report}");
}

#[test]
fn scoped_cps_abort_commits_pipeline_writes_and_runs_pure_callbacks() {
    executes(
        r#"
type Resource={mut on_close:fn()->()}
eff Abort{stop()->int}
pub fn test_native(){
    let mut events:[]int=[]
    let result={
        with Abort::stop()->9
        let scoped mut first=Resource.{on_close:\->events !> Array::push(1)}
        let scoped mut second=Resource.{on_close:\->events !> Array::push(2)}
        events !> Array::push(0)
        Abort::stop()
    }
    assert(result==9 && events==[0,2,1])
}
"#,
    );
}

#[test]
fn cps_optional_and_result_fallbacks_are_lazy_and_call_the_actual_recovery() {
    executes(
        r#"
eff Read{get()->int}
fn optional(flag:bool)->?int @Read{if flag{Some(Read::get())}else{None}}
fn result(flag:bool)->Result<int,str> @Read{if flag{Ok(Read::get())}else{Err("bad")}}
fn recover(error:str)->int @Read{assert(error=="bad");Read::get()+1}
pub fn test_native(){
    var count=0
    with Read::get()->{count+=1;resume 21}
    assert((optional(true) ?? (Read::get()+100))==21)
    assert((optional(false) ?? (Read::get()+100))==121)
    assert((result(true) ?? recover)==21)
    assert((result(false) ?? recover)==22)
    assert(count==4)
}
"#,
    );
}

#[test]
fn source_cannot_forge_private_native_identifiers() {
    let temp = tempfile::tempdir().unwrap();
    for name in [
        "__ril_fn_1",
        "__ril_lambda_0",
        "__ril_nested_0",
        "__ril_globals",
    ] {
        let input = temp.path().join("private.ril");
        fs::write(&input, format!("fn {name}()->int{{1}}\n")).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_ril"))
            .arg("check")
            .arg(&input)
            .arg("--json")
            .output()
            .unwrap();
        let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(report["status"], "rejected", "{report}");
        assert!(
            report["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|diagnostic| diagnostic["code"] == "E0102"),
            "{report}"
        );
    }
}

#[test]
fn higher_order_wrappers_accept_native_cps_callbacks_with_local_handlers() {
    executes(
        r#"
eff Read{get()->int}
fn handled(value:int){with Read::get()->resume 1;assert(Read::get()==value)}
fn each(action:fn(int)->()){Array::for_each([1],action)}
pub fn test_native(){each(handled)}
"#,
    );
}

#[test]
fn structured_higher_order_loops_and_variants_resume_and_short_circuit() {
    executes(
        r#"
eff Tick{get(int)->int}
fn identity(value:int)->int @Tick{Tick::get(value)}
fn greater(value:int)->bool @Tick{Tick::get(value)>1}
fn accumulate(total:int,value:int)->int @Tick{total+Tick::get(value)}
fn maybe(value:int)->?int @Tick{Some(Tick::get(value))}
fn fresh()->int @Tick{Tick::get(7)}
fn checked(value:int)->Result<int,str> @Tick{Ok(Tick::get(value))}
fn fix_error(error:str)->str @Tick{assert(error=="x");Tick::get(0);"fixed"}
fn recover(error:str)->int @Tick{assert(error=="x");Tick::get(9)}
fn transform(values:[]int,action:fn(int)->int)->[]int{Array::map(values,action)}
pub fn test_native(){
    var count=0
    with Tick::get(value)->{count+=1;resume value}
    assert(transform([1,2,3],identity)==[1,2,3])
    assert(Array::filter([1,2,3],greater)==[2,3])
    assert(Array::fold([1,2,3],0,accumulate)==6)
    assert(Array::find([1,2,3],greater)==Some(2))
    assert(Array::any([1,2,3],greater))
    assert(Array::all([2,3],greater))
    assert(!Array::all([1,2],greater))
    assert(count==16)
    assert(Options::map(Some(2),identity)==Some(2))
    assert(Options::map(None,identity)==None)
    assert(Options::and_then(Some(2),maybe)==Some(2))
    assert(Options::unwrap_or_else(Some(3),fresh)==3)
    assert(Options::unwrap_or_else(None,fresh)==7)
    assert(Results::map(Ok(2),identity) is Ok(2))
    assert(Results::map_err(Err("x"),fix_error) is Err("fixed"))
    assert(Results::and_then(Ok(2),checked) is Ok(2))
    assert(Results::recover(Err("x"),recover)==9)
    assert(Results::recover(Ok(3),recover)==3)
    assert(count==23)
}
"#,
    );
}

#[test]
fn an_abort_in_a_higher_order_callback_stops_later_visits_and_closes_the_scope() {
    executes(
        r#"
eff Stop{now()->int}
type Guard={on_close:fn()->()}
var trace=0
var closed=0
fn close() &{mut closed}{closed+=1}
fn stop(value:int)->int @Stop &{mut trace}{trace+=1;Stop::now()}
pub fn test_native() &{mut trace,mut closed}{
    let result={
        let scoped guard=Guard.{on_close:close}
        with Stop::now()->9
        let mapper=Array::map
        mapper([1,2,3],stop)
        100
    }
    assert(result==9 && trace==1 && closed==1)
}
"#,
    );
}

#[test]
fn stored_higher_order_builtins_accept_native_cps_callbacks() {
    executes(
        r#"
eff Read{get()->int}
fn handled(value:int)->int{with Read::get()->resume 1;Read::get()+value}
pub fn test_native(){
    let mapper=Array::map
    assert(mapper([1],handled)==[2])
    let record=.{operation:Array::map}
    assert(record.operation([2],handled)==[3])
    let operations=[Array::map]
    assert(operations[0]([3],handled)==[4])
}
"#,
    );
}

#[test]
fn parameter_defaults_are_included_in_suspend_classification() {
    executes(
        r#"
eff Read{get()->int}
fn handled()->int{with Read::get()->resume 1;Read::get()}
fn defaulted(value:int=handled())->int{value}
pub fn test_native(){assert(defaulted()==1)}
"#,
    );
}

#[test]
fn structured_ordering_inside_handlers_preserves_stable_ties_and_lower_bounds() {
    executes(
        r#"
use ril/order
eff Read { identity(int)->int }
type Entry={rank:int,label:str}
fn compare(left:int,right:int)->Order::Ordering {
    Order::compare_int(left,right)
}

fn rank(left:Entry,right:Entry)->Order::Ordering {
    Order::compare_int(left.rank,right.rank)
}
pub fn test_native(){
    with Read::identity(value)->resume value
    assert(Read::identity(1)==1)
    let order=.{compare:compare}
    assert(Order::sorted([9,5,7,3,1,8,6,4,2,0,5],order)==[0,1,2,3,4,5,5,6,7,8,9])
    assert(Order::sorted([1],order)==[1])
    let empty:[]int=[]
    assert(Order::sorted(empty,order)==empty)
    assert(Order::binary_search([1,1,3,5,5,5,8],5,order) is Ok(3))
    assert(Order::binary_search([1,1,3,5,5,5,8],4,order) is Err(3))
    assert(Order::binary_search([1],0,order) is Err(0))
    assert(Order::binary_search([1],2,order) is Err(1))
    assert(Order::binary_search(empty,0,order) is Err(0))
    let ordered=Order::sorted([
        Entry.{rank:2,label:"z"},Entry.{rank:1,label:"a"},
        Entry.{rank:2,label:"y"},Entry.{rank:1,label:"b"}
    ],.{compare:rank})
    assert(ordered[0].label=="a" && ordered[1].label=="b")
    assert(ordered[2].label=="z" && ordered[3].label=="y")
}
"#,
    );
}

#[test]
fn generic_constructor_instances_keep_their_types_and_share_the_declaration_tag() {
    executes(
        r#"
type Token<size:int>(int)
type Box<T>{Item(T),Empty}
fn extract(value:Box<int>)->int {
    match value { Box::Item(number)->number,Box::Empty->-1 }
}
pub fn test_native(){
    let first=Token<1>(11)
    let second=Token<2>(22)
    assert(inner(first)==11 && inner(second)==22)
    let boxed=Box::Item<int>(33)
    assert(extract(boxed)==33)
    match boxed { Box::Item(number)->assert(number==33),Box::Empty->panic("wrong tag") }
}
"#,
    );
}

#[test]
fn with_file_invokes_the_native_callback_once_and_keeps_its_result() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("input.bin");
    fs::write(&path, b"abc").unwrap();
    let text = serde_json::to_string(&path.to_string_lossy()).unwrap();
    executes(&format!(
        r#"
use ril/file
use ril/path
use ril/io
fn read(mut file:File::Handle)->Result<Io::ReadChunk,Io::IoError> @Fiber &mut {{File::read_chunk(mut file,3)}}
fn checked()->Result<(),Io::IoError> @Fiber {{
    let path=Path::from_string({text})
    let chunk=File::with_file(path,File::OpenMode::Read,read)?
    assert(chunk.data==b"abc")
    let empty=File::with_file(path,File::OpenMode::Read,\mut file -> File::read_chunk(mut file,0))?
    assert(empty.data==b""&&!empty.end)
    File::remove_file(path)?
    Ok()
}}
pub fn test_native() @Fiber {{assert(checked() is Ok())}}
"#
    ));
}

#[test]
fn ordering_comparators_can_suspend_under_their_own_finite_handlers() {
    executes(
        r#"
use ril/order
eff Read{identity(int)->int}
fn compare(left:int,right:int)->Order::Ordering{
    with Read::identity(value)->resume value
    Order::compare_int(Read::identity(left),right)
}
pub fn test_native(){
    let ops=.{compare:compare}
    assert(Order::sorted([3,1,2,1],ops)==[1,1,2,3])
    assert(Order::binary_search([1,1,2,3],1,ops) is Ok(0))
    assert(Order::binary_search([1,1,2,3],4,ops) is Err(4))
}
"#,
    );
}

#[test]
fn cps_for_cursors_advance_before_next_and_close_each_iteration_scope() {
    executes(
        r#"
eff Visit{value(int)->int}
type Guard={on_close:fn()->()}
var closed=0
fn close() &{mut closed}{closed+=1}
pub fn test_native() &{mut closed}{
    with Visit::value(number)->resume number
    let mut values=[1,2,3,4]
    var sum=0
    for values as number {
        let scoped guard=Guard.{on_close:close}
        let visited=Visit::value(number)
        if visited==2 {next}
        sum+=visited
        if visited==1 {values[2]=30}
        if visited==30 {last}
    }
    assert(sum==31 && closed==3)
    var ranged=0
    for 0..5 as number {
        let visited=Visit::value(number)
        if visited==2 {next}
        ranged+=visited
    }
    assert(ranged==8)
}
"#,
    );
}

#[test]
fn with_file_keeps_authority_across_callback_suspension_and_preserves_action_errors() {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("input.bin");
    fs::write(&input, b"abc").unwrap();
    let input = serde_json::to_string(&input.to_string_lossy()).unwrap();
    let output =
        serde_json::to_string(&directory.path().join("output.bin").to_string_lossy()).unwrap();
    let missing =
        serde_json::to_string(&directory.path().join("missing.bin").to_string_lossy()).unwrap();
    executes(&format!(
        r#"
use ril/file
use ril/path
use ril/io
eff Read{{count()->int}}
fn read(mut file:File::Handle)->Result<Io::ReadChunk,Io::IoError> @{{Fiber,Read}} &mut {{
    File::read_chunk(mut file,Read::count())
}}
fn read_error(mut file:File::Handle)->Result<Io::ReadChunk,Io::IoError> @{{Fiber,Read}} &mut {{
    File::read_chunk(mut file,Read::count())
}}
fn read_missing(mut file:File::Handle)->Result<Io::ReadChunk,Io::IoError> @{{Fiber,Read}} &mut {{
    File::read_chunk(mut file,Read::count())
}}
fn checked()->Result<(),Io::IoError> @Fiber {{
    var calls=0
    with Read::count()->{{calls+=1;resume 3}}
    let input=Path::from_string({input})
    let output=Path::from_string({output})
    let missing=Path::from_string({missing})
    let chunk=File::with_file(input,File::OpenMode::Read,read)?
    assert(chunk.data==b"abc"&&calls==1)
    match File::with_file(output,File::OpenMode::WriteNew,read_error) {{
        Err(error)->assert(error.kind==Io::ErrorKind::InvalidInput),
        Ok(_)->panic("read from write-only handle"),
    }}
    assert(calls==2)
    assert(File::with_file(missing,File::OpenMode::Read,read_missing) is Err(_))
    assert(calls==2)
    File::remove_file(input)?
    File::remove_file(output)?
    Ok()
}}
pub fn test_native() @Fiber {{assert(checked() is Ok())}}
"#
    ));
}

#[test]
fn ranges_stream_without_a_representable_length_or_an_overflowing_final_increment() {
    executes(
        r#"
eff Visit{value(int)->int}
fn plain(){
    for -1..9223372036854775807 as number {assert(number == -1);last}
    for -9223372036854775808..=9223372036854775807 as number {assert(number == -9223372036854775808);last}
    for 0u64..=18446744073709551615u64 as number {assert(number == 0u64);last}
    var count=0
    for 18446744073709551614u64..=18446744073709551615u64 as number {assert(number>=18446744073709551614u64);count+=1}
    assert(count==2)
    var big=0
    for 1000000000000000000000000000000bigint..=1000000000000000000000000000001bigint as number {assert(number>=1000000000000000000000000000000bigint);big+=1}
    assert(big==2)
}
pub fn test_native(){
    plain()
    with Visit::value(number)->resume number
    for -9223372036854775808..=9223372036854775807 as number {assert(Visit::value(number) == -9223372036854775808);last}
    for 0u64..=18446744073709551615u64 as number {assert(Visit::value(1)==1&&number==0u64);last}
    var count=0
    for 126i8..=127i8 as number {assert(Visit::value(1)==1&&number>=126i8);count+=1}
    assert(count==2)
    var big=0
    for 1000000000000000000000000000000bigint..=1000000000000000000000000000001bigint as number {assert(Visit::value(1)==1&&number>=1000000000000000000000000000000bigint);big+=1}
    assert(big==2)
}
"#,
    );
}

#[test]
fn safe_fields_flatten_standard_options_without_confusing_user_prelude_variants() {
    executes(
        r#"
type Prelude{Some(int),None}
pub fn test_native(){
    let value=Prelude::Some(7)
    let ordinary:?int=Some(8)
    assert(ordinary is Some(8))
    let wrapped=Some(.{child:value})
    let projected=wrapped?.child
    let chosen=projected ?? Prelude::None
    match chosen {Prelude::Some(number)->assert(number==7),Prelude::None->panic("wrong tag")}
    let nested=Some(.{child:Some(9)})
    assert(nested?.child==Some(9))
    let absent:?{child:Prelude}=None
    assert(absent?.child==None)
}
"#,
    );
}

#[test]
fn with_child_invokes_a_native_cps_action_and_reaps_a_real_ril_child() {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("child.ril");
    let executable = directory
        .path()
        .join(if cfg!(windows) { "child.exe" } else { "child" });
    fs::write(&source, "pub fn main(){}").unwrap();
    let built = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("build")
        .arg(&source)
        .args(["--unit", "executable", "--output"])
        .arg(&executable)
        .arg("--json")
        .output()
        .unwrap();
    assert!(
        built.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&built.stdout),
        String::from_utf8_lossy(&built.stderr)
    );
    let report: serde_json::Value = serde_json::from_slice(&built.stdout).unwrap();
    assert_eq!(report["status"], "built", "{report}");
    assert!(executable.is_file());
    let path = serde_json::to_string(&executable.to_string_lossy()).unwrap();
    executes(&format!(
        r#"
use ril/process
use ril/path
use ril/os
eff Visit{{tick()->()}}
fn wait(mut child:Process::Child)->Result<Process::ExitStatus,Process::ProcessError> @{{Fiber,Visit}} &mut {{
    Visit::tick()
    let first=Process::wait(mut child)?
    let second=Process::wait(mut child)?
    assert(first==second)
    Ok(first)
}}
fn wait_error(mut child:Process::Child)->Result<Process::ExitStatus,Process::ProcessError> @{{Fiber,Visit}} &mut {{
    Visit::tick()
    Process::wait(mut child)?
    Err(Process::ProcessError::InvalidCommand("action"))
}}
pub fn test_native() @Fiber {{
    var called=0
    with Visit::tick()->{{called+=1;resume ()}}
    let args:[]Os::NativeString=[]
    let command=Process::command(Path::from_string({path}),args)
    let status=Process::with_child(command,wait) ?? \_error->panic("child")
    assert(Process::success(status)&&called==1)
    assert(Process::with_child(command,wait_error) is Err(Process::ProcessError::InvalidCommand("action")))
    assert(called==2)
    let missing=Process::command(Path::from_string("bad\u{{0}}path"),args)
    assert(Process::with_child(missing,wait_error) is Err(Process::ProcessError::InvalidCommand(_)))
    assert(called==2)
}}
"#
    ));
}

#[test]
fn non_tail_resume_returns_the_delimited_answer_to_the_actual_arm_suffix() {
    executes(
        r#"
eff Read{get()->int}
pub fn test_native(){
    let answer={
        with Read::get()->{let answer=resume 2;answer+5}
        Read::get()+1
    }
    assert(answer==8)
}
"#,
    );
}

#[test]
fn non_tail_resume_runs_two_nested_arm_suffixes_in_lifo_order() {
    executes(
        r#"
eff Read{get()->int}
pub fn test_native(){
    let answer={
        with Read::get()->{let answer=resume 1;answer+10}
        Read::get()+Read::get()
    }
    assert(answer==22)
}
"#,
    );
}

#[test]
fn non_tail_resume_observes_body_cleanup_before_suffix_and_arm_cleanup_afterward() {
    executes(
        r#"
type Guard={mut on_close:fn()->()}
eff Read{get()->int}
pub fn test_native(){
    var stage=0
    let answer={
        with Read::get()->{
            let scoped mut arm=Guard.{on_close:\->{stage=3}}
            let answer=resume 2
            assert(stage==2)
            answer+1
        }
        let scoped mut body=Guard.{on_close:\->{stage=2}}
        Read::get()+5
    }
    assert(answer==8 && stage==3)
}
"#,
    );
}

#[test]
fn non_tail_resume_preserves_arm_values_and_observes_post_continuation_writes() {
    executes(
        r#"
eff Tick{go()->()}
pub fn test_native(){
    var stage=0
    let answer={
        with Tick::go()->{
            let before=stage
            let retained:Result<int,str>=Ok(before)
            let answer=resume ()
            assert(stage==2 && retained is Ok(1))
            stage=3
            answer+before
        }
        stage=1
        Tick::go()
        stage=2
        7
    }
    assert(answer==8 && stage==3)
}
"#,
    );
}

#[test]
fn indexed_sum_matches_keep_the_generic_arm_equations_and_actual_constructor_tags() {
    executes(
        r#"
type Expr<T>{Int(int)->Expr<int>,Bool(bool)->Expr<bool>}
fn eval<T>(value:Expr<T>)->T{
    match value{Expr::Int(number)->number,Expr::Bool(flag)->flag}
}
pub fn test_native(){
    assert(eval(Expr::Int(7))==7)
    assert(eval(Expr::Bool(true)))
    assert(!eval(Expr::Bool(false)))
}
"#,
    );
}

#[test]
fn io_all_aliases_accumulate_chunks_retry_only_suffixes_and_validate_an_empty_write() {
    executes(
        r#"
use ril/io
use ril/bytes
type Reader={mut calls:int}
type Writer={mut calls:int,mut data:bytes}
fn read(mut reader:Reader,maximum:int)->Result<Io::ReadChunk,Io::IoError> &mut{
    assert(maximum>0)
    reader.calls+=1
    if reader.calls==1{Ok(.{data:b"ab",end:false})}else{Ok(.{data:b"c",end:true})}
}
fn write(mut writer:Writer,data:bytes)->Io::WriteProgress &mut{
    writer.calls+=1
    let count=if len(data)==0{0}else{1}
    if count==1{
        let prefix=Bytes::slice(data,0,1) ?? panic("prefix")
        writer.data=Bytes::concat(writer.data,prefix)
    }
    .{written:count,error:None}
}
pub fn test_native(){
    let mut reader=Reader.{calls:0}
    let read_all=Io::read_all
    assert(read_all(mut reader,.{read:read}) is Ok(b"abc"))
    assert(reader.calls==2)
    let mut writer=Writer.{calls:0,data:b""}
    let write_all=Io::write_all
    assert(write_all(mut writer,b"abc",.{write:write}) is Ok())
    assert(writer.calls==3 && writer.data==b"abc")
    assert(write_all(mut writer,b"",.{write:write}) is Ok())
    assert(writer.calls==4 && writer.data==b"abc")
}
"#,
    );
}

#[test]
fn io_all_callbacks_resume_under_the_invocation_handler_on_each_transfer() {
    executes(
        r#"
use ril/io
use ril/bytes
eff Transfer{tick()->()}
type Stream={mut calls:int}
fn read(mut stream:Stream,maximum:int)->Result<Io::ReadChunk,Io::IoError> @Transfer &mut{
    Transfer::tick()
    assert(maximum>0)
    stream.calls+=1
    if stream.calls==1{Ok(.{data:b"a",end:false})}else{Ok(.{data:b"b",end:true})}
}
fn write(mut stream:Stream,data:bytes)->Io::WriteProgress @Transfer &mut{
    Transfer::tick()
    stream.calls+=1
    .{written:if len(data)==0{0}else{1},error:None}
}
pub fn test_native(){
    let read_all=Io::read_all
    let write_all=Io::write_all
    var ticks=0
    with Transfer::tick()->{ticks+=1;resume ()}
    let mut reader=Stream.{calls:0}
    assert(read_all(mut reader,.{read:read}) is Ok(b"ab"))
    assert(ticks==2 && reader.calls==2)
    let mut writer=Stream.{calls:0}
    assert(write_all(mut writer,b"abc",.{write:write}) is Ok())
    assert(ticks==5 && writer.calls==3)
}
"#,
    );
}

#[test]
fn io_all_stops_at_the_first_error_without_rolling_back_committed_progress() {
    executes(
        r#"
use ril/io
use ril/bytes
type Reader={mut calls:int}
type Writer={mut calls:int,mut data:bytes}
fn read(mut reader:Reader,maximum:int)->Result<Io::ReadChunk,Io::IoError> &mut{
    reader.calls+=1
    if reader.calls==1{Ok(.{data:b"prefix",end:false})}
    else{Err(.{kind:Io::ErrorKind::Other,message:"read error",native_code:None})}
}
fn write(mut writer:Writer,data:bytes)->Io::WriteProgress &mut{
    writer.calls+=1
    let prefix=Bytes::slice(data,0,1) ?? panic("prefix")
    writer.data=Bytes::concat(writer.data,prefix)
    .{written:1,error:Some(.{kind:Io::ErrorKind::Other,message:"write error",native_code:None})}
}
pub fn test_native(){
    let mut reader=Reader.{calls:0}
    let result=Io::read_all(mut reader,.{read:read})
    match result{Err(error)->assert(error.message=="read error"),Ok(_)->panic("lost read error")}
    assert(reader.calls==2)
    let mut writer=Writer.{calls:0,data:b""}
    let written=Io::write_all(mut writer,b"abc",.{write:write})
    match written{Err(error)->assert(error.message=="write error"),Ok()->panic("lost write error")}
    assert(writer.calls==1 && writer.data==b"a")
}
"#,
    );
}

#[test]
fn io_all_contract_violations_are_language_panics_at_the_transfer_boundary() {
    let read = execution(
        r#"
use ril/io
type Stream={mut calls:int}
fn invalid(mut stream:Stream,maximum:int)->Result<Io::ReadChunk,Io::IoError> &mut{
    stream.calls+=1
    Ok(.{data:b"",end:false})
}
pub fn test_native(){
    let mut stream=Stream.{calls:0}
    let _=Io::read_all(mut stream,.{read:invalid}) ?? \_->b""
}
"#,
    );
    assert_eq!(read["runtime"], "language-panic", "{read}");
    assert_eq!(read["message"], "empty read without eof", "{read}");
    for (written, message) in [
        (-1, "negative progress"),
        (0, "no progress"),
        (2, "excess progress"),
    ] {
        let write = execution(&format!(
            r#"
use ril/io
type Stream={{mut calls:int}}
fn invalid(mut stream:Stream,data:bytes)->Io::WriteProgress &mut{{
    stream.calls+=1
    .{{written:{written},error:None}}
}}
pub fn test_native(){{
    let mut stream=Stream.{{calls:0}}
    let _=Io::write_all(mut stream,b"x",.{{write:invalid}}) ?? \_->()
}}
"#
        ));
        assert_eq!(write["runtime"], "language-panic", "{write}");
        assert_eq!(write["message"], message, "{write}");
    }
}

#[test]
fn an_abort_in_an_io_callback_stops_transfers_and_closes_the_caller_scope() {
    executes(
        r#"
use ril/io
eff Stop{now()->()}
type Stream={mut calls:int}
type Guard={mut on_close:fn()->()}
fn read(mut stream:Stream,maximum:int)->Result<Io::ReadChunk,Io::IoError> @Stop &mut{
    stream.calls+=1
    Stop::now()
    Ok(.{data:b"x",end:false})
}
pub fn test_native(){
    var closed=0
    let mut stream=Stream.{calls:0}
    let answer={
        with Stop::now()->7
        let scoped mut guard=Guard.{on_close:\->{closed+=1}}
        let _=Io::read_all(mut stream,.{read:read}) ?? \_->b""
        99
    }
    assert(answer==7 && stream.calls==1 && closed==1)
}
"#,
    );
}

#[test]
fn safe_indexes_skip_the_index_for_none_receivers_in_managed_and_cps_functions() {
    executes(
        r#"
eff Pick{index()->int}
fn plain(){
    let missing:?[]int=None
    assert(missing?[panic("index must not execute")] == None)
    assert([1]?[1]==None && [1]?[-1]==None)
    let present:?[]int=Some([7])
    assert(present?[0]==Some(7) && present?[1]==None)
    let nested:?[]?int=Some([Some(9),None])
    assert(nested?[0]==Some(9) && nested?[1]==None)
}
pub fn test_native(){
    plain()
    var calls=0
    with Pick::index()->{calls+=1;resume 0}
    let missing:?[]int=None
    assert(missing?[Pick::index()]==None && calls==0)
    assert(missing?[panic("CPS index must not execute")] == None)
    let present:?[]int=Some([7])
    assert(present?[Pick::index()]==Some(7) && calls==1)
    let nested:?[]?int=Some([Some(9),None])
    assert(nested?[0]==Some(9) && nested?[1]==None)
}
"#,
    );
}

#[test]
fn cps_defaults_follow_parameter_order_and_preserve_written_argument_order_with_holes() {
    executes(
        r#"
eff Identity{get(int)->int}
type Counter={mut trace:int}
fn step(number:int)->int{with Identity::get(value)->resume value;Identity::get(number)}
fn pair(first:int=step(1),second:int=step(first+1),third:int=step(second+1))->int{first*100+second*10+third}
fn mark(mut counter:Counter,number:int)->int &mut{counter.trace=counter.trace*10+number;number}
pub fn test_native(){
    assert(pair()==123 && pair(4)==456)
    assert(pair(third:9)==129 && pair(second:5)==156)
    assert(pair(third:9,first:4)==459)
    let alias=pair
    assert(alias(third:9)==129)
    let mut counter=Counter.{trace:0}
    assert(pair(third:mark(mut counter,3),first:mark(mut counter,1))==123)
    assert(counter.trace==31)
}
"#,
    );
}

#[test]
fn cps_defaults_skip_supplied_unit_and_bind_earlier_parameters_in_anonymous_callables() {
    executes(
        r#"
eff Identity{get(int)->int}
fn step(number:int)->int{with Identity::get(value)->resume value;Identity::get(number)}
fn unit_value(value:()=panic("supplied unit default must not execute")){
    with Identity::get(number)->resume number
    assert(Identity::get(0)==0)
    value
}
pub fn test_native(){
    unit_value(())
    let action=\first:int=step(2),second:int=step(first+1)->first*10+second
    assert(action()==23 && action(4)==45 && action(second:9)==29)
}
"#,
    );
}

#[test]
fn cps_defaults_keep_local_abort_boundaries_and_close_default_expression_resources() {
    executes(
        r#"
eff Stop{now()->int}
type Guard={mut on_close:fn()->()}
fn defaulted(value:int={
    var stage=0
    let answer={
        with Stop::now()->7
        let scoped mut guard=Guard.{on_close:\->{stage+=1}}
        Stop::now()
        99
    }
    assert(stage==1)
    answer
},second:int=value+1)->int{value*10+second}
pub fn test_native(){
    assert(defaulted()==78)
    assert(defaulted(2)==23)
    assert(defaulted(second:4)==74)
}
"#,
    );
}

#[test]
fn managed_named_argument_holes_use_defaults_without_mistaking_unit_for_a_missing_value() {
    executes(
        r#"
fn pair(first:int=1,second:int=first+1)->int{first*10+second}
fn unit_value(first:()=panic("unit is present"),second:int=3)->int{second}
pub fn test_native(){
    assert(pair(second:9)==19)
    assert(pair(second:9,first:4)==49)
    assert(unit_value(())==3)
}
"#,
    );
}

#[test]
fn nested_windows_keep_relative_bounds_and_evaluate_effectful_bounds_once() {
    executes(
        r#"
eff Pick{bound(int)->int}
fn plain(){
    let values=[10,20,30,40]
    let window=values[1..4]
    let nested=window[1..=1]
    assert(nested==[30] && len(nested)==1)
    assert(window[3..3]==[] && window[..=]==[20,30,40])
}
pub fn test_native(){
    plain()
    var calls=0
    with Pick::bound(number)->{calls+=1;resume number}
    let values=[10,20,30,40]
    let window=values[Pick::bound(1)..Pick::bound(4)]
    let nested=window[Pick::bound(1)..=Pick::bound(1)]
    assert(calls==4 && nested==[30] && len(nested)==1)
}
"#,
    );
}

#[test]
fn nested_window_bounds_are_checked_against_the_window_before_the_backing_array() {
    let report = execution(
        r#"
pub fn test_native(){
    let values=[10,20,30,40]
    let window=values[1..3]
    let _=window[0..3]
}
"#,
    );
    assert_eq!(report["runtime"], "language-panic", "{report}");
}

#[test]
fn source_budget_uses_semantic_coverage_for_zero_one_and_unbounded_actions() {
    executes(
        r#"
fn one()->int{1}
fn forbidden()->int{panic("zero action must not execute")}
fn spin()->int{loop{}}
fn zero()->?int{with Div::exhausted()->None;Some(Div::budget(0,forbidden))}
fn single()->?int{with Div::exhausted()->None;Some(Div::budget(1,one))}
fn wrapped()->?int{with Div::exhausted()->None;Div::budget(1,\->Some(1))}
fn bounded()->?int{with Div::exhausted()->None;Some(Div::budget(20000,spin))}
pub fn test_native(){
    assert(zero()==None)
    assert(single()==Some(1))
    assert(wrapped()==Some(1))
    assert(bounded()==None)
    assert(one()==1)
}
"#,
    );
}

#[test]
fn source_budget_remaining_block_charges_final_iteration_tests() {
    executes(
        r#"
fn exact()->?int{
    with Div::exhausted()->None
    with Div::budget(4)
    var total=0
    for [1,2] as number{total+=number}
    Some(total)
}
fn short()->?int{
    with Div::exhausted()->None
    with Div::budget(3)
    var total=0
    for [1,2] as number{total+=number}
    Some(total)
}
pub fn test_native(){assert(exact()==Some(3));assert(short()==None)}
"#,
    );
}

#[test]
fn source_budget_covers_internal_handlers_and_sequential_callbacks() {
    executes(
        r#"
eff Read{get()->int}
fn action()->int{with Read::get()->resume 7;Read::get()}
fn run()->?int{with Div::exhausted()->None;Some(Div::budget(20,action))}
fn map_action()->int{
    let values=Array::map([1,2],\number->number+1)
    values[0]+values[1]
}
fn mapped()->?int{with Div::exhausted()->None;Some(Div::budget(100,map_action))}
pub fn test_native(){assert(run()==Some(7));assert(mapped()==Some(5))}
"#,
    );
}

#[test]
fn source_budget_negative_limit_panics_before_action_and_recovery() {
    let report = execution(
        r#"
fn action()->int{panic("action must not execute")}
pub fn test_native(){
    with Div::exhausted()->panic("recovery must not execute")
    let _=Div::budget(-1,action)
}
"#,
    );
    assert_eq!(report["runtime"], "language-panic", "{report}");
    assert!(
        report["message"].as_str().unwrap().contains("negative"),
        "{report}"
    );
}

#[test]
fn source_budget_callback_entries_charge_builtins_once_and_do_not_double_charge_regular_functions()
{
    executes(
        r#"
fn measure(text:str)->int{String::byte_len(text)}
fn builtin_action()->int{let sizes=Array::map(["abc"],String::byte_len);sizes[0]}
fn regular_action()->int{let sizes=Array::map(["abc"],measure);sizes[0]}
fn builtin(limit:int)->?int{with Div::exhausted()->None;Some(Div::budget(limit,builtin_action))}
fn regular(limit:int)->?int{with Div::exhausted()->None;Some(Div::budget(limit,regular_action))}
pub fn test_native(){
    assert(builtin(3)==Some(3) && builtin(2)==None)
    assert(regular(3)==Some(3) && regular(2)==None)
}
"#,
    );
}

#[test]
fn source_budget_immediately_invokes_nested_and_higher_order_remaining_blocks() {
    executes(
        r#"
fn spin()->int{loop{}}
halt fn nested()->?int{
    with Div::exhausted()->None
    with Div::budget(2)
    with Div::exhausted()->Some(99)
    with Div::budget(100)
    Some(spin())
}
halt fn mapped()->?int{
    with Div::exhausted()->None
    with Div::budget(100)
    let values=Array::map([1,2],\number->number+1)
    Some(values[0]+values[1])
}
pub fn test_native(){assert(nested()==None);assert(mapped()==Some(5))}
"#,
    );
}

#[test]
fn generic_sum_tuple_payloads_resolve_by_the_stable_constructor_tag() {
    executes(
        r#"
type Pair<T>{Both(T,T),Empty}
pub fn test_native(){
    let pair=Pair::Both<int>(2,3)
    assert(pair is Pair::Both(2,3))
    match pair{Pair::Both(left,right)->assert(left+right==5),Pair::Empty->panic("wrong tag")}
}
"#,
    );
}

#[test]
fn closed_record_rows_keep_nested_fields_and_mutability_in_native_layouts() {
    executes(
        r#"
type Inner<R>={id:int,..R}
type Outer<R>={flag:bool,..Inner<R>}
type Actual=Outer<{mut name:str}>
pub fn test_native(){
    let mut item:Actual=.{flag:true,id:1,name:"Ada"}
    item.name="Grace"
    assert(item.id==1 && item.name=="Grace" && item.flag)
}
"#,
    );
}

#[test]
fn closed_aggregate_gadt_equations_keep_the_actual_tuple_payload_and_answer() {
    executes(
        r#"
type Expr<T>{Pair((int,bool))->Expr<(int,bool)>,Flag(bool)->Expr<bool>}
fn evaluate<T>(value:Expr<T>)->T{
    match value{Expr::Pair((number,flag))->(number,flag),Expr::Flag(flag)->flag}
}
pub fn test_native(){
    let pair=evaluate(Expr::Pair((7,true)))
    assert(pair.0==7 && pair.1)
    assert(evaluate(Expr::Flag(true)))
}
"#,
    );
}

#[test]
fn explicit_indexed_iteration_stores_successors_and_keeps_an_ended_cursor_sticky() {
    executes(
        r#"
use ril/iter
pub fn test_native(){
    let source=Iter::indexed([10,20])
    let mut cursor=Iter::cursor(0)
    assert(Iter::pull(mut cursor,source)==Some(10) && cursor.state==1)
    assert(Iter::pull(mut cursor,source)==Some(20) && cursor.state==2)
    assert(Iter::pull(mut cursor,source)==None && cursor.ended)
    assert(Iter::pull(mut cursor,source)==None && cursor.state==2)
}
"#,
    );
}

#[test]
fn explicit_indexed_iteration_rejects_a_negative_state_before_element_access() {
    let report = execution(
        r#"
use ril/iter
pub fn test_native(){
    let source=Iter::indexed([1])
    let mut cursor=Iter::cursor(-1)
    let _=Iter::pull(mut cursor,source)
}
"#,
    );
    assert_eq!(report["runtime"], "language-panic", "{report}");
    assert!(
        report["message"]
            .as_str()
            .unwrap()
            .contains("negative index"),
        "{report}"
    );
}

#[test]
fn explicit_custom_iteration_calls_the_actual_step_and_preserves_abort_state() {
    executes(
        r#"
use ril/iter
var calls=0
eff Stop{now()->()}
fn step(state:int)->Iter::Step<int,int> &{mut calls}{
    calls+=1
    if state>=1{Iter::Step::Done}else{Iter::Step::Yielded(5,state+1)}
}
fn aborting_step(state:int)->Iter::Step<int,int> @Stop &{mut calls}{
    calls+=1
    Stop::now()
    Iter::Step::Yielded(9,state+1)
}
pub fn test_native() &{mut calls}{
    let source:Iter::Source<int,int>=.{step:step}
    let mut cursor=Iter::cursor(0)
    assert(Iter::pull(mut cursor,source)==Some(5))
    assert(Iter::pull(mut cursor,source)==None)
    assert(Iter::pull(mut cursor,source)==None && calls==2)
    let aborting:Iter::Source<int,int>=.{step:aborting_step}
    let mut unchanged=Iter::cursor(3)
    let answer={with Stop::now()->7;Iter::pull(mut unchanged,aborting);99}
    assert(answer==7 && calls==3 && unchanged.state==3 && !unchanged.ended)
}
"#,
    );
}

#[test]
fn explicit_map_and_take_construct_lazily_and_keep_the_successor_state() {
    executes(
        r#"
use ril/iter
var calls=0
fn double(number:int)->int &{mut calls}{calls+=1;number*2}
pub fn test_native() &{mut calls}{
    let source=Iter::indexed([10,20])
    let mapped=Iter::map(source,double)
    assert(calls==0)
    assert(mapped.step(0) is Iter::Step::Yielded(20,1))
    assert(calls==1)
    let stopped=Iter::take(mapped,0)
    assert(stopped.step((0,0)) is Iter::Step::Done)
    assert(calls==1)
    let limited=Iter::take(mapped,1)
    assert(limited.step((0,0)) is Iter::Step::Yielded(20,(1,1)))
    assert(limited.step((1,1)) is Iter::Step::Done && calls==2)
}
"#,
    );
}

#[test]
fn explicit_take_validates_negative_count_and_invalid_consumed_state_before_pulling() {
    for state in ["(0,-1)", "(0,3)"] {
        let report = execution(&format!(
            r#"
use ril/iter
fn uncalled(state:int)->Iter::Step<int,int>{{panic("underlying step must not execute")}}
pub fn test_native(){{
    let source:Iter::Source<int,int>=.{{step:uncalled}}
    let limited=Iter::take(source,2)
    let _=limited.step({state})
}}
"#,
        ));
        assert_eq!(report["runtime"], "language-panic", "{report}");
        assert!(
            report["message"].as_str().unwrap().contains("consumed"),
            "{report}"
        );
    }
    let report = execution(
        r#"
use ril/iter
pub fn test_native(){let _=Iter::take(Iter::indexed([1]),-1)}
"#,
    );
    assert_eq!(report["runtime"], "language-panic", "{report}");
    assert!(
        report["message"]
            .as_str()
            .unwrap()
            .contains("negative take"),
        "{report}"
    );
}

#[test]
fn exported_opaque_returned_closures_keep_their_contract_through_aliases_and_higher_order_calls() {
    let report = execution_project(
        r#"
use token
pub fn test_native(){
    let action=Token::make()
    let first:fn()->Token::Value=action
    let alias:fn()->Token::Value=first
    assert(Array::map([1,2],\number->Token::reveal(alias())+number)==[8,9])
}
"#,
        &[(
            "token.ril",
            "pub opaque type Value=int\npub type Action=fn()->Value\npub fn make()->Action{\\->7}\npub fn reveal(value:Value)->int{value}",
        )],
    );
    assert_eq!(report["runtime"], "returned-unit", "{report}");
    assert_eq!(report["exit"], 0, "{report}");
}

#[test]
fn generic_multi_payload_aliases_keep_the_actual_variant_and_values_in_higher_order_calls() {
    executes(
        r#"
type Cell={value:int}
type Bundle<T>{Empty,Pair(T,T)}
type Alias<T>=Bundle<T>
fn wrap(flag:bool,left:Cell,right:Cell)->Alias<Cell>{
    if flag{Bundle::Empty}else{Bundle::Pair(left,right)}
}
pub fn test_native(){
    let left=Cell.{value:7}
    let right=Cell.{value:9}
    let variants=[wrap(true,left,right),wrap(false,left,right)]
    assert(variants[0] is Bundle::Empty)
    let values=Array::map(variants,\value->match value{
        Bundle::Empty->0,
        Bundle::Pair(first,second)->first.value*10+second.value
    })
    assert(values==[0,79])
}
"#,
    );
}

#[test]
fn explicit_iteration_collects_and_filters_a_custom_source_from_dynamic_states() {
    executes(
        r#"
use ril/iter
var step_calls=0
fn step(state:int)->Iter::Step<int,int> &{mut step_calls}{
    step_calls+=1
    if state>=5{Iter::Step::Done}else{Iter::Step::Yielded(state*10,state+1)}
}
fn collect_from(state:int)->[]int &{mut step_calls}{
    let source:Iter::Source<int,int>=.{step:step}
    Iter::collect(state,source)
}
fn filtered_from(state:int,limit:int)->[]int &{mut step_calls}{
    let source:Iter::Source<int,int>=.{step:step}
    Iter::collect(state,Iter::filter(source,\number->number>limit))
}
pub fn test_native() &{mut step_calls}{
    assert(collect_from(2)==[20,30,40] && step_calls==4)
    assert(collect_from(5)==[] && step_calls==5)
    assert(filtered_from(0,25)==[30,40] && step_calls==11)
    assert(filtered_from(1,100)==[] && step_calls==16)
}
"#,
    );
}

#[test]
fn explicit_iteration_collects_a_long_tail_and_preserves_a_readonly_fold_accumulator() {
    let items = (0..40)
        .map(|value| value.to_string())
        .collect::<Vec<_>>()
        .join(",");
    executes(
        &r#"
use ril/iter
type Cell={mut count:int}
fn collect_from(state:int)->[]int{Iter::collect(state,Iter::indexed([ITEMS]))}
fn keep_from(state:int,initial:Cell)->Cell{
    Iter::fold(state,Iter::indexed([1,2,3]),initial,\acc,number->{assert(acc.count==7);acc})
}
pub fn test_native(){
    let values=collect_from(0)
    assert(len(values)==40 && values[0]==0 && values[39]==39)
    let tail=collect_from(12)
    assert(len(tail)==28 && tail[0]==12 && tail[27]==39)
    let mut initial=Cell.{count:7}
    let view kept=keep_from(0,initial)
    assert(kept.count==7)
    initial.count=9
    assert(kept.count==9)
}
"#
        .replace("ITEMS", &items),
    );
}

#[test]
fn explicit_iteration_rejects_write_authority_for_readonly_collected_elements_and_fold_results() {
    for (function, body) in [
        (
            "fn gather(items:[]Cell)->[]Cell{Iter::collect(0,Iter::indexed(items))}",
            "let mut cells=[Cell.{count:7}];let mut gathered=gather(cells);gathered[0].count+=1",
        ),
        (
            "fn keep(initial:Cell)->Cell{Iter::fold(0,Iter::indexed([1]),initial,\\acc,number->acc)}",
            "let mut initial=Cell.{count:7};let mut returned=keep(initial);returned.count+=1",
        ),
    ] {
        let source = format!(
            "use ril/iter\ntype Cell={{mut count:int}}\n{function}\npub fn test_native(){{{body}}}"
        );
        let directory = tempfile::tempdir().unwrap();
        let input = directory.path().join("readonly-iteration.ril");
        fs::write(&input, source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_ril"))
            .arg("test")
            .arg(&input)
            .args(["--entry", "test_native", "--json"])
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(report["status"], "rejected", "{report}");
        assert!(
            report["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|diagnostic| {
                    matches!(
                        diagnostic["code"].as_str(),
                        Some("E0520" | "E0522" | "E0528")
                    )
                }),
            "{report}"
        );
    }
}

#[test]
fn binding_alternatives_reject_computed_expected_expressions_before_native_emission() {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("computed-binding-alternatives.ril");
    fs::write(
        &input,
        r#"
var calls=0
fn expected()->int &{mut calls}{calls=calls*10+1;1}
fn other()->int &{mut calls}{calls=calls*10+2;2}
fn choose(subject:(int,int))->int{
    match subject{(expected(),value)|(other(),value)->value,_ -> 99}
}
pub fn test_native(){assert(choose((1,7))==7)}
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(input)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["status"], "rejected", "{report}");
    let computed = report["diagnostics"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|diagnostic| diagnostic["code"] == "E0349")
        .count();
    assert_eq!(computed, 2, "each expected call must be rejected: {report}");
}

#[test]
fn binding_alternatives_install_the_selected_payload_and_evaluate_one_guard() {
    executes(
        r#"
type Pair { Both(int,int) }
type Counter={mut calls:int}
fn choose(value:Pair)->int{
    match value{Pair::Both(x,0)|Pair::Both(0,x)->x,Pair::Both(_,_)->99}
}
fn guarded(value:Pair,mut counter:Counter)->int &mut{
    match value{
        Pair::Both(x,0)|Pair::Both(0,x) if {counter.calls+=1;x<0}->x,
        _->77,
    }
}
fn nested(value:Pair)->int{
    match (value,3){
        (Pair::Both(x,0)|Pair::Both(0,x),offset)->x+offset,
        _->99,
    }
}
pub fn test_native(){
    assert(choose(Pair::Both(11,0))==11)
    assert(choose(Pair::Both(0,22))==22)
    assert(choose(Pair::Both(4,5))==99)
    assert(nested(Pair::Both(0,30))==33)
    let mut counter=Counter.{calls:0}
    assert(guarded(Pair::Both(0,0),mut counter)==77)
    assert(counter.calls==1)
    assert(guarded(Pair::Both(0,-5),mut counter)==-5)
    assert(counter.calls==2)
}
"#,
    );
}

#[test]
fn binding_alternatives_keep_selected_cells_across_guard_and_body_suspension() {
    executes(
        r#"
type Pair { Both(int,int) }
eff Read { get()->int }
fn choose(value:Pair)->int @Read{
    match value{
        Pair::Both(x,0)|Pair::Both(0,x) if Read::get()>0->x+Read::get(),
        _->99,
    }
}
fn decline(value:Pair)->int @Read{
    match value{
        Pair::Both(x,0)|Pair::Both(0,x) if Read::get()<0->x,
        _->55,
    }
}
pub fn test_native(){
    var calls=0
    with Read::get()->{calls+=1;resume 1}
    assert(choose(Pair::Both(11,0))==12)
    assert(choose(Pair::Both(0,22))==23)
    assert(decline(Pair::Both(0,0))==55)
    assert(calls==5)
}
"#,
    );
}

#[test]
fn binding_alternatives_select_payloads_of_distinct_variants() {
    executes(
        r#"
type Choice{Left(int),Right(int)}
fn choose(value:Choice)->int{match value{Choice::Left(x)|Choice::Right(x)->x}}
pub fn test_native(){
    assert(choose(Choice::Left(11))==11)
    assert(choose(Choice::Right(22))==22)
}
"#,
    );
}

#[test]
fn nested_cps_where_functions_capture_later_initializers_and_shared_mutable_cells() {
    executes(
        r#"
eff Read{get()->int}
fn run()->int @Read{
    var count=Read::get()
    step()
    let _=Read::get()
    step()
    count
    where
        fn step()->int &{closure,mut count}{bump();count}
        fn bump() &{closure,mut count}{count+=1}
}
fn defaulted(base:int)->int @Read{
    let _=Read::get()
    add()
    where fn add(value:int=7)->int &{closure,base}{base+value}
}
pub fn test_native(){
    with Read::get()->resume 7
    assert(run()==9)
    assert(run()==9)
    assert(defaulted(30)==37)
}
"#,
    );
}

#[test]
fn nested_cps_where_functions_recur_and_mutually_recur_through_hoisted_cells() {
    executes(
        r#"
eff Read{get()->int}
fn count(value:int)->int @Read{
    let increment=Read::get()
    visit(value)
    where fn visit(value:int)->int &{closure,increment}{
        if value==0{0}else{increment+visit(value-1)}
    }
}
fn alternate(value:int)->int @Read{
    let _=Read::get()
    even(value)
    where
        fn even(value:int)->int{
            if value==0{1}else{odd(value-1)}
        }
        fn odd(value:int)->int{
            if value==0{0}else{1+even(value-1)}
        }
}
pub fn test_native(){
    with Read::get()->resume 1
    assert(count(100)==100)
    assert(alternate(100)==51)
    assert(alternate(99)==49)
}
"#,
    );
}
