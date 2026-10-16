use std::{fs, process::Command};
fn report(source: &str, execute: bool) -> serde_json::Value {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("heap.ril");
    fs::write(&path, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_ril"));
    command
        .arg(if execute { "test" } else { "check" })
        .arg(path)
        .arg("--json");
    if execute {
        command.args(["--entry", "test_native"]);
    }
    let output = command.output().unwrap();
    serde_json::from_slice(&output.stdout).unwrap_or_else(|_| {
        panic!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}
fn executes(source: &str) {
    let report = report(source, true);
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], "returned-unit", "{report}");
}
#[test]
fn the_original_local_handler_comparator_executes() {
    executes(
        r#"
use ril/order
use ril/heap
eff Read{get()->int}
fn compare(left:int,right:int)->Order::Ordering{
    with Read::get()->resume left
    Order::compare_int(Read::get(),right)
}
pub fn test_native(){let mut heap=Heap::new<int>(.{compare:compare});Heap::push(mut heap,2);Heap::push(mut heap,1);assert(Heap::pop(mut heap)==Some(1))}
"#,
    );
}
#[test]
fn parallel_comparison_ties_and_clones_keep_heap_identity() {
    executes(
        r#"
use ril/order
use ril/heap
use ril/parallel
fn compare(left:(int,str),right:(int,str))->Order::Ordering{
    let pair=Parallel::join(\->left.0,\->right.0)
    Order::compare_int(pair.0,pair.1)
}
pub fn test_native(){
    let mut heap=Heap::new<(int,str)>(.{compare:compare})
    assert(Heap::len(heap)==0)
    assert(Heap::peek(heap)==None)
    assert(Heap::pop(mut heap)==None)
    Heap::push(mut heap,(2,"later"))
    Heap::push(mut heap,(1,"first"))
    Heap::push(mut heap,(1,"second"))
    let mut copied=clone(heap)
    assert(Heap::len(copied)==3)
    assert(Heap::peek(heap)==Some((1,"first")))
    assert(Heap::pop(mut heap)==Some((1,"first")))
    assert(Heap::pop(mut heap)==Some((1,"second")))
    assert(Heap::pop(mut heap)==Some((2,"later")))
    assert(Heap::pop(mut heap)==None)
    assert(Heap::pop(mut copied)==Some((1,"first")))
    assert(Heap::len(copied)==2)
}
"#,
    );
}
#[test]
fn comparator_local_cleanup_and_panic_keep_their_native_exit_paths() {
    executes(
        r#"
use ril/order
use ril/heap
use ril/concurrent::{scope,TaskFault}
type Guard={on_close:fn()->()}
eff Read{get()->int}
halt fn clean(){with Read::get()->resume 7;assert(Read::get()==7)}
fn compare(left:int,right:int)->Order::Ordering{
    let scoped guard=Guard.{on_close:clean}
    if left<0{panic("heap comparator panic")}
    Order::compare_int(left,right)
}
pub fn test_native() @Async{
    let result=scope \mut s->{
        let task=s.fork(\->{let mut heap=Heap::new<int>(.{compare:compare});Heap::push(mut heap,1);Heap::push(mut heap,-1)})
        task.join()
    }
    match result{Ok(_)->panic("expected failure"),Err(fault)->assert(fault is TaskFault::Panicked(_))}
}
"#,
    );
}
#[test]
fn captured_and_effectful_comparators_keep_their_static_rejections() {
    for source in [
        "use ril/heap\nuse ril/order\nfn example(){let bias=1;let mut heap=Heap::new<int>(.{compare:\\left,right->Order::compare_int(left+bias,right)});Heap::push(mut heap,1)}",
        "use ril/heap\nuse ril/order\nfn compare(left:int,right:int)->Order::Ordering @Fiber{Fiber::yield();Order::compare_int(left,right)}\nfn example(){let mut heap=Heap::new<int>(.{compare:compare});Heap::push(mut heap,1)}",
        "use ril/heap\nuse ril/order\nvar calls=0\nfn compare(left:int,right:int)->Order::Ordering &{mut calls}{calls+=1;Order::compare_int(left,right)}\nfn example(){let mut heap=Heap::new<int>(.{compare:compare});Heap::push(mut heap,1)}",
    ] {
        let report = report(source, false);
        assert_eq!(report["status"], "rejected", "{report}");
    }
}

#[test]
fn heap_builtin_value_aliases_preserve_the_actual_comparator() {
    executes(
        r#"
use ril/heap
use ril/order
eff Read{get()->int}
fn compare(left:int,right:int)->Order::Ordering{with Read::get()->resume left;Order::compare_int(Read::get(),right)}
fn attempt()->?int{
        let create=Heap::new<int>
        let mut heap=create(.{compare:compare})
        let push=Heap::push
        push(mut heap,2)
        push(mut heap,1)
        Heap::pop(mut heap)
}
pub fn test_native(){assert(attempt()==Some(1))}
"#,
    );
}

#[test]
fn heap_budget_charges_actual_comparisons_and_no_internal_sift_iterations() {
    executes(
        r#"
use ril/heap
use ril/order
fn compare(left:int,right:int)->Order::Ordering{Order::compare_int(left,right)}
fn attempt(limit:int)->?int{
    with Div::exhausted()->None
    Some(Div::budget(limit,\->{
        let mut heap=Heap::new<int>(.{compare:compare})
        Heap::push(mut heap,5);Heap::push(mut heap,3);Heap::push(mut heap,4);Heap::push(mut heap,1);Heap::push(mut heap,2)
        assert(Heap::pop(mut heap)==Some(1));assert(Heap::pop(mut heap)==Some(2));assert(Heap::pop(mut heap)==Some(3));assert(Heap::pop(mut heap)==Some(4));assert(Heap::pop(mut heap)==Some(5))
        7
    }))
}
pub fn test_native(){assert(attempt(12)==None);assert(attempt(13)==Some(7))}
"#,
    );
}

#[test]
fn heap_budget_preserves_local_handler_charges_and_builtin_alias_entries() {
    executes(
        r#"
use ril/heap
use ril/order
eff Read{get()->int}
fn compare(left:int,right:int)->Order::Ordering{with Read::get()->resume left;Order::compare_int(Read::get(),right)}
fn handled(limit:int)->?int{
    with Div::exhausted()->None
    Some(Div::budget(limit,\->{let mut heap=Heap::new<int>(.{compare:compare});Heap::push(mut heap,2);Heap::push(mut heap,1);Heap::pop(mut heap)??0}))
}
fn aliased(limit:int)->?int{
    with Div::exhausted()->None
    Some(Div::budget(limit,\->{let create=Heap::new<int>;let mut heap=create(.{compare:Order::compare_int});let push=Heap::push;push(mut heap,2);push(mut heap,1);Heap::pop(mut heap)??0}))
}
pub fn test_native(){assert(handled(3)==None && handled(4)==Some(1));assert(aliased(1)==None && aliased(2)==Some(1))}
"#,
    );
}

#[test]
fn heap_allocation_and_passive_reads_do_not_execute_the_latent_comparator() {
    executes(
        r#"
use ril/heap
use ril/order
use ril/parallel
fn compare(left:int,right:int)->Order::Ordering{let pair=Parallel::join(\->left,\->right);Order::compare_int(pair.0,pair.1)}
fn attempt()->?int{
    with Div::exhausted()->None
    Some(Div::budget(1,\->{let heap=Heap::new<int>(.{compare:compare});assert(Heap::len(heap)==0);assert(Heap::peek(heap)==None);7}))
}
fn passive_length(heap:Heap::Heap<int>)->int{
    with Div::exhausted()->-1
    Div::budget(1,\->Heap::len(heap))
}
pub fn test_native(){assert(attempt()==Some(7));let heap=Heap::new<int>(.{compare:compare});assert(passive_length(heap)==0)}
"#,
    );
    let report = report(
        "use ril/heap\nuse ril/order\nfn compare(left:int,right:int)->Order::Ordering{loop{}}\nfn example(){with Div::exhausted()->();Div::budget(1,\\->{let heap=Heap::new<int>(.{compare:compare});assert(Heap::len(heap)==0)})}",
        false,
    );
    assert_eq!(report["status"], "rejected", "{report}");
    assert!(
        report["diagnostics"]
            .as_array()
            .unwrap()
            .iter()
            .any(|diagnostic| diagnostic["code"] == "E0534"),
        "{report}"
    );
}
