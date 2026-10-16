//! Scope-exit continuations retain lexical cells and initialized global values.
use std::{fs, process::Command};

fn execution(source: &str) -> serde_json::Value {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("cleanup_continuations.ril");
    fs::write(&input, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(input)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["status"], "executed", "{report}");
    report
}
fn executes(source: &str) {
    let report = execution(source);
    assert_eq!(report["runtime"], "returned-unit", "{report}");
}

#[test]
fn cps_global_initializer_publishes_only_top_level_cells_and_keeps_budget_arm_pairs() {
    executes(
        r#"
type Guard = { on_close: fn() -> () }
eff Read { get() -> int }
fn read() -> int @Read { Read::get() }
var shared = { let scoped guard = Guard.{ on_close: \-> () }; 41 }
let SHADOW = { let shared = 7; shared + 1 }
let PAIR = (shared, SHADOW)
let MEASURED = { with Read::get() -> resume 5; with Div::exhausted() -> 0; Div::budget(3, read) }
var count = 3
pub fn test_native() &{mut shared, SHADOW, PAIR, MEASURED, mut count} {
    assert(shared == 41 && SHADOW == 8 && PAIR == (41, 8) && MEASURED == 5)
    count += 1
    shared += 1
    assert(count == 4 && shared == 42)
}
"#,
    );
}

#[test]
fn scoped_defaults_lambdas_and_lifted_functions_keep_their_return_continuations() {
    executes(
        r#"
type Guard = { on_close: fn() -> () }
fn defaulted(value: int = { let scoped guard = Guard.{ on_close: \-> () }; 7 }) -> int { value }
fn nested() -> int {
    local()
    where fn local() -> int { let scoped guard = Guard.{ on_close: \-> () }; 8 }
}
pub fn test_native() {
    let action = \-> { let scoped guard = Guard.{ on_close: \-> () }; 9 }
    assert(defaulted() == 7 && defaulted(1) == 1 && nested() == 8 && action() == 9)
}
"#,
    );
}

#[test]
fn suspending_cleanups_preserve_lifo_replacement_return_next_and_break() {
    executes(
        r#"
eff Read { get() -> int }
type Guard = { mut on_close: fn() -> () }
var trace = 0
fn mark(value: int) &{mut trace} { with Read::get() -> resume value; trace = trace * 10 + Read::get() }
fn early() -> int &{mut trace} { let scoped mut guard = Guard.{on_close: \-> mark(6)}; return 9 }
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
fn effect_abort_finishes_suspending_arm_and_body_cleanups_before_the_outer_answer() {
    executes(
        r#"
eff Read { get() -> int }
eff Stop { now() -> int }
type Guard = { on_close: fn() -> () }
var trace = 0
fn mark(value: int) &{mut trace} { with Read::get() -> resume value; trace = trace * 10 + Read::get() }
fn close_body() &{mut trace} { mark(1) }
fn close_arm() &{mut trace} { mark(2) }
pub fn test_native() &{mut trace} {
    let answer = {
        with Stop::now() -> { let scoped arm = Guard.{on_close: close_arm}; 7 }
        let scoped body = Guard.{on_close: close_body}
        Stop::now()
        panic("abandoned body resumed")
    }
    assert(answer == 7 && trace == 21)
}
"#,
    );
}

#[test]
fn cleanup_local_budgets_and_gc_preserve_pending_results_and_exhaustion_recovery() {
    executes(
        r#"
eff Read { get() -> int }
type Guard = { on_close: fn() -> () }
fn read() -> int @Read { Read::get() }
halt fn clean() {
    let kept = [7]
    for 0..1200 as index { let unused = [index, index + 1] }
    with Read::get() -> resume kept[0]
    with Div::exhausted() -> panic("cleanup local budget was corrupted")
    assert(Div::budget(3, read) == 7)
}
fn returned() -> []int { let scoped guard = Guard.{on_close: clean}; [42] }
fn one() -> int { let scoped guard = Guard.{on_close: clean}; 42 }
fn spin() -> int { let scoped guard = Guard.{on_close: clean}; loop {} }
fn exact() -> ?int { with Div::exhausted() -> None; Some(Div::budget(1, one)) }
fn exhausted() -> ?int { with Div::exhausted() -> None; Some(Div::budget(2, spin)) }
pub fn test_native() { assert(returned() == [42]); assert(exact() == Some(42)); assert(exhausted() == None) }
"#,
    );
}

#[test]
fn cleanup_panic_during_budget_abort_keeps_both_causes_and_prevents_recovery() {
    let report = execution(
        r#"
eff Read { get() -> int }
type Guard = { on_close: fn() -> () }
halt fn clean() { with Read::get() -> resume 7; assert(Read::get() == 7); panic("cleanup panic") }
fn spin() -> int { let scoped guard = Guard.{on_close: clean}; loop {} }
pub fn test_native() { with Div::exhausted() -> panic("recovery must not execute"); let _ = Div::budget(2, spin) }
"#,
    );
    assert_eq!(report["runtime"], "double-fault", "{report}");
    assert_eq!(
        report["cause"]["cleanup"]["message"], "cleanup panic",
        "{report}"
    );
}

#[test]
fn task_cancellation_runs_suspending_cleanup_before_scope_fault_recovery() {
    executes(
        r#"
use ril/concurrent::{scope, TaskFault}
use ril/time
eff Read { get() -> int }
type Guard = { on_close: fn() -> () }
var trace = 0
fn clean() &{mut trace} { with Read::get() -> resume 1; trace += Read::get() }
pub fn test_native() @Async &{mut trace} {
    let result = scope \mut s -> {
        s.fork(\-> { Time::sleep(Time::duration_nanos(50000000i64)); panic("child") })
        let scoped guard = Guard.{on_close: clean}
        loop { Fiber::yield() }
        Ok()
    }
    assert(result is Err(TaskFault::Panicked(_)))
    assert(trace == 1)
}
"#,
    );
}

#[test]
fn global_callable_effects_scopes_and_budgets_select_matching_caller_entries() {
    for (action, expected) in [
        ("\\->{with Read::get()->resume 7;Read::get()}", 7),
        (
            "\\->{loop{last helper() where fn helper()->int{with Read::get()->resume 12;Read::get()}}}",
            12,
        ),
        ("{with Read::get()->resume 8;\\->Read::get()}", 8),
        (
            "\\->{let scoped guard=Guard.{on_close:\\->()};(\\->9)()}",
            9,
        ),
        ("\\->{with Div::exhausted()->-1;Div::budget(1,\\->11)}", 11),
    ] {
        executes(&format!(
            "eff Read{{get()->int}}\ntype Guard={{on_close:fn()->()}}\nlet ACTION={action}\npub fn test_native() &{{ACTION}}{{assert(ACTION()=={expected})}}"
        ));
    }
}
