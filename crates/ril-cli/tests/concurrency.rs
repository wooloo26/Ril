//! Source regressions for structured native task boundaries and channel waits.
use std::{fs, process::Command};

fn executes(source: &str) {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("concurrency.ril");
    fs::write(&input, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&input)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], "returned-unit", "{report}");
    assert_eq!(report["exit"], 0, "{report}");
}

#[test]
fn native_scope_joins_children_and_preserves_nested_business_results() {
    executes(
        r#"
use ril/concurrent::{scope, TaskFault}
pub fn test_native() @Concurrent {
    let result = scope \mut s -> {
        let first = s.fork(\-> 42)
        let second = s.fork(\-> { let result: Result<int, str> = Err("business"); result })
        assert(first.join()? == 42)
        let result = second.join()?
        Ok(result)
    }
    match result { Ok(value) -> assert(value is Err("business")), Err(_) -> panic("task fault") }
}
"#,
    );
}

#[test]
fn native_scope_contains_unjoined_child_panics_and_cleanup_double_faults() {
    executes(
        r#"
use ril/concurrent::{scope, TaskFault}
type Guard = { on_close: fn() -> () }
pub fn test_native() @Concurrent {
    let panicked = scope \mut s -> { s.fork(\-> panic("child")); Ok() }
    assert(panicked is Err(TaskFault::Panicked(_)))
    let doubled = scope \mut s -> {
        s.fork(\-> { let scoped guard = Guard.{ on_close: \-> panic("cleanup") }; panic("body") })
        Ok()
    }
    assert(doubled is Err(TaskFault::DoubleFaultFatal(_)))
    let healthy = scope \mut s -> { let child = s.fork(\-> 7); child.join() }
    assert(healthy is Ok(7))
}
"#,
    );
}

#[test]
fn native_scope_keeps_body_handlers_and_child_local_handlers() {
    executes(
        r#"
use ril/concurrent::{scope, TaskFault}
eff Read { get() -> int }
pub fn test_native() @Concurrent {
    with Read::get() -> resume 40
    let result = scope \mut s -> {
        let base = Read::get()
        let child = s.fork(\-> { with Read::get() -> resume 2; Read::get() })
        Ok(base + child.join()?)
    }
    assert(result is Ok(42))
}
"#,
    );
}

#[test]
fn native_scope_body_abort_preserves_the_outer_answer_and_cleanup_order() {
    executes(
        r#"
use ril/concurrent::{scope, TaskFault}
eff Stop { now() -> int }
type Guard = { on_close: fn() -> () }
var trace = 0
fn close_body() &{mut trace} { trace = trace * 10 + 1 }
fn close_arm() &{mut trace} { trace = trace * 10 + 2 }
pub fn test_native() @Concurrent &{mut trace} {
    let answer = {
        with Stop::now() -> { let scoped guard = Guard.{ on_close: close_arm }; 9 }
        let result = scope \mut s -> {
            let scoped guard = Guard.{ on_close: close_body }
            let child = s.fork(\-> 1)
            let _ = Stop::now()
            let joined = child.join()
            assert(joined is Ok(1))
            Ok()
        }
        assert(result is Ok())
        100
    }
    assert(answer == 9 && trace == 21)
    let healthy = scope \mut s -> { let child = s.fork(\-> 7); child.join() }
    assert(healthy is Ok(7))
}
"#,
    );
}

#[test]
fn native_bound_task_methods_remain_first_class() {
    executes(
        r#"
use ril/concurrent::{scope, TaskFault}
pub fn test_native() @Concurrent {
    let result = scope \mut s -> {
        let fork = s.fork
        let child = fork(\-> 9)
        var evaluations = 0
        let join = ({ evaluations += 1; child }).join
        assert(evaluations == 1)
        let result = join()
        assert(evaluations == 1)
        result
    }
    assert(result is Ok(9))
}
"#,
    );
}

#[test]
fn native_channels_preserve_fifo_and_drained_close() {
    executes(
        r#"
use ril/concurrent::{scope, TaskFault}
use ril/concurrent/channel
pub fn test_native() @Async {
    let result = scope \mut s -> {
        let child = s.fork(\-> ())
        let (mut tx, mut rx) = Channel::bounded<int>(2)
        assert((tx !> Channel::send(1)) is Ok())
        assert((tx !> Channel::send(2)) is Ok())
        Channel::close(tx)
        assert((rx !> Channel::recv()) is Ok(1))
        assert((rx !> Channel::recv()) is Ok(2))
        assert((rx !> Channel::recv()) is Err(Channel::ChannelError::Closed))
        child.join()?; Ok()
    }
    assert(result is Ok())
}
"#,
    );
}

#[test]
fn native_detached_receiver_moves_into_a_child() {
    executes(
        r#"
use ril/concurrent::{scope, TaskFault}
use ril/concurrent/channel
pub fn test_native() @Async {
    let result = scope \mut s -> {
        let (mut tx, mut rx) = Channel::bounded<int>(1)
        let ticket = Channel::detach(mut rx)
        let child = s.fork(\-> {
            let mut local = Channel::attach(ticket)
            (local !> Channel::recv()) ?? \_error -> -1
        })
        assert((tx !> Channel::send(8)) is Ok())
        assert(child.join()? == 8)
        Ok()
    }
    assert(result is Ok())
}
"#,
    );
}

#[test]
fn native_child_failure_cancels_a_blocked_receiver_without_resuming_body() {
    executes(
        r#"
use ril/concurrent::{scope, TaskFault}
use ril/concurrent/channel
pub fn test_native() @Async {
    let result: Result<(), TaskFault> = scope \mut s -> {
        let (tx, mut rx) = Channel::bounded<int>(1)
        s.fork(\-> { let local = clone(tx); Channel::close(local); panic("producer") })
        let _ = (rx !> Channel::recv()) ?? \_error -> panic("cancelled wait resumed")
        panic("cancelled body resumed")
    }
    assert(result is Err(TaskFault::Panicked(_)))
}
"#,
    );
}

#[test]
fn native_task_returns_a_detached_endpoint_to_its_creator() {
    executes(
        r#"
use ril/concurrent::{scope, TaskFault}
use ril/concurrent/channel
pub fn test_native() @Async {
    let result = scope \mut s -> {
        let (mut tx, mut rx) = Channel::bounded<int>(1)
        let ticket = Channel::detach(mut rx)
        let child = s.fork(\-> ticket)
        let returned = child.join()?
        let mut local = Channel::attach(returned)
        assert((tx !> Channel::send(17)) is Ok())
        Channel::close(tx)
        assert((local !> Channel::recv()) is Ok(17))
        assert((local !> Channel::recv()) is Err(Channel::ChannelError::Closed))
        Ok()
    }
    assert(result is Ok())
}
"#,
    );
}

#[test]
fn native_child_termination_closes_its_local_sender_authority() {
    executes(
        r#"
use ril/concurrent::{scope, TaskFault}
use ril/concurrent/channel
pub fn test_native() @Async {
    let result = scope \mut s -> {
        let (tx, mut rx) = Channel::bounded<int>(1)
        let child = s.fork(\-> {
            let mut local = clone(tx)
            assert((local !> Channel::send(23)) is Ok())
        })
        child.join()?
        Channel::close(tx)
        assert((rx !> Channel::recv()) is Ok(23))
        assert((rx !> Channel::recv()) is Err(Channel::ChannelError::Closed))
        Ok()
    }
    assert(result is Ok())
}
"#,
    );
}
