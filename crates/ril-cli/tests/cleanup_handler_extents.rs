//! Existing named cleanup actions use the still-live protected handler extent.
use std::{
    fs,
    process::{Command, Stdio},
    time::{Duration, Instant},
};

fn execution(source: &str) -> (std::process::ExitStatus, String) {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("handler_extent.ril");
    let executable = directory.path().join(if cfg!(windows) {
        "handler_extent.exe"
    } else {
        "handler_extent"
    });
    fs::write(&input, source).unwrap();
    let built = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("build")
        .arg(&input)
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
    let errors = directory.path().join("stderr");
    let mut child = Command::new(executable)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(fs::File::create(&errors).unwrap())
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(8);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("handler cleanup did not reach its continuation");
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    (status, fs::read_to_string(errors).unwrap())
}

fn executes(source: &str) {
    let (status, errors) = execution(source);
    assert!(status.success(), "{errors}");
}

#[test]
fn normal_protected_cleanup_uses_the_caller_handler_for_an_existing_function() {
    executes(
        r#"
eff Close { run() -> int }
type Guard = { on_close: fn() -> () }
var trace = 0
fn close() @Close &{mut trace} { trace = Close::run() }
pub fn main() &{mut trace} {
    { with Close::run() -> resume 7; let scoped guard = Guard.{on_close: close} }
    assert(trace == 7)
}
"#,
    );
}

#[test]
fn a_caller_handler_arm_created_during_cleanup_outlives_the_resumed_body() {
    executes(
        r#"
eff Tick { first() -> (), second() -> () }
type Guard = { on_close: fn() -> () }
var trace = 0
fn mark(value: int) &{mut trace} { trace = trace * 10 + value }
fn close() @Tick &{mut trace} { mark(2); Tick::second() }
fn remaining() &{mut trace} { mark(3) }
fn first_arm() &{mut trace} { mark(1) }
fn second_arm() &{mut trace} { mark(4) }
pub fn main() &{mut trace} {
    {
        with {
            Tick::first() -> { let scoped arm = Guard.{on_close: first_arm}; resume () },
            Tick::second() -> { let scoped arm = Guard.{on_close: second_arm}; resume () }
        }
        let scoped older = Guard.{on_close: remaining}
        let scoped effectful = Guard.{on_close: close}
        Tick::first()
    }
    assert(trace == 2341)
}
"#,
    );
}

#[test]
fn caller_handler_abort_during_cleanup_retires_the_abandoned_exit() {
    executes(
        r#"
eff Tick { first() -> (), second() -> () }
type Guard = { on_close: fn() -> () }
var trace = 0
fn mark(value: int) &{mut trace} { trace = trace * 10 + value }
fn close() @Tick &{mut trace} { mark(2); Tick::second(); panic("abandoned cleanup resumed") }
fn remaining() &{mut trace} { mark(3) }
fn first_arm() &{mut trace} { mark(1) }
pub fn main() &{mut trace} {
    {
        with {
            Tick::first() -> { let scoped arm = Guard.{on_close: first_arm}; resume () },
            Tick::second() -> ()
        }
        let scoped older = Guard.{on_close: remaining}
        let scoped effectful = Guard.{on_close: close}
        Tick::first()
    }
    assert(trace == 231)
}
"#,
    );
}

#[test]
fn a_handler_arms_cleanup_uses_its_outer_handler_mask() {
    executes(
        r#"
eff Read { get() -> int }
type Guard = { on_close: fn() -> () }
var trace = 0
fn close() @Read &{mut trace} { trace = trace * 10 + Read::get() }
pub fn main() &{mut trace} {
    with Read::get() -> resume 7
    {
        with Read::get() -> { let scoped guard = Guard.{on_close: close}; resume 1 }
        assert(Read::get() == 1)
    }
    assert(trace == 7)
}
"#,
    );
}

#[test]
fn aborting_an_inner_body_keeps_the_protected_cleanup_handler_live() {
    executes(
        r#"
eff Close { run() -> int }
eff Stop { now() -> int }
type Guard = { on_close: fn() -> () }
var trace = 0
fn close() @Close &{mut trace} { trace = Close::run() }
fn stopped() -> int &{mut trace} {
    with Close::run() -> resume 7
    with Stop::now() -> 42
    let scoped guard = Guard.{on_close: close}
    Stop::now()
}
pub fn main() &{mut trace} {
    assert(stopped() == 42)
    assert(trace == 7)
}
"#,
    );
}

#[test]
fn an_aborting_handler_stays_live_for_its_remaining_protected_cleanup() {
    executes(
        r#"
eff Close { run() -> () }
type Guard = { on_close: fn() -> () }
var trace = 0
fn mark(value: int) &{mut trace} { trace = trace * 10 + value }
fn close() @Close &{mut trace} { mark(2); Close::run(); panic("abandoned cleanup resumed") }
fn remaining() &{mut trace} { mark(3) }
pub fn main() &{mut trace} {
    {
        with Close::run() -> mark(1)
        let scoped older = Guard.{on_close: remaining}
        let scoped effectful = Guard.{on_close: close}
        Close::run()
        panic("abandoned protected body resumed")
    }
    assert(trace == 1213)
}
"#,
    );
}

#[test]
fn interleaved_handler_owners_preserve_the_inner_arm_suffix_and_cleanup() {
    executes(
        r#"
eff Inner { run() -> () }
eff Outer { run() -> () }
type Guard = { on_close: fn() -> () }
var trace = 0
fn mark(value: int) &{mut trace} { trace = trace * 10 + value }
fn close() @Outer &{mut trace} { mark(2); Outer::run(); mark(3) }
fn inner_arm() &{mut trace} { mark(7) }
fn outer_arm() &{mut trace} { mark(5) }
pub fn main() &{mut trace} {
    {
        with Outer::run() -> { let scoped arm = Guard.{on_close: outer_arm}; resume () }
        {
            with Inner::run() -> {
                let scoped arm = Guard.{on_close: inner_arm}
                let answer = resume ()
                mark(6)
                answer
            }
            let scoped guard = Guard.{on_close: close}
            Inner::run()
            mark(1)
        }
    }
    assert(trace == 123675)
}
"#,
    );
}

#[test]
fn final_panic_closes_an_arm_created_after_cleanup_started() {
    let source = r#"
eff Close { run() -> () }
type Guard = { on_close: fn() -> () }
var trace = 0
fn mark(value: int) &{mut trace} { trace = trace * 10 + value }
fn close() @Close &{mut trace} { mark(2); Close::run() }
fn arm_close() &{mut trace} { mark(1) }
fn observe() &{trace} { assert(trace == 21) }
fn failing() &{mut trace} {
    with Close::run() -> { let scoped arm = Guard.{on_close: arm_close}; ARM_RESULT }
    let scoped guard = Guard.{on_close: close}
    panic("original body panic")
}
pub fn main() &{mut trace} {
    let scoped observer = Guard.{on_close: observe}
    failing()
}
"#;
    for arm in ["resume ()", "()"] {
        let source = source.replace("ARM_RESULT", arm);
        let (status, errors) = execution(&source);
        assert!(!status.success(), "the original panic was discarded: {arm}");
        assert_eq!(errors.trim(), "original body panic", "arm: {arm}");

        // A second run makes observer execution externally observable. Skipping
        // its activation would otherwise leave the original panic unchanged.
        let source = source.replace(
            "assert(trace == 21)",
            "assert(trace == 21); panic(\"outer observer ran\")",
        );
        let (status, errors) = execution(&source);
        assert!(!status.success());
        assert_eq!(
            errors.trim(),
            "double fault: original body panic; cleanup: outer observer ran",
            "arm: {arm}",
        );
    }
}

#[test]
fn concurrent_cancellation_closes_deferred_arms_before_recovery() {
    executes(
        r#"
use ril/concurrent::{scope, TaskFault}
eff Read { get() -> int }
type Guard = { on_close: fn() -> () }
var trace = 0
fn mark(value: int) &{mut trace} { trace = trace * 10 + value }
fn body_close() &{mut trace} { mark(1) }
fn arm_close() &{mut trace} { mark(2) }
fn fail_child() { panic("child") }
pub fn main() @Async &{mut trace} {
    let result = scope \mut s -> {
        with Read::get() -> { let scoped arm = Guard.{on_close: arm_close}; resume 7 }
        let scoped guard = Guard.{on_close: body_close}
        assert(Read::get() == 7)
        s.fork(fail_child)
        loop { Fiber::yield() }
        Ok()
    }
    assert(result is Err(TaskFault::Panicked(_)))
    assert(trace == 12)
    { with Read::get() -> resume 9; assert(Read::get() == 9) }
    let healthy = scope \mut s -> { let task = s.fork(\-> 42); task.join() }
    assert(healthy is Ok(42))
}
"#,
    );
}
