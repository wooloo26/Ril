use ril_compiler::{CompilationOutcome, Session};

fn accepted(source: &str) {
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    ril_compiler::lower::lower_core(&verified).unwrap();
}

#[test]
fn cancelled_diverging_body_has_a_checked_recovery_continuation() {
    accepted(
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

#[test]
fn prefix_reference_replacement_is_explicitly_unproved_even_if_restored_later() {
    let source = r#"
use ril/concurrent
fn entry() @Async {
    let original = [1]
    var retained = original
    let result = Concurrent::scope \mut s -> {
        s.fork(\->panic("child"))
        retained = [2]
        Fiber::yield()
        retained = original
        Ok()
    }
    assert(result is Ok() || result is Err(_))
    assert(retained[0] == 1)
}
"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::NotImplemented { reason } if reason.to_string().contains("prefix heap transfer")),
        "{outcome:?}"
    );
}

#[test]
fn caller_result_inspection_after_a_cancellation_point_is_not_guaranteed() {
    let source = r#"
use ril/concurrent
fn entry() @Async {
    let old: Result<int,str> = Ok(1)
    let result = Concurrent::scope \mut s -> {
        s.fork(\->panic("child"))
        Fiber::yield()
        assert(old is Ok(_))
        Ok()
    }
    assert(result is Ok() || result is Err(_))
}

"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected {diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720")),
        "{outcome:?}"
    );
    accepted(&source.replace(
        "let result = Concurrent::scope",
        "assert(old is Ok(_))\nlet result = Concurrent::scope",
    ));
}

#[test]
fn prefix_certificate_includes_cleanup_callee_and_handler_reference_writes() {
    for body in [
        "let scoped mut guard=Guard.{on_close:\\->{retained=[2];retained=original}};loop{Fiber::yield()};Ok()",
        "let mut change=\\->{retained=[2];retained=original};change();Ok()",
        "with Step::run()->{retained=[2];retained=original;resume ()};Step::run();Ok()",
    ] {
        let source = format!(
            r#"
use ril/concurrent
eff Step {{ run()->() }}
type Guard={{mut on_close:fn()->()}}
fn entry() @Async {{
    let original=[1]
    var retained=original
    let result=Concurrent::scope \mut s->{{s.fork(\->panic("child"));{body}}}
    assert(result is Ok() || result is Err(_))
    assert(retained[0]==1)
}}
"#
        );
        let outcome = Session::new(source.into_bytes()).check();
        assert!(
            matches!(&outcome,CompilationOutcome::NotImplemented {reason} if reason.to_string().contains("prefix heap transfer")),
            "{body}: {outcome:?}"
        );
    }
}

#[test]
fn recovered_cancellation_produces_a_real_result_inspection_duty() {
    let source = r#"use ril/concurrent
fn entry() @Async {let ignored=Concurrent::scope \mut s->{s.fork(\->panic("child"));loop{Fiber::yield()};Ok()}}"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720")),
        "{outcome:?}"
    );
}

#[test]
fn cleanup_inspection_needs_an_exit_proof_instead_of_a_language_rejection() {
    let source = r#"use ril/concurrent
type Guard={on_close:fn()->()}
fn entry() @Async {
    let old:Result<int,str>=Ok(1)
    let result=Concurrent::scope \mut s->{
        let scoped guard=Guard.{on_close:\->assert(old is Ok(_))}
        s.fork(\->panic("child"))
        loop{Fiber::yield()}
        Ok()
    }
    assert(result is Err(_))
}"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::NotImplemented{reason}if reason.to_string().contains("per-prefix cleanup replay")),
        "{outcome:?}"
    );
}

#[test]
fn a_named_literal_body_does_not_hide_a_panicking_default() {
    let source = r#"use ril/concurrent
eff Stop{now()->()}
fn action(value:int=panic("default"))->int{1}
fn entry() @Concurrent {
    with Stop::now()->()
    let result=Concurrent::scope \mut s->{s.fork(action);Stop::now();Ok()}
    assert(result is Ok())
}"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::NotImplemented{reason}if reason.to_string().contains("separate per-exit targets")),
        "{outcome:?}"
    );
}

#[test]
fn child_private_recency_does_not_change_the_parent_cancellation_projection() {
    use ril_compiler::{CheckOptions, session::ProjectSource};
    let source = r#"
use foreign
use ril/concurrent::{scope, TaskFault}
pub fn test_native() @Concurrent {
    let result = scope \mut s -> {
        let child = s.fork(\-> Foreign::apply(1, \number -> panic("callback panic")))
        child.join()
    }
    match result {
        Err(TaskFault::Panicked(info)) -> assert(info.message == "callback panic"),
        _ -> panic("callback fault was replaced"),
    }
}
"#;
    let verified = Session::with_project(
        "virtual/main.ril".into(),
        vec![
            ProjectSource {
                path: "virtual/main.ril".into(),
                bytes: source.as_bytes().to_vec(),
            },
            ProjectSource {
                path: "virtual/foreign.d.ril".into(),
                bytes: b"pub fn apply(value: int, callback: fn(int) -> int) -> int @{} &{}"
                    .to_vec(),
            },
        ],
        CheckOptions::default(),
    )
    .unwrap()
    .verify()
    .unwrap();
    ril_compiler::lower::lower_core(&verified).unwrap();
}

#[test]
fn unrelated_local_recency_is_allowed_but_external_origins_still_require_transport() {
    accepted(
        r#"use ril/concurrent
fn create()->[]int{[1] |> Array::map(\value -> value)}
fn entry() @Concurrent {
    let result=Concurrent::scope \mut s->{
        let child=s.fork(\->panic("child"))
        let first=create()
        let second=create()
        assert(first[0]==second[0])
        child.join()
    }
    assert(result is Err(_))
}"#,
    );
    let source = r#"use ril/concurrent
fn create()->[]int{[1] |> Array::map(\value -> value)}
fn entry() @Concurrent {
    let outside=create()
    let result=Concurrent::scope \mut s->{
        s.fork(\->panic("child"))
        let fresh=create()
        assert(fresh[0]==1)
        Ok()
    }
    assert(result is Ok() || result is Err(_))
    assert(outside[0]==1)
}"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::NotImplemented{reason}if reason.to_string().contains("prefix identity transport")),
        "{outcome:?}"
    );
}

#[test]
fn joined_child_panic_is_a_normal_result_with_an_inspection_duty() {
    let source = r#"use ril/concurrent
fn entry() @Concurrent {
    let result=Concurrent::scope \mut s->{
        let child=s.fork(\->panic("child"))
        child.join()
    }
}
"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
        "{outcome:?}"
    );
    accepted(&source.replace("    }\n}", "    }\n    assert(result is Err(_))\n}"));
}

#[test]
fn cancelled_waits_have_a_normal_error_exit_even_with_a_parent_panic_sentinel() {
    accepted(
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
    for operation in [
        "let result=Io::stdin_read(1);assert(result is Ok(_))",
        "print(\"blocked\")",
        "println(\"blocked\")",
        "let result=File::read_bytes(Path::from_string(\"blocked\"));assert(result is Ok(_))",
    ] {
        accepted(&format!(
            r#"
use ril/concurrent::{{scope,TaskFault}}
use ril/io
use ril/file
use ril/path
use ril/time
pub fn main() @Async {{
    let result=scope \mut s->{{
        s.fork(\->{{Time::sleep(Time::duration_nanos(100000000i64));panic("child")}})
        {operation}
        panic("blocked operation resumed")
        Ok()
    }}
    assert(result is Err(TaskFault::Panicked(_)))
}}
"#
        ));
    }
}

#[test]
fn a_parent_panic_cannot_waive_the_cancellation_paths_caller_result() {
    let source = r#"use ril/concurrent
fn entry() @Async {
    let old:Result<int,str>=Ok(1)
    let result=Concurrent::scope \mut s->{
        s.fork(\->panic("child"))
        Fiber::yield()
        assert(old is Ok(_))
        panic("parent path")
    }
    assert(result is Err(_))
}
"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720")),
        "{outcome:?}"
    );
    accepted(&source.replace(
        "    assert(result is Err(_))",
        "    assert(result is Err(_))\n    assert(old is Ok(_))",
    ));
}

#[test]
fn parent_panic_does_not_bypass_a_changed_external_prefix_graph() {
    let source = r#"use ril/concurrent
fn entry() @Async {
    let original=[1]
    var retained=original
    let result=Concurrent::scope \mut s->{
        s.fork(\->panic("child"))
        retained=[2]
        Fiber::yield()
        retained=original
        panic("parent path")
    }
    assert(result is Err(_))
    assert(retained[0]==1)
}"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::NotImplemented{reason}if reason.to_string().contains("prefix heap transfer")),
        "{outcome:?}"
    );
}
