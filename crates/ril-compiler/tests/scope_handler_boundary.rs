use ril_compiler::Session;

#[test]
fn immediate_scope_abort_keeps_the_outer_answer_and_creates_no_retained_recipe() {
    let source = r#"use ril/concurrent::{scope, TaskFault}
eff Stop { now() -> int }
type Guard = { on_close: fn() -> () }
var trace = 0
fn close_body() &{mut trace} { trace = trace * 10 + 1 }
fn close_arm() &{mut trace} { trace = trace * 10 + 2 }
fn example() @Concurrent &{mut trace} {
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
}"#;
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    assert!(verified.facts().retained_handlers.is_empty());
}
