#![forbid(unsafe_code)]

use std::process::Command;

use ril_driver::{CompileOptions, Driver};
use ril_test::{Unit, VirtualPackage, run_worker};

fn run_aot(source: &str, expected_stdout: &str) -> Result<(), String> {
    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.insert(pkg.entry.clone(), source.as_bytes().to_vec());

    let tmp = tempfile::tempdir().map_err(|err| err.to_string())?;
    for (label, opt) in [("base", false), ("opt", true)] {
        let compiler = Driver.with_options(CompileOptions {
            opt_stack_promote: opt,
            ..CompileOptions::default()
        });
        let exe = tmp.path().join(format!("r0_{label}"));
        compiler
            .compile_aot(&pkg, &exe)
            .map_err(|diags| format!("{label} compile failed: {diags:?}"))?;
        let mut cmd = Command::new(&exe);
        cmd.env("RIL_GC_STRESS", "1");
        let output = run_worker(&mut cmd).map_err(|err| err.to_string())?;
        if !output.status.success() {
            return Err(format!(
                "{label} AOT failed: {}",
                String::from_utf8_lossy(&output.stderr)
            ));
        }
        let stdout = String::from_utf8_lossy(&output.stdout);
        if stdout != expected_stdout {
            return Err(format!(
                "{label} stdout mismatch: got {stdout:?}, expected {expected_stdout:?}"
            ));
        }
    }
    Ok(())
}

#[test]
fn b1_defer_unwinds_in_lifo_order_with_sibling_handlers() -> Result<(), String> {
    let source = r#"
eff Log {
    fn tag() -> str
    fn emit(msg: str) -> ()
}

opaque type Res(.{ id: int })

fn close_res(ref r: Res) @Log -> () {
    Log::emit("{Log::tag()}:{r.id}")
}

fn work(fail: bool) @Log -> () {
    let r = Res::(.{ id: 7 })
    defer close_res(ref r)
    with Log::tag = \-> "inner"
    Log::emit(Log::tag())
    if fail {
        panic("boom")
    }
}

fn main() @io -> () {
    with Log::tag = \-> "outer"
    with Log::emit = \msg -> println(msg)
    work(false)
    let outcome = recover_panic(\-> {
        with Log::tag = \-> "outer"
        with Log::emit = \msg -> {
            if msg == "inner:7" {
                panic("wrong handler")
            }
        }
        work(true)
    })
    match outcome {
        Ok(_) -> println("unexpected")
        Err(_) -> println("recovered")
    }
}
"#;
    run_aot(source, "inner\nouter:7\nrecovered\n")
}

#[test]
fn b2_derive_abort_under_panic_preserves_base_and_recovers() -> Result<(), String> {
    let source = r#"
type Box = .{ x: int }

fn main() @io -> () {
    let base = Box.{ x: 10 }
    let res = recover_panic(\-> {
        derive(base, \mut d -> {
            d.x = 99
            panic("abort draft")
        })
    })
    match res {
        Ok(_) -> println("unexpected ok")
        Err(_) -> println(String::inspect(base.x))
    }
}
"#;
    run_aot(source, "10\n")
}

#[test]
fn b3_closure_captures_record_shorthand_and_transitive_local_up() -> Result<(), String> {
    let source = r#"
type Point = .{ x: int, y: int }
type Counter = .{ var n: int }

fn call_twice(f: fn() & -> int) -> int {
    f() + f()
}

fn main() @io -> () {
    var x = 3
    let y = 4
    let ref make = \-> Point.{ x, y }
    x = 10
    let p = make()
    let mut counter = Counter.{ n: 5 }
    counter.n += 1
    let sum = call_twice(\-> read_n())
    println(String::inspect(p.x + p.y + sum))
    where
        fn read_n() &up(ref counter) -> int {
            counter.n
        }
}
"#;
    run_aot(source, "26\n")
}

#[test]
fn b4_closure_captures_destructured_var_bindings() -> Result<(), String> {
    let source = r#"
fn main() @io -> () {
    let (var a, _) = (1, 2)
    let ^mut inc_a = \-> {
        a += 5
        a
    }
    let r1 = inc_a()
    let r2 = match Some(10) {
        Some(var z) -> {
            let ^mut bump = \-> {
                z += 3
                z
            }
            let _ = bump()
            bump()
        }
        None -> 0
    }
    println(String::inspect(r1 + a + r2))
}
"#;
    run_aot(source, "28\n")
}

#[test]
fn b5_eight_arg_closure_does_not_root_raw_arity_or_code_address() -> Result<(), String> {
    let source = r#"
fn main() @io -> () {
    let add8 = \a: int, b: int, c: int, d: int, e: int, f: int, g: int, h: int ->
        a + b + c + d + e + f + g + h
    println(String::inspect(add8(1, 2, 3, 4, 5, 6, 7, 8)))
}
"#;
    run_aot(source, "36\n")
}

#[test]
fn b6_ctl_continuations_abort_cleanly_and_run_lifo_defers() -> Result<(), String> {
    let source = r#"
eff Stop {
    ctl halt(v: int) -> never
}

fn main() @io -> () {
    var acc = 0
    for 0..100 as i {
        var cleaned = 0
        let v = with {
            ctl Stop::halt = \n, new k -> {
                unwind_ctl(new k)
                n
            }
            defer { cleaned += 1 }
            Stop::halt(i)
        }
        assert(cleaned == 1)
        acc += v
    }
    println(String::inspect(acc))
}
"#;
    run_aot(source, "4950\n")
}
