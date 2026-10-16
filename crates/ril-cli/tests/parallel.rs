//! Source-level native parallel completion, ordering, and callback regressions.
use std::{fs, process::Command};

fn executes(source: &str) {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("parallel.ril");
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
fn native_parallel_operations_and_aliases_preserve_element_order() {
    executes(
        r#"
use ril/parallel
pub fn test_native() {
    let map = Parallel::map
    assert(map([1, 2, 3], \n -> n * 2) == [2, 4, 6])
    assert(Parallel::map_bounded([1, 2, 3], 1, \n -> n + 1) == [2, 3, 4])
    assert(Parallel::find([3, 1, 2], \n -> n < 3) == Some(1))
    assert(Parallel::first([3, 1, 2], \n -> n < 3) == Some(1))
    assert(Parallel::any([1, 2], \n -> n == 2))
    assert(Parallel::join(\-> 1, \-> "a") == (1, "a"))
    assert(Parallel::join3(\-> 1, \-> 2, \-> 3) == (1, 2, 3))
    let empty: []int = []
    assert(Parallel::map(empty, \n -> n + 1) == [])
    assert(Parallel::find(empty, \n -> true) == None)
    assert(Parallel::first(empty, \n -> true) == None)
    assert(!Parallel::any(empty, \n -> true))
}
"#,
    );
}

#[test]
fn native_parallel_decisive_match_suppresses_right_panic_and_double_fault() {
    executes(
        r#"
use ril/parallel
type Guard = { on_close: fn() -> () }
pub fn test_native() {
    assert(Parallel::find([0, 1], \n -> { if n == 0 { true } else { panic("right") } }) == Some(0))
    assert(Parallel::first([0, 1], \n -> { if n == 0 { true } else { panic("right") } }) == Some(0))
    assert(Parallel::any([0, 1], \n -> {
        if n == 0 { true } else {
            let scoped guard = Guard.{ on_close: \-> panic("cleanup") }
            panic("right")
        }
    }))
}
"#,
    );
}

#[test]
fn native_parallel_fold_uses_64_element_groups_and_adjacent_merge_levels() {
    executes(
        r#"
use ril/parallel
pub fn test_native() {
    for [0, 1, 63, 64, 65, 128, 129] as size {
        let mut data: []int = []
        for 0..size as index { data !> Array::push(index) }
        let result = Parallel::fold(clone_immut(data), \-> 10, \sum, item -> sum + item, \left, right -> left + right)
        let groups = if size == 0 { 1 } else { (size + 63) / 64 }
        assert(result == groups * 10 + size * (size - 1) / 2)
    }
    let mut data: []int = []
    for 0..257 as index { data !> Array::push(index) }
    let result = Parallel::fold(clone_immut(data), \-> 0, \sum, item -> item, \left, right -> left * 10 + right)
    assert(result == ((63 * 10 + 127) * 10 + (191 * 10 + 255)) * 10 + 256)
}
"#,
    );
}

#[test]
fn native_parallel_preserves_disjoint_writes_and_nested_result_graphs() {
    executes(
        r#"
use ril/parallel
type Cell = { mut count: int }
pub fn test_native() {
    let mut cells = [Cell.{ count: 1 }, Cell.{ count: 2 }]
    cells !> Parallel::for_each(\mut cell -> { cell.count *= 2 })
    assert(cells[0].count == 2 && cells[1].count == 4)
    let mut left = Cell.{ count: 1 }
    let mut right = Cell.{ count: 2 }
    Parallel::join(\-> { left.count += 3 }, \-> { right.count += 4 })
    assert(left.count == 4 && right.count == 6)
    let values = Parallel::map([0, 1, 2], \n -> {
        for 0..1200 as index { let unused = [index, index + 1] }
        [[n, n + 1]]
    })
    assert(values == [[[0, 1]], [[1, 2]], [[2, 3]]])
    assert(Parallel::join(\-> Parallel::map([1, 2], \n -> n + 1), \-> 7) == ([2, 3], 7))
}
"#,
    );
}

#[test]
fn native_parallel_callbacks_handle_local_effects_and_local_budgets() {
    executes(
        r#"
use ril/parallel
eff Read { get() -> int }
fn spin() -> int { loop {} }
pub fn test_native() {
    let values = Parallel::map([1, 2], \n -> {
        with Read::get() -> resume n
        Read::get() + 1
    })
    assert(values == [2, 3])
    let recovered = Parallel::map([1, 2], \n -> {
        with Div::exhausted() -> n + 10
        Div::budget(3, spin)
    })
    assert(recovered == [11, 12])
}
"#,
    );
}

#[test]
fn native_parallel_faults_keep_pure_order_and_fold_source_index() {
    executes(
        r#"
use ril/parallel
use ril/concurrent::{scope, TaskFault}
type Guard = { on_close: fn() -> () }
pub fn test_native() @Concurrent {
    let mapped = scope \mut s -> {
        let child = s.fork(\-> Parallel::map([0, 1], \n -> {
            if n == 0 { panic("left") } else {
                let scoped guard = Guard.{ on_close: \-> panic("cleanup") }
                panic("right")
            }
        }))
        child.join()
    }
    match mapped {
        Err(TaskFault::Panicked(info)) -> assert(info.message == "left"),
        _ -> panic("map must select the left fault"),
    }
    let folded = scope \mut s -> {
        let child = s.fork(\-> Parallel::fold([0, 1, 2], \-> 0,
            \acc, item -> { if item == 1 { panic("local") }; acc + item },
            \left, right -> left + right))
        child.join()
    }
    match folded {
        Err(TaskFault::Panicked(info)) -> assert(info.message == "local" && info.index == Some(1)),
        _ -> panic("fold must preserve source index"),
    }
    let bounded = scope \mut s -> {
        let child = s.fork(\-> Parallel::map_bounded([1], 0, \n -> panic("callback must not run")))
        child.join()
    }
    match bounded {
        Err(TaskFault::Panicked(info)) -> assert(info.message == "nonpositive bound"),
        _ -> panic("invalid bound must fail before invocation"),
    }
}
"#,
    );
}

#[test]
fn native_parallel_callbacks_carry_their_pure_retained_handler_recipe() {
    executes(
        r#"
use ril/parallel
eff Read { get() -> int }
pub fn test_native() {
    let callback = {
        with Read::get() -> resume 40
        \n: int -> Read::get() + n
    }
    assert(Parallel::map([1, 2], callback) == [41, 42])
    let branch = {
        with Read::get() -> resume 7
        \-> Read::get()
    }
    assert(Parallel::join(branch, \-> 3) == (7, 3))
}
"#,
    );
}

#[test]
fn parallel_named_generic_arguments_evaluate_in_written_order() {
    executes(
        r#"
use ril/parallel
type Trace = { mut value: int }
pub fn test_native() {
    let mut trace = Trace.{ value: 0 }
    let mapped = Parallel::map_bounded<int, int>(
        transform: { trace.value = trace.value * 10 + 1; \n -> n + 1 },
        items: { trace.value = trace.value * 10 + 2; [2] },
        max_concurrency: { trace.value = trace.value * 10 + 3; 1 },
    )
    assert(trace.value == 123 && mapped == [3])
    trace.value = 0
    let folded = Parallel::fold<int, int>(
        merge_acc: { trace.value = trace.value * 10 + 1; \left, right -> left + right },
        fold_local: { trace.value = trace.value * 10 + 2; \acc, item -> acc + item },
        items: { trace.value = trace.value * 10 + 3; [1, 2] },
        init_acc: { trace.value = trace.value * 10 + 4; \-> 10 },
    )
    assert(trace.value == 1234 && folded == 13)
    assert(Parallel::join<int, str>(right: \-> "x", left: \-> 1) == (1, "x"))
}
"#,
    );
}
