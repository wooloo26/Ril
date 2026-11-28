#![forbid(unsafe_code)]

use std::process::Command;

use ril_driver::{CompileOptions, Driver};
use ril_test::{Stage, Unit, VirtualPackage, run_worker};

fn check_aot_equivalence(source: &str, expected_stdout: &str) -> Result<(), String> {
    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.insert(pkg.entry.clone(), source.as_bytes().to_vec());

    let base = Driver.with_options(CompileOptions {
        opt_stack_promote: false,
        ..CompileOptions::default()
    });
    let opt = Driver.with_options(CompileOptions {
        opt_stack_promote: true,
        ..CompileOptions::default()
    });

    let tmp = tempfile::tempdir().map_err(|err| err.to_string())?;
    for (label, compiler) in [("base", &base), ("opt", &opt)] {
        let exe = tmp.path().join(format!("bin_{label}"));
        compiler
            .compile_aot(&pkg, &exe)
            .map_err(|diags| format!("{label} compile failed: {diags:?}"))?;
        let aot = run_worker(&mut Command::new(&exe)).map_err(|err| err.to_string())?;
        if !aot.status.success() {
            return Err(format!(
                "{label} AOT failed: {}",
                String::from_utf8_lossy(&aot.stderr)
            ));
        }
        let stdout = String::from_utf8_lossy(&aot.stdout);
        if stdout != expected_stdout {
            return Err(format!(
                "{label} AOT stdout mismatch: got {stdout:?}, expected {expected_stdout:?}"
            ));
        }
    }
    Ok(())
}

#[test]
fn promoted_nested_records_tuples_arrays_and_tags_eliminate_heap_ops() {
    let source = r#"
use ril/io
type Point = .{ var x: int, var y: int }
type Pair = .{ a: Point, b: Point }
fn main() @io -> () {
    var total = 0
    for 0..50 as i {
        let mut p = Point.{ x: i, y: i + 1 }
        if i % 2 == 0 {
            p.x += p.y
        } else {
            p.y += p.x
        }
        let seg = Pair.{ a: Point.{ x: p.x, y: p.y }, b: Point.{ x: 3, y: 4 } }
        let arr = [seg.a.x, seg.b.y]
        let tag = Some((arr[0], arr[1]))
        match tag {
            Some((u, v)) -> { total += u + v + len(arr) }
            None -> {}
        }
    }
    Io::println(String::inspect(total))
}
"#;
    check_aot_equivalence(source, "2150\n").unwrap();

    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.insert(pkg.entry.clone(), source.as_bytes().to_vec());
    let base_mir = format!(
        "{:#?}",
        Driver
            .with_options(CompileOptions {
                opt_stack_promote: false,
                ..CompileOptions::default()
            })
            .lower(&pkg)
            .unwrap()
    );
    let opt_mir = format!(
        "{:#?}",
        Driver
            .with_options(CompileOptions {
                opt_stack_promote: true,
                ..CompileOptions::default()
            })
            .lower(&pkg)
            .unwrap()
    );
    assert!(base_mir.contains("ril_rt_record"));
    assert!(base_mir.contains("ril_rt_tuple"));
    assert!(base_mir.contains("ril_rt_array"));
    assert!(base_mir.contains("ril_rt_tag"));
    assert!(!opt_mir.contains("ril_rt_record"));
    assert!(!opt_mir.contains("ril_rt_tuple"));
    assert!(!opt_mir.contains("ril_rt_array"));
    assert!(!opt_mir.contains("ril_rt_tag"));
    assert!(!opt_mir.contains("ril_rt_is_tag"));
}

#[test]
fn escaping_and_loop_carried_objects_preserve_identity_and_gc_roots() {
    let source = r#"
use ril/io
type Node = .{ var label: str, var value: int }
fn bump(mut n: Node) -> int {
    n.value += 10
    n.value
}
fn main() @io -> () {
    -- Loop-carried alias must NOT merge distinct iterations' allocations.
    var prev = Node.{ label: "init", value: 0 }
    var sum = 0
    for 1..5 as i {
        let cur = Node.{ label: "step_{i}", value: i }
        sum += prev.value * 10 + cur.value
        prev = cur
    }

    -- Promoted mutable record holding heap strings updated conditionally across allocations.
    let mut box = Node.{ label: "a{0}", value: 1 }
    for 0..8 as i {
        let transient = "iter_{i}"
        if i == 2 {
            box.label = transient
        }
        let _ = "pressure_{i}"
        box.value += 1
    }

    -- Escaping to function call and array keeps heap identity.
    let escaped = {
        let mut e = Node.{ label: "esc", value: 5 }
        let _ = bump(mut e)
        e
    }
    let bumped = escaped.value
    let items = [escaped]
    Io::println("{sum}:{prev.label}:{box.label}:{box.value}:{bumped}:{items[0].value}")
}
"#;
    check_aot_equivalence(source, "70:step_4:iter_2:9:15:15\n").unwrap();
}

#[test]
fn stack_promotion_preserves_compile_diagnostics_identically() {
    let cases = [
        (Unit::Lib, Stage::Type, "fn bad() -> int { \"nope\" }"),
        (
            Unit::Lib,
            Stage::Access,
            "type Cell = .{ var count: int }\nfn bad(ref c: Cell) -> () { c.count += 1 }",
        ),
        (
            Unit::Lib,
            Stage::Access,
            "fn make() -> !<int, str> { Ok(1) }\nfn bad() -> () { let _ = make() }",
        ),
    ];
    let base = Driver.with_options(CompileOptions {
        opt_stack_promote: false,
        ..CompileOptions::default()
    });
    let opt = Driver.with_options(CompileOptions {
        opt_stack_promote: true,
        ..CompileOptions::default()
    });
    for (unit, stage, source) in cases {
        let mut pkg = VirtualPackage::new(unit);
        pkg.insert(pkg.entry.clone(), source.as_bytes().to_vec());
        let base_diags = base.check(&pkg, stage).result.diagnostics;
        let opt_diags = opt.check(&pkg, stage).result.diagnostics;
        assert!(!base_diags.is_empty());
        assert_eq!(base_diags, opt_diags);
    }
}
