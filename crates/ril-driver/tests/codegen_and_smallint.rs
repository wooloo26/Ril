#![forbid(unsafe_code)]

use std::process::Command;

use ril_driver::{CompileOptions, Driver, OptLevel};
use ril_test::{Unit, VirtualPackage, run_worker};

#[test]
fn clif_uses_intrusive_root_frame_and_inline_smallint_constants() -> Result<(), String> {
    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.insert(
        pkg.entry.clone(),
        br#"
        fn sum_loop(n: int) -> int {
            var acc = 0
            var i = 0
            while i < n {
                acc = acc + i * 2 - 1
                i = i + 1
            }
            acc
        }
        fn main() -> () {
            assert(sum_loop(100) == 9800)
        }
        "#
        .to_vec(),
    );

    let clif = Driver
        .clif(&pkg)
        .map_err(|diags| format!("clif failed: {diags:?}"))?;
    assert!(
        !clif.contains("ril_rt_roots_push"),
        "stack RootFrame must eliminate ril_rt_roots_push\n{clif}"
    );
    assert!(
        !clif.contains("ril_rt_roots_set"),
        "stack RootFrame must eliminate ril_rt_roots_set\n{clif}"
    );
    assert!(
        !clif.contains("ril_rt_roots_pop"),
        "stack RootFrame must eliminate ril_rt_roots_pop\n{clif}"
    );
    assert!(
        !clif.contains("ril_rt_int_literal"),
        "63-bit SmallInt literals must emit inline iconst, not ril_rt_int_literal\n{clif}"
    );
    Ok(())
}

#[test]
fn smallint_63bit_boundaries_overflow_and_demotion_across_opt_levels() -> Result<(), String> {
    let source = r#"
        fn main() @io -> () {
            let max = 4611686018427387903
            let min = -4611686018427387904
            let big_pos = max + 1
            let big_neg = min - 1
            assert(big_pos - 1 == max)
            assert(big_neg + 1 == min)
            assert(-min == big_pos)
            assert(min * -1 == big_pos)
            assert(min * 1 == min)
            assert(~max == min)
            assert(~min == max)
            assert((max & min) == 0)
            assert((max | min) == -1)
            assert((max ^ min) == -1)
            assert(min < max && max > min && min <= min && max >= max)
            assert(!(max < min))
            assert(big_pos > max && big_neg < min)
            println("r3-smallint-ok")
        }
    "#;
    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.insert(pkg.entry.clone(), source.as_bytes().to_vec());
    let tmp = tempfile::tempdir().map_err(|err| err.to_string())?;
    for (label, opt_level) in [("none", OptLevel::None), ("speed", OptLevel::Speed)] {
        let compiler = Driver.with_options(CompileOptions {
            opt_stack_promote: opt_level != OptLevel::None,
            opt_level,
        });
        let exe = tmp
            .path()
            .join(format!("r3_{label}{}", std::env::consts::EXE_SUFFIX));
        compiler
            .compile_aot(&pkg, &exe)
            .map_err(|diags| format!("{label} compile failed: {diags:?}"))?;
        let mut cmd = Command::new(&exe);
        cmd.env("RIL_GC_STRESS", "1");
        let output = run_worker(&mut cmd).map_err(|err| err.to_string())?;
        if !output.status.success() {
            return Err(format!(
                "{label} failed: {}",
                String::from_utf8_lossy(&output.stderr)
            ));
        }
        assert_eq!(output.stdout, b"r3-smallint-ok\n");
    }
    Ok(())
}

#[test]
fn leaf_rootframe_elision_const_folding_effect_op_ids_and_concat_many() -> Result<(), String> {
    let source = r#"
        eff Counter {
            fn bump(delta: int) -> int
        }

        fn flip(b: bool) -> bool { !b }

        fn folded() -> int {
            let x = 2 + 3 * 4
            if x == 14 { x + 1 } else { 999 }
        }

        fn main() @io -> () {
            assert(flip(true) == false)
            assert(flip(false) == true)
            assert(folded() == 15)
            with Counter::bump = \d -> d + 10
            let v = Counter::bump(5)
            let msg = "v={v},f={folded()},ok={!false}"
            println(msg)
        }
    "#;
    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.insert(pkg.entry.clone(), source.as_bytes().to_vec());

    let clif = Driver
        .clif(&pkg)
        .map_err(|diags| format!("clif failed: {diags:?}"))?;
    let flip_section = clif
        .split("; pkg/main.ril::flip\n")
        .nth(1)
        .and_then(|s| s.split("\n; ").next())
        .ok_or("missing flip function in CLIF")?;
    assert!(
        !flip_section.contains("ss0"),
        "safepoint-free leaf function flip must not allocate a RootFrame\n{flip_section}"
    );
    let folded_section = clif
        .split("; pkg/main.ril::folded\n")
        .nth(1)
        .and_then(|s| s.split("\n; ").next())
        .ok_or("missing folded function in CLIF")?;
    assert!(
        !folded_section.contains("ss0") && folded_section.contains("iconst.i64 31"),
        "folded() must constant-fold to tagged 15 (31) with zero RootFrame\n{folded_section}"
    );
    let mir_text = format!(
        "{:#?}",
        Driver
            .lower(&pkg)
            .map_err(|diags| format!("mir lower failed: {diags:?}"))?
    );
    assert!(
        mir_text.contains("ril_rt_concat_many"),
        "multi-part string interpolation must fuse into ril_rt_concat_many\n{mir_text}"
    );

    let tmp = tempfile::tempdir().map_err(|err| err.to_string())?;
    let exe = tmp
        .path()
        .join(format!("r3b{}", std::env::consts::EXE_SUFFIX));
    Driver
        .with_options(CompileOptions {
            opt_stack_promote: true,
            opt_level: OptLevel::Speed,
        })
        .compile_aot(&pkg, &exe)
        .map_err(|diags| format!("aot compile failed: {diags:?}"))?;
    let mut cmd = Command::new(&exe);
    cmd.env("RIL_GC_STRESS", "1");
    let output = run_worker(&mut cmd).map_err(|err| err.to_string())?;
    if !output.status.success() {
        return Err(format!(
            "r3b failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    assert_eq!(output.stdout, b"v=15,f=15,ok=true\n");
    Ok(())
}
