#![forbid(unsafe_code)]

use std::process::Command;

use ril_driver::{CompileOptions, Driver, OptLevel};
use ril_test::{Unit, VirtualPackage, run_worker};

#[test]
fn large_indexmap_and_utf8_str_metadata_under_gc_stress() -> Result<(), String> {
    let source = r#"
        fn main() @io -> () {
            let mut m: [int: int] = [:]
            var i = 0
            while i < 1000 {
                m[i] = i * 3 + 1
                i += 1
            }
            assert(len(ref m) == 1000)
            assert(m?[0] == Some(1) && m?[500] == Some(1501) && m?[999] == Some(2998))
            -- Update existing key preserves insertion order and length.
            m[500] = 9999
            assert(len(ref m) == 1000 && m?[500] == Some(9999))

            var sum = 0
            let frozen = new m
            for frozen as (k, v) {
                sum += k + v
            }
            assert(sum > 0)

            let ascii = "abcdefghij"
            assert(len(ascii) == 10 && String::at(ascii, 3) == Some(100) && ascii[2..6] == "cdef")
            let utf8 = "a中b文c"
            assert(len(utf8) == 5 && String::at(utf8, 1) == Some(20013) && utf8[1..4] == "中b文")
            println("r4-map-str-ok")
        }
    "#;
    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.insert(pkg.entry.clone(), source.as_bytes().to_vec());
    let tmp = tempfile::tempdir().map_err(|err| err.to_string())?;
    let exe = tmp
        .path()
        .join(format!("r4_map{}", std::env::consts::EXE_SUFFIX));
    Driver
        .with_options(CompileOptions {
            opt_stack_promote: true,
            opt_level: OptLevel::Speed,
        })
        .compile_aot(&pkg, &exe)
        .map_err(|diags| format!("compile failed: {diags:?}"))?;
    let mut cmd = Command::new(&exe);
    cmd.env("RIL_GC_STRESS", "1");
    let output = run_worker(&mut cmd).map_err(|err| err.to_string())?;
    if !output.status.success() {
        return Err(format!(
            "r4_map failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    assert_eq!(output.stdout, b"r4-map-str-ok\n");
    Ok(())
}

#[test]
fn ctl_stack_pool_reuses_stacks_across_many_prompts_under_gc_stress() -> Result<(), String> {
    let source = r#"
        eff Yield {
            ctl emit(v: int) -> ()
        }

        fn main() @io -> () {
            let mut out: []int = []
            var i = 0
            while i < 120 {
                let v = with {
                    ctl Yield::emit = \n, new k -> {
                        Array::push(mut out, n)
                        k()
                    }
                    Yield::emit(i * 2)
                    i * 2
                }
                assert(v == i * 2)
                i += 1
            }
            assert(len(ref out) == 120 && out[0] == 0 && out[119] == 238)
            println("r4-ctl-pool-ok")
        }
    "#;
    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.insert(pkg.entry.clone(), source.as_bytes().to_vec());
    let tmp = tempfile::tempdir().map_err(|err| err.to_string())?;
    let exe = tmp
        .path()
        .join(format!("r4_ctl{}", std::env::consts::EXE_SUFFIX));
    Driver
        .with_options(CompileOptions {
            opt_stack_promote: false,
            opt_level: OptLevel::Speed,
        })
        .compile_aot(&pkg, &exe)
        .map_err(|diags| format!("compile failed: {diags:?}"))?;
    let mut cmd = Command::new(&exe);
    cmd.env("RIL_GC_STRESS", "1");
    let output = run_worker(&mut cmd).map_err(|err| err.to_string())?;
    if !output.status.success() {
        return Err(format!(
            "r4_ctl failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    assert_eq!(output.stdout, b"r4-ctl-pool-ok\n");
    Ok(())
}
