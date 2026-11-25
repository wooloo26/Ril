#![forbid(unsafe_code)]

use std::process::Command;

use ril_base::diag::Code;
use ril_driver::{CompileOptions, Driver};
use ril_test::{Stage, Unit, VirtualPackage, run_worker};

fn run_aot(source: &str, expected_stdout: &str) -> Result<(), String> {
    let mut package = VirtualPackage::new(Unit::Bin);
    package.insert(package.entry.clone(), source.as_bytes().to_vec());
    let tmp = tempfile::tempdir().map_err(|err| err.to_string())?;
    for (label, opt) in [("base", false), ("opt", true)] {
        let compiler = Driver.with_options(CompileOptions {
            opt_stack_promote: opt,
            ..CompileOptions::default()
        });
        let exe = tmp
            .path()
            .join(format!("r2_{label}{}", std::env::consts::EXE_SUFFIX));
        compiler
            .compile_aot(&package, &exe)
            .map_err(|diags| format!("{label} aot compile failed: {diags:?}"))?;
        let mut cmd = Command::new(&exe);
        cmd.env("RIL_GC_STRESS", "1");
        let output = run_worker(&mut cmd).map_err(|err| err.to_string())?;
        if !output.status.success() {
            return Err(format!(
                "{label} aot exited {:?}: {}",
                output.status.code(),
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
fn self_hosted_stdlib_combinators_execute_under_gc_stress() -> Result<(), String> {
    let source = r#"
        fn main() @io -> () {
            assert(Numeric::checked_div(42, 6) == Some(7))
            assert(Numeric::checked_div(42, 0) == None)
            assert(Numeric::checked_rem(43, 6) == Some(1))
            assert(Numeric::checked_rem(43, 0) == None)

            let xs = [10, 20, 30, 40]
            assert(Array::get(xs, 2) == Some(30))
            assert(Array::get(xs, -1) == None)
            assert(Array::at(xs, 4) == None)
            assert(Array::contains(xs, 20))
            assert(!Array::contains(xs, 99))

            let doubled = Array::map(xs, \x -> x * 2)
            assert(len(doubled) == 4 && doubled[0] == 20 && doubled[3] == 80)

            let big = Array::filter(xs, \x -> x >= 25)
            assert(len(big) == 2 && big[0] == 30 && big[1] == 40)

            let raw = Bytes::from_str("ril-std")
            assert(String::from_bytes(raw) == Some("ril-std"))
            println("std-ok")
        }
    "#;
    run_aot(source, "std-ok\n")
}

#[test]
fn top_level_monomorphization_projects_out_unrelated_caller_type_params() -> Result<(), String> {
    let source = r#"
        fn helper(x: int) -> int { x + 1 }
        fn identity<U>(x: U) -> U { x }
        fn wrap<T>(x: T, n: int) -> int {
            let _ = x
            helper(identity(n))
        }
        fn main() @io -> () {
            assert(wrap(1, 10) == 11)
            assert(wrap("hi", 20) == 21)
            assert(wrap(true, 30) == 31)
            println("mono-ok")
        }
    "#;
    let mut package = VirtualPackage::new(Unit::Bin);
    package.insert(package.entry.clone(), source.as_bytes().to_vec());

    let clif = Driver
        .clif(&package)
        .map_err(|diags| format!("clif failed: {diags:?}"))?;
    let helper_count = clif.matches("; pkg/main.ril::helper\n").count();
    let identity_count = clif.matches("; pkg/main.ril::identity\n").count();
    assert_eq!(
        helper_count, 1,
        "non-generic top-level helper must be monomorphized once across wrap<int/str/bool>\n{clif}"
    );
    assert_eq!(
        identity_count, 1,
        "identity<int> must be monomorphized once across wrap<int/str/bool>\n{clif}"
    );

    run_aot(source, "mono-ok\n")
}

#[test]
fn access_diagnostics_attach_secondary_labels_and_help() -> Result<(), String> {
    let mut pkg_e0501 = VirtualPackage::new(Unit::Lib);
    pkg_e0501.insert(
        pkg_e0501.entry.clone(),
        br#"
        fn bad() -> () {
            let x = 1
            x = 2
        }
        "#
        .to_vec(),
    );
    let checked = Driver.check(&pkg_e0501, Stage::Access);
    let diag = checked
        .result
        .diagnostics
        .iter()
        .find(|d| d.code == Some(Code::E0501))
        .ok_or_else(|| format!("expected E0501, got {:?}", checked.result.diagnostics))?;
    assert!(
        !diag.labels().is_empty(),
        "expected secondary declaration label on E0501"
    );
    assert!(
        !diag.help().is_empty(),
        "expected actionable help hint on E0501"
    );

    let mut pkg_e0548 = VirtualPackage::new(Unit::Lib);
    pkg_e0548.insert(
        pkg_e0548.entry.clone(),
        br#"
        type Boxed = .{ var n: int }
        fn bad() -> new Boxed {
            var mut b = Boxed.{ n: 1 }
            b = Boxed.{ n: 2 }
            new b
        }
        "#
        .to_vec(),
    );
    let checked = Driver.check(&pkg_e0548, Stage::Access);
    let diag = checked
        .result
        .diagnostics
        .iter()
        .find(|d| d.code == Some(Code::E0548))
        .ok_or_else(|| format!("expected E0548, got {:?}", checked.result.diagnostics))?;
    assert!(
        !diag.labels().is_empty(),
        "expected secondary var-slot declaration label on E0548"
    );
    Ok(())
}
