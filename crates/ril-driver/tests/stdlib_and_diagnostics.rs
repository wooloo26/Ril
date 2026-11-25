#![forbid(unsafe_code)]

use std::process::Command;

use ril_driver::{CompileOptions, Driver};
use ril_source::diag::Code;
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
            assert(Array::at(xs, 2) == Some(30))
            assert(Array::at(xs, -1) == None)
            assert(Array::at(xs, 4) == None)
            assert(Array::contains(xs, 20))
            assert(!Array::contains(xs, 99))

            let doubled = Array::map(xs, \x -> x * 2)
            assert(len(doubled) == 4 && doubled[0] == 20 && doubled[3] == 80)

            let big = Array::filter(xs, \x -> x >= 25)
            assert(len(big) == 2 && big[0] == 30 && big[1] == 40)

            let raw = String::encode_utf8("ril-std")
            assert(String::decode_utf8(raw) == Some("ril-std"))
            assert(String::decode_utf8(String::encode_utf8("ril-std")) == Some("ril-std"))
            println("std-ok")
        }
    "#;
    run_aot(source, "std-ok\n")
}

#[test]
fn private_stdlib_intrinsics_are_hidden_and_array_get_is_removed() {
    let mut private_call = VirtualPackage::new(Unit::Bin);
    private_call.insert(
        private_call.entry.clone(),
        b"fn main() -> () { let _ = String::raw_encode_utf8(\"hi\") }\n".to_vec(),
    );
    let checked = Driver.check(&private_call, Stage::Hir);
    assert!(
        checked
            .result
            .diagnostics
            .iter()
            .any(|d| d.code == Some(Code::E0201)),
        "expected E0201 private-item error for internal intrinsic, got {:?}",
        checked.result.diagnostics
    );

    let mut removed_get = VirtualPackage::new(Unit::Bin);
    removed_get.insert(
        removed_get.entry.clone(),
        b"fn main() -> () { let _ = Array::get([1, 2], 0) }\n".to_vec(),
    );
    let checked = Driver.check(&removed_get, Stage::Hir);
    assert!(
        checked
            .result
            .diagnostics
            .iter()
            .any(|d| d.code == Some(Code::E0209)),
        "expected E0209 unresolved-member error for removed Array::get, got {:?}",
        checked.result.diagnostics
    );
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

#[test]
fn prelude_real_sums_platform_math_and_removed_aliases() -> Result<(), String> {
    let source = r#"
        use ril/bytes
        use ril/crypto
        use ril/math
        use ril/os
        use ril/platform

        fn check_set_sig(s: Set<int>) -> int { Set::len(s) }

        fn main() @io -> new Result<(), str> {
            let opt: Option<int> = Option::Some(42)
            assert(opt == Some(42))
            let none_val: Option<int> = Option::None
            assert(none_val == None)

            let res: Result<int, str> = Result::Ok(7)
            assert(res == Ok(7))
            let err_val: Result<int, str> = Result::Err("boom")
            assert(err_val == Err("boom"))

            let caught = absorb_panic(\-> { panic("oops"); 1 })
            match caught {
                Result::Ok(_) -> panic("expected panic")
                Result::Err(Panicked(info)) -> assert(panic_message(info) == "oops")
            }

            assert(len(Platform::OS) > 0)
            assert(len(Platform::ARCH) > 0)
            assert(Platform::HAS_OPENAT || !Platform::HAS_OPENAT)

            assert(Math::abs(-9) == 9)
            assert(Math::abs(-2.5) == 2.5)
            assert(Math::min(3, 7) == 3)
            assert(Math::max(3, 7) == 7)
            assert(Math::clamp(15, 0, 10) == 10)
            assert(Math::PI > 3.14 && Math::EULER > 2.71)
            assert(Bytes::len(String::encode_utf8("ab")) == 2)
            let _ = check_set_sig
            println("wave-a-ok")
            Result::Ok()
        }
    "#;
    run_aot(source, "wave-a-ok\n")?;

    for bad in [
        "use ril/fiber\nfn main() @fiber -> () { Fiber::yield() }\n",
        "use ril/fiber\nfn main() @io @fiber -> () { Fiber::sleep(1) }\n",
        "use ril/channel\nfn main() -> () { let _ = Channel::mpsc(1) }\n",
        "fn main() -> () { let _ = Numeric::to_int(1.0) }\n",
        "fn main() -> () { let _ = String::from_bytes(bytes\"a\") }\n",
        "fn main() -> () { let _ = Bytes::from_str(\"a\") }\n",
    ] {
        let mut pkg = VirtualPackage::new(Unit::Bin);
        pkg.insert(pkg.entry.clone(), bad.as_bytes().to_vec());
        let checked = Driver.check(&pkg, Stage::Hir);
        assert!(
            checked
                .result
                .diagnostics
                .iter()
                .any(|d| d.code == Some(Code::E0209)),
            "expected E0209 for removed legacy alias `{bad}`, got {:?}",
            checked.result.diagnostics
        );
    }
    Ok(())
}
