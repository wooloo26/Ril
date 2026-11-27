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
            assert(Numeric::div(42, 6) == Some(7))
            assert(Numeric::div(42, 0) == None)
            assert(Numeric::rem(43, 6) == Some(1))
            assert(Numeric::rem(43, 0) == None)

            let xs = [10, 20, 30, 40]
            assert(xs?[2] == Some(30))
            assert(xs?[-1] == None)
            assert(xs?[4] == None)
            assert(Array::contains(xs, 20))
            assert(!Array::contains(xs, 99))

            let doubled = Array::map(xs, \x -> x * 2)
            assert(len(doubled) == 4 && doubled[0] == 20 && doubled[3] == 80)

            let big = Array::filter(xs, \x -> x >= 25)
            assert(len(big) == 2 && big[0] == 30 && big[1] == 40)

            assert(Array::fold(xs, 0, \acc, x -> acc + x) == 100)
            assert(Array::any(xs, \x -> x == 30) && !Array::any(xs, \x -> x > 100))
            assert(Array::all(xs, \x -> x > 0) && !Array::all(xs, \x -> x < 30))
            assert(Array::find(xs, \x -> x > 25) == Some(30))
            assert(Array::find(xs, \x -> x > 99) == None)

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
        b"fn main() -> () { let _ = meta Reflect::raw_type_kind(<int>) }\n".to_vec(),
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
        fn take(new b: Boxed) -> int { b.n += 1; b.n }
        fn bad() -> int {
            let mut b = Boxed.{ n: 1 }
            b.n += 1
            take(b)
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
        use ril/math
        use ril/panic as Panic
        use ril/platform

        fn check_set_sig(s: Set<int>) -> int { len(s) }

        fn main() @io -> new Result<(), str> {
            let opt: Option<int> = Option::Some(42)
            assert(opt == Some(42))
            let none_val: Option<int> = Option::None
            assert(none_val == None)

            let res: Result<int, str> = Result::Ok(7)
            assert(res == Ok(7))
            let err_val: Result<int, str> = Result::Err("boom")
            assert(err_val == Err("boom"))

            let caught = Panic::recover(\-> { panic("oops"); 1 })
            match caught {
                Result::Ok(_) -> panic("expected panic")
                Result::Err(Panic::Error::Panicked(info)) -> assert(Panic::message(info) == "oops")
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
            assert(len(String::encode_utf8("ab")) == 2)
            let _ = check_set_sig
            println("wave-a-ok")
            Result::Ok()
        }
    "#;
    run_aot(source, "wave-a-ok\n")?;

    for bad in [
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

#[test]
fn wave_b_stdlib_primitives_set_sort_first_class_and_named_args() -> Result<(), String> {
    let source = r#"
        fn sub_named(left: int, right: int) -> int { left - right }

        fn main() @io -> () {
            -- Array::{pop, insert, remove, sort, clear, len}
            let mut xs = [30, 10, 20]
            Array::sort(mut xs)
            assert(xs == [10, 20, 30])
            Array::insert(mut xs, 1, 15)
            assert(xs == [10, 15, 20, 30])
            assert(Array::remove(mut xs, 2) == Some(20))
            assert(Array::pop(mut xs) == Some(30))
            assert(len(ref xs) == 2)
            Array::clear(mut xs)
            assert(len(ref xs) == 0 && Array::pop(mut xs) == None)

            -- Map::{get, insert, remove, contains, clear, keys, values}
            let mut m: [str: int] = [:]
            Map::insert(mut m, "a", 1)
            Map::insert(mut m, "b", 2)
            assert(len(ref m) == 2)
            assert(Map::contains(ref m, "a") && !Map::contains(ref m, "z"))
            assert(m?["b"] == Some(2))
            assert(Map::keys(ref m) == ["a", "b"])
            assert(Map::values(ref m) == [1, 2])
            assert(Map::remove(mut m, "a") == Some(1))
            assert(Map::remove(mut m, "a") == None)
            Map::clear(mut m)
            assert(len(ref m) == 0)

            -- Set::{empty, from_array, insert, remove, contains, clear, to_array}, clone, ==, for
            let mut s: Set<int> = Set::empty()
            Set::insert(mut s, 10)
            Set::insert(mut s, 20)
            Set::insert(mut s, 10)
            assert(len(ref s) == 2)
            assert(Set::contains(ref s, 10) && !Set::contains(ref s, 99))
            assert(Set::to_array(ref s) == [10, 20])
            let s2 = Set::from_array([20, 10, 20])
            assert(s == s2)
            let s3 = clone(ref s)
            assert(s3 == s2)
            var sum = 0
            for s2 as item {
                sum += item
            }
            assert(sum == 30)
            assert(Set::remove(mut s, 10) && !Set::remove(mut s, 10))
            assert(len(ref s) == 1)
            Set::clear(mut s)
            assert(len(ref s) == 0)

            -- String::split + named args + first-class primitives + indirect named args
            let parts = String::split(separator: ",", text: "alpha,beta,gamma")
            assert(parts == ["alpha", "beta", "gamma"])
            let joined = String::join(separator: "-", parts: parts)
            assert(joined == "alpha-beta-gamma")

            let f_to_f64 = Numeric::to_f64
            let floats = Array::map([1, 2, 3], f_to_f64)
            assert(floats == [1.0, 2.0, 3.0])

            -- BigInt to_f64 overflow returns +-infinity rather than panicking
            let huge = 1 << 2000
            let inf = Numeric::to_f64(huge)
            assert(inf > 1.0e300 && Numeric::to_int_trunc(inf) == None)

            let f_sub: fn(left: int, right: int) -> int = sub_named
            assert(f_sub(right: 3, left: 10) == 7)

            println("wave-b-ok")
        }
    "#;
    run_aot(source, "wave-b-ok\n")?;

    // Unified len() rejects non-LenTarget values and removed module-specific len() fails resolution.
    for (src, code) in [
        (
            "fn main() -> () { let _ = Map::contains(\"abc\", \"a\") }\n",
            Code::E0301,
        ),
        (
            "fn main() -> () { let _ = Array::len([1, 2]) }\n",
            Code::E0209,
        ),
        (
            "fn main() -> () { let _ = len(ref \"abc\") }\n",
            Code::E0401,
        ),
        (
            "fn main() -> () { let _ = String::inspect(ref 42) }\n",
            Code::E0401,
        ),
        (
            "fn main() -> () { let xs = [3, 1, 2]; Array::sort(mut xs) }\n",
            Code::E0520,
        ),
        (
            "fn f(mut xs: []int) -> () { Array::sort(mut xs) }\nfn main() -> () { let mut xs = [1]; f(mut xs) }\n",
            Code::E0510,
        ),
        (
            "fn main() -> () { let mut xs = [true, false]; Array::sort(mut xs) }\n",
            Code::E0327,
        ),
    ] {
        let mut pkg = VirtualPackage::new(Unit::Bin);
        pkg.insert(pkg.entry.clone(), src.as_bytes().to_vec());
        let checked = Driver.check(&pkg, Stage::Access);
        assert!(
            checked
                .result
                .diagnostics
                .iter()
                .any(|d| d.code == Some(code)),
            "expected {code:?} for `{src}`, got {:?}",
            checked.result.diagnostics
        );
    }
    Ok(())
}

#[test]
fn wave_c_soundness_static_checks_narrowing_patterns_and_nominals() -> Result<(), String> {
    let source = r#"
        type UserId(int)
        type Config(.{ host: str = "localhost", port: int = 8080 })
        meta let DEFAULT_CFG = Config::(.{ port: 9000 })

        fn inner_only<T |> InnerTarget>(t: T) -> T { t }
        fn shared_only<T |> SharedObject>(v: T) -> T { v }

        fn narrow_and(x: ?int) -> bool { x != None && x > 5 }
        fn narrow_or(x: ?int) -> bool { x == None || x > 5 }

        fn break_from_let_else(xs: []?int) -> int {
            var i = 0
            while true {
                let Some(v) = xs[i] else { break }
                i += 1
                let _ = v
            }
            i
        }

        fn main() @io -> () {
            -- Nominal wrap inside closure
            let ids = Array::map([1, 2, 3], \x -> UserId::(x))
            assert(inner(ids[0]) == 1 && inner(ids[2]) == 3)

            -- Prelude static checks & helpers
            assert(inner(inner_only(UserId::(4))) == 4)
            assert(shared_only([1, 2]) == [1, 2])
            assert(len("abc") == 3)

            -- Static record defaults evaluated
            assert(DEFAULT_CFG.host == "localhost" && DEFAULT_CFG.port == 9000)

            -- Safe map indexing preserves ??int
            let m: [str: ?int] = ["a": None, "b": Some(7)]
            let got_a: ??int = m?["a"]
            let got_b: ??int = m?["b"]
            let got_c: ??int = m?["c"]
            assert(got_a == Some(None) && got_b == Some(Some(7)) && got_c == None)

            -- Narrowing across && and || + break inside let..else
            assert(narrow_and(Some(10)) && !narrow_and(None))
            assert(narrow_or(None) && narrow_or(Some(10)) && !narrow_or(Some(1)))
            assert(break_from_let_else([Some(1), Some(2), None]) == 2)

            println("wave-c-ok")
        }
    "#;
    run_aot(source, "wave-c-ok\n")?;

    for (src, code) in [
        ("fn main() -> () { let _ = \"abc\"[0] }\n", Code::E0352),
        ("fn main() -> () { let _ = bytes\"abc\"[0] }\n", Code::E0352),
        (
            "fn main() -> () { for \"abc\" as c { let _ = c } }\n",
            Code::E0355,
        ),
        (
            "fn main() -> () { let r = .{ a: 1 }; let i = 0; let _ = r[i] }\n",
            Code::E0324,
        ),
        (
            "fn f(x: int<str>) -> int { x }\nfn main() -> () {}\n",
            Code::E0340,
        ),
        (
            "fn f(x: Option<int, str>) -> () { let _ = x }\nfn main() -> () {}\n",
            Code::E0340,
        ),
        (
            "fn f<T |> SharedObject>(x: T) -> T { x }\nfn main() -> () { let _ = f(1) }\n",
            Code::E0301,
        ),
        (
            "fn f<T |> InnerTarget>(x: T) -> T { x }\nfn main() -> () { let _ = f(1) }\n",
            Code::E0301,
        ),
        ("fn main() -> () { let _ = len(1) }\n", Code::E0301),
        (
            "fn f<T |> LenTarget>(x: T) -> T { x }\nfn main() -> () { let _ = f(1) }\n",
            Code::E0301,
        ),
        (
            "type BadKey { Num(f64) }\nfn f(m: [BadKey: int]) -> () { let _ = m }\nfn main() -> () {}\n",
            Code::E0328,
        ),
        (
            "type Open { A; .. }\nfn f(m: [Open: int]) -> () { let _ = m }\nfn main() -> () {}\n",
            Code::E0328,
        ),
        (
            "type FnSum { Call(fn() -> int) }\nfn f(a: FnSum, b: FnSum) -> bool { a == b }\nfn main() -> () {}\n",
            Code::E0327,
        ),
        (
            "fn main() -> () { match \"hi\" { str[] -> ()\n _ -> () } }\n",
            Code::E0349,
        ),
        (
            "fn main() -> () { let xs = [Some(1)]; for xs as Some(v) { let _ = v } }\n",
            Code::E0345,
        ),
        ("fn main() -> () { while false { 42 } }\n", Code::E0301),
        (
            "fn f(x: ?int) -> () { if x == None { if x != None { () } } }\nfn main() -> () {}\n",
            Code::E0311,
        ),
        (
            "type A { Tag }\ntype B { Tag }\nfn f(a: A) -> () { match a { B::Tag -> ()\n _ -> () } }\nfn main() -> () {}\n",
            Code::E0301,
        ),
        (
            "type U(.{ id: int })\ntype V(.{ id: int })\nfn f(u: U) -> int { let V::(.{ id }) = u; id }\nfn main() -> () {}\n",
            Code::E0301,
        ),
        (
            "fn main() -> () { let _: .{ var x: int } = .{ x: 1 } }\n",
            Code::E0357,
        ),
    ] {
        let mut pkg = VirtualPackage::new(Unit::Bin);
        pkg.insert(pkg.entry.clone(), src.as_bytes().to_vec());
        let checked = Driver.check(&pkg, Stage::Type);
        assert!(
            checked
                .result
                .diagnostics
                .iter()
                .any(|d| d.code == Some(code)),
            "expected {code:?} for `{src}`, got {:?}",
            checked.result.diagnostics
        );
    }
    Ok(())
}

#[test]
fn wave_d_effects_guards_recover_panic_and_ctl() -> Result<(), String> {
    let source = r#"
        type Box = .{ var v: int }
        eff Tag { fn mark() -> int }
        eff Yield { ctl emit(value: int) -> () }

        fn make_box() -> new Box { .{ var v: 7 } }
        fn take_plain(f: fn() -> Box) -> int { f().v }
        fn make_ref_reader(ref b: Box) &capture &return(ref b) -> new fn() &up(ref) -> int { \-> b.v }
        fn take_up(mut f: fn() &up -> int) &mut -> int { f() }
        fn ref_alias(ref a: Box, ref b: Box = a) -> int { b.v }
        fn take_eff(f: fn() @Tag -> int) -> bool {
            let _ = f
            true
        }

        fn main() @io -> () {
            -- -> new T into -> T
            assert(take_plain(make_box) == 7)

            -- &up(ref) into &up
            let mut b: Box = .{ var v: 9 }
            b.v = 11
            let mut up_fn: fn() &up -> int = make_ref_reader(ref b)
            assert(take_up(mut up_fn) == 11)
            assert(ref_alias(ref b) == 11)

            -- ctl Yield + unwind_ctl(k) + defer cleanup
            let mut out: []int = []
            var unwound = false
            with {
                ctl Yield::emit = \v, k -> {
                    Array::push(mut out, v)
                    if len(ref out) < 2 { k() } else { unwind_ctl(k) }
                }
                defer { unwound = true }
                let _ = Array::map([10, 20, 30], \x -> { Yield::emit(x); x })
            }
            assert(unwound && out == [10, 20])
            assert(take_eff(\-> Tag::mark()))

            println("wave-d-ok")
        }
    "#;
    run_aot(source, "wave-d-ok\n")?;

    for (src, stage, code) in [
        (
            "type Box = .{ var v: int }\neff E { fn op(x: Box) -> () }\nfn bad(x: Box) &capture -> () { let _ = x }\nfn main() -> () { with E::op = bad; E::op(.{ v: 1 }) }\n",
            Stage::Type,
            Code::E0534,
        ),
        (
            "type Box = .{ var v: int }\nfn f(ref a: Box, n: int = a.v) -> int { n }\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0409,
        ),
        (
            "fn in_range(v: int, lo: int, hi: int) -> ?() { if v >= lo && v <= hi { Some(()) } else { None } }\nfn f(x: int |> in_range(0, \"bad\")) -> ?int { Some(x) }\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0301,
        ),
        (
            "fn in_range(v: int, lo: int, hi: int) -> ?() { if v >= lo && v <= hi { Some(()) } else { None } }\nfn f(x: int |> in_range(0)) -> ?int { Some(x) }\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0314,
        ),
        (
            "use ril/panic as Panic\nfn main() -> () { let _ = Panic::recover(42) }\n",
            Stage::Type,
            Code::E0338,
        ),
        (
            "use ril/panic as Panic\nfn main() -> () { let _ = Panic::recover(\\x: int -> x) }\n",
            Stage::Type,
            Code::E0314,
        ),
        (
            "use ril/panic as Panic\neff Y { ctl step() -> () }\nfn main() -> () { with { ctl Y::step = \\k -> { let _ = Panic::recover(\\-> unwind_ctl(k)); () }; Y::step() } }\n",
            Stage::Access,
            Code::E0608,
        ),
        (
            "eff Y { ctl step() -> () }\nfn main() -> () { with { Y::step = \\k -> k(); Y::step() } }\n",
            Stage::Type,
            Code::E0623,
        ),
        (
            "eff Y { ctl step() -> () }\nfn bad() @Y -> () { defer Y::step() }\nfn main() -> () { with { ctl Y::step = \\k -> k(); bad() } }\n",
            Stage::Access,
            Code::E0616,
        ),
        (
            "eff Y { ctl step() -> () }\nfn main() -> () { with { ctl Y::step = \\k -> { let _ = k; () }; Y::step() } }\n",
            Stage::Access,
            Code::E0625,
        ),
    ] {
        let mut pkg = VirtualPackage::new(Unit::Bin);
        pkg.insert(pkg.entry.clone(), src.as_bytes().to_vec());
        let checked = Driver.check(&pkg, stage);
        assert!(
            checked
                .result
                .diagnostics
                .iter()
                .any(|d| d.code == Some(code)),
            "expected {code:?} at {stage:?} for `{src}`, got {:?}",
            checked.result.diagnostics
        );
    }
    Ok(())
}

#[test]
fn wave_e_introspection_type_patterns_and_parser_conformance() -> Result<(), String> {
    let source = r#"
        use ril/panic as Panic
        type Pair(int, str)
        type Config(.{ host: str = "localhost", port: int })
        type Box<T>(.{ item: T })
        type Shape { Circle(f64); Rect(f64, f64); Unit }

        type UnwrapBox = \T -> match <T> {
            <Box<let X>> -> <X>
            <Set<let X>> -> <X>
            <[let K: let M let V]> -> <(K, V)>
            _ -> <int>
        }
        type DropHost = \T -> match <T> {
            <.{ host: str, ..let Rest }> -> <Rest>
            _ -> <.{}>
        }
        type CirclePayload = Shape.("Circle")
        type Dict<K, M: FieldMode, V> = [K: M V]

        fn main() @io -> () {
            -- Self-hosted LenTarget in std/prelude.ril
            assert(len("hello") == 5)
            assert(len([1, 2, 3]) == 3)
            assert(len(["a": 1]) == 1)
            assert(len(Set::from_array([1, 2])) == 2)

            -- Structural type pattern matching (Box<let X>, Set<let X>, [K: M V], ..let Rest)
            let b: UnwrapBox<Box<str>> = "unboxed"
            let s: UnwrapBox<Set<int>> = 99
            let kv: UnwrapBox<[str: int]> = ("k", 7)
            let rest: DropHost<.{ host: str, port: int }> = .{ port: 80 }
            let r: CirclePayload = 3.5
            let d: Dict<str, let, int> = ["x": 1]
            assert(b == "unboxed" && s == 99 && kv.0 == "k" && kv.1 == 7 && rest.port == 80)
            assert(r == 3.5 && d?["x"] == Some(1))

            -- Runtime static folding of Reflect::{type_name, fields, sum_tags, type_kind, has_default}
            assert(meta Reflect::type_name(<int>) == "int")
            assert(len(meta Reflect::fields(<()>)) == 0)
            assert(len(meta Reflect::fields(<Pair>)) == 2)
            assert(len(meta Reflect::sum_tags(<Shape>)) == 3)
            assert(meta Reflect::type_kind(<int>) == Reflect::TypeKind::Value)
            assert(meta Reflect::type_kind(<()>) == Reflect::TypeKind::Value)
            assert(meta Reflect::type_kind(<(int, str)>) == Reflect::TypeKind::Tuple)
            assert(meta Reflect::type_kind(<Shape>) == Reflect::TypeKind::Sum)
            assert(meta Reflect::type_kind(<Set<int>>) == Reflect::TypeKind::OpaqueShared)
            assert(meta Reflect::type_kind(<Panic::Report>) == Reflect::TypeKind::OpaqueValue)
            assert(meta Reflect::type_kind(<Type<int>>) == Reflect::TypeKind::Meta)
            assert(meta Reflect::has_default(<Config>, "host"))
            assert(!meta Reflect::has_default(<Config>, "port"))

            -- for xs as mut x
            let mut boxes: [mut].{ var n: int } = [.{ var n: 1 }, .{ var n: 2 }]
            for mut boxes as mut item {
                item.n += 10
            }
            assert(boxes[0].n == 11 && boxes[1].n == 12)

            println("wave-e-ok")
        }
    "#;
    run_aot(source, "wave-e-ok\n")?;

    for (src, stage, code) in [
        (
            "fn f(x: [var][]int) -> () { let _ = x }\nfn main() -> () {}\n",
            Stage::Parse,
            Code::E0356,
        ),
        (
            "fn f(x: (int @io, str)) -> () { let _ = x }\nfn main() -> () {}\n",
            Stage::Parse,
            Code::E0333,
        ),
        (
            "type Bad = int @io\nfn main() -> () {}\n",
            Stage::Parse,
            Code::E0613,
        ),
        (
            "fn main() -> () { let MAX = 1; let _ = MAX }\n",
            Stage::Parse,
            Code::E0101,
        ),
        (
            "fn main() -> () { pub let x = 1; let _ = x }\n",
            Stage::Parse,
            Code::E0120,
        ),
        (
            "fn main() -> () { var via x = 1; let _ = x }\n",
            Stage::Parse,
            Code::E0403,
        ),
        (
            "fn main() -> () { use ref x = 1; let _ = x }\n",
            Stage::Parse,
            Code::E0208,
        ),
        (
            "fn main() -> () { var x = Some(1) else { return }; let _ = x }\n",
            Stage::Parse,
            Code::E0120,
        ),
        (
            "type F<T> = \\U -> <U>\nfn main() -> () {}\n",
            Stage::Parse,
            Code::E0120,
        ),
        (
            "type G = \\x -> <int>\nfn main() -> () {}\n",
            Stage::Parse,
            Code::E0544,
        ),
        (
            "fn f(x: .{ mut n: int }) -> () { let _ = x }\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0402,
        ),
        (
            "fn f(x: (mut []int, int)) -> () { let _ = x }\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0356,
        ),
        (
            "fn main() -> () { let _: .{ a: int, .. } = .{ a: 1 } }\n",
            Stage::Type,
            Code::E0344,
        ),
        (
            "fn f() -> .{ a: int, .. } { .{ a: 1 } }\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0344,
        ),
        (
            "meta let BAD = Reflect::sum_tags(<int>)\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0301,
        ),
        (
            "type Cfg(.{ host: str = \"a\" })\nmeta let BAD = Reflect::has_default(<Cfg>, \"missing\")\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0323,
        ),
    ] {
        let mut pkg = VirtualPackage::new(Unit::Bin);
        pkg.insert(pkg.entry.clone(), src.as_bytes().to_vec());
        let checked = Driver.check(&pkg, stage);
        assert!(
            checked
                .result
                .diagnostics
                .iter()
                .any(|d| d.code == Some(code)),
            "expected {code:?} at {stage:?} for `{src}`, got {:?}",
            checked.result.diagnostics
        );
    }
    Ok(())
}

#[test]
fn primitive_manifest_runtime_symbols_exist_in_ril_rt() {
    let rt_symbols: std::collections::HashSet<&str> =
        ril_codegen::runtime_symbol_names().into_iter().collect();
    for spec in ril_hir::PRIMITIVE_FNS {
        if let Some(symbol) = spec.runtime_symbol {
            assert!(
                rt_symbols.contains(symbol),
                "PRIMITIVE_FNS entry {}::{} references missing ril-rt symbol `{symbol}`",
                spec.module,
                spec.name
            );
        }
    }
}

#[test]
fn de_magification_self_hosted_set_stdlib_convert_compile_error_and_wrapper_syntax()
-> Result<(), String> {
    let source = r#"
        eff Ask { ctl value() -> int }

        type UserId(int)
        type AliasInt = int
        type Marker
        type BoxRec(.{ label: str = "def", count: int })
        opaque type SecretTag(str)

        fn make_secret(s: str) -> SecretTag { SecretTag::(s) }
        fn read_secret(t: SecretTag) -> str { inner(t) }

        meta fn static_stdlib_check() -> int {
            let s_snap: Set<int> = {
                let mut s = Set::from_array([3, 1, 2, 1])
                Set::insert(mut s, 4)
                let _ = Set::remove(mut s, 2)
                s
            }
            var sum = 0
            for s_snap as x {
                sum += x
            }
            let mut xs = [5, 2, 4, 1, 3]
            Array::sort(mut xs)
            let mut m: [str: int] = ["a": 10, "b": 20]
            Map::insert(mut m, "c", 30)
            let total = sum + xs[0] + (m?["c"] ?? 0) + len(String::split("x,y,z", ",")) + len(Bytes::to_array(bytes"AB"))
            Map::clear(mut m)
            Array::clear(mut xs)
            total + len(ref m) + len(ref xs)
        }

        meta let STATIC_TOTAL = static_stdlib_check()

        fn main() @io -> () {
            -- Wrapper vs alias distinction
            let uid = UserId::(7)
            let alias: AliasInt = 7
            let plain: int = alias
            assert(inner(uid) == plain && inner(Marker) == ())
            let rec = BoxRec::(.{ count: 2 })
            assert(rec.label == "def" && rec.count == 2)
            assert(read_secret(make_secret("ok")) == "ok")

            -- Self-hosted Set + derive + inspect + len + for
            let s0 = Set::from_array([10, 20])
            let s1 = derive(s0, \mut d -> {
                Set::insert(mut d, 30)
                let _ = Set::remove(mut d, 10)
            })
            assert(len(s0) == 2 && Set::contains(s0, 10) && !Set::contains(s0, 30))
            assert(len(s1) == 2 && !Set::contains(s1, 10) && Set::contains(s1, 30))
            assert(String::inspect(s1) == "Set([20, 30])")

            -- Self-hosted Numeric::to_int_exact
            assert(Numeric::to_int_exact(3.5) == None)
            assert(Numeric::to_int_exact(4.0) == Some(4))

            -- Self-hosted Array::sort (including NaN), Map, String, Bytes under Draft too
            let a0 = [3, 1, 2]
            let a1 = derive(a0, \mut d -> {
                Array::sort(mut d)
            })
            assert(a0 == [3, 1, 2] && a1 == [1, 2, 3])
            let m0: [str: int] = ["k": 1, "z": 2]
            let m1 = derive(m0, \mut d -> {
                Map::clear(mut d)
                Map::insert(mut d, "n", 9)
            })
            assert(len(m0) == 2 && m1?["n"] == Some(9) && Map::keys(m1) == ["n"] && Map::values(m1) == [9])
            assert(String::split("ab", "") == ["", "a", "b", ""])
            assert(String::split("", ",") == [""])
            assert(Bytes::to_array(bytes"AZ") == [65, 90])

            -- First-class Array::pop_front & ctl effect resumption
            let mut q = [41, 99]
            let head = Array::pop_front(mut q) ?? 0
            let result = with {
                ctl Ask::value = \k -> k(head + 1)
                Ask::value()
            }
            assert(result == 42 && q == [99])
            assert(STATIC_TOTAL == 44)
            println("wave-5-ok")
        }
    "#;
    run_aot(source, "wave-5-ok\n")?;

    // compile_error reports E0832 anchored at caller instantiation site with secondary label.
    let compile_err_src = concat!(
        "type MustBeInt = \\T -> match <T> {\n",
        "    <int> -> <int>\n",
        "    _ -> compile_error(\"expected int type\")\n",
        "}\n",
        "type Bad = MustBeInt<str>\n",
        "fn main() -> () {}\n",
    );
    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.insert(pkg.entry.clone(), compile_err_src.as_bytes().to_vec());
    let checked = Driver.check(&pkg, Stage::Type);
    let diag = checked
        .result
        .diagnostics
        .iter()
        .find(|d| d.code == Some(Code::E0832))
        .ok_or_else(|| format!("expected E0832, got {:?}", checked.result.diagnostics))?;
    assert!(
        diag.message.contains("expected int type"),
        "unexpected compile_error message: {}",
        diag.message
    );
    let call_offset = compile_err_src
        .find("MustBeInt<str>")
        .ok_or("missing call site")?;
    let primary = diag.primary.ok_or("missing primary span")?;
    assert_eq!(
        primary.start, call_offset,
        "expected compile_error primary span anchored at caller instantiation site"
    );
    assert!(
        !diag.labels().is_empty(),
        "expected secondary label pointing at compile_error site"
    );

    // Reject `opaque type Bad = int` (no `=` on opaque wrapper) and distinct wrappers `type A int` vs `type B int`.
    for (src, stage, code) in [
        (
            "opaque type Bad = int\nfn main() -> () {}\n",
            Stage::Parse,
            Code::E0120,
        ),
        (
            "type A(int)\ntype B(int)\nfn main() -> () { let _: B = A::(1) }\n",
            Stage::Type,
            Code::E0305,
        ),
        (
            "fn f<T |> InnerTarget>(x: T) -> () { let _ = x }\nfn main() -> () { f(42) }\n",
            Stage::Type,
            Code::E0301,
        ),
        (
            "fn main() -> () { let _ = meta Reflect::fields(<int>) }\n",
            Stage::Type,
            Code::E0358,
        ),
        (
            "fn main() -> () { let _ = Reflect::fields(<int>) }\n",
            Stage::Type,
            Code::E0810,
        ),
        (
            "fn main() -> () { let _ = Reflect::type_name(<int>) }\n",
            Stage::Type,
            Code::E0810,
        ),
        (
            "fn main() -> () { let _ = meta(1 + 2) }\n",
            Stage::Parse,
            Code::E0120,
        ),
        (
            "fn f(x: int) -> int { meta { if false { x } else { 1 } } }\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0814,
        ),
        (
            "fn f() -> str { let _: int = meta { return \"hi\" }; \"ok\" }\nfn main() -> () {}\n",
            Stage::Hir,
            Code::E0707,
        ),
        (
            "fn main() -> () { let _ = meta <int> }\n",
            Stage::Type,
            Code::E0816,
        ),
        (
            "fn main() -> () { let _ = meta (\\x: int -> x) }\n",
            Stage::Type,
            Code::E0816,
        ),
        (
            "fn main() -> () { let mut xs = meta [1, 2]; Array::push(mut xs, 3) }\n",
            Stage::Access,
            Code::E0520,
        ),
        (
            "fn main() -> () { let xs: [mut][]int = meta [[1]]; let _ = xs }\n",
            Stage::Access,
            Code::E0522,
        ),
        (
            "fn f<T |> InnerTarget>(x: T) -> () { let _ = x }\nfn main() -> () { f(()) }\n",
            Stage::Type,
            Code::E0301,
        ),
        (
            "type BadKey = Reflect::FieldKey<int>\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0358,
        ),
        (
            "type BadNominal = Nominal<int>\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0306,
        ),
        (
            "fn main() -> () { let _ = Nominal }\n",
            Stage::Type,
            Code::E0319,
        ),
        (
            "type BadKeyOf = KeyOf<.{ a: int }>\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0306,
        ),
        (
            "type BadArity = \\T -> match <T> { <Nominal> -> <int>; _ -> <str> }\ntype X = BadArity<int>\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0340,
        ),
        (
            "type BadArity2 = \\T -> match <T> { <Nominal<int, str>> -> <int>; _ -> <str> }\ntype X = BadArity2<int>\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0340,
        ),
        (
            "sub Secret { pub opaque type Hidden(int) }\ntype U = Inner<Secret::Hidden>\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0308,
        ),
        (
            "sub Secret { pub opaque type Hidden(.{ x: int }) }\ntype K = Reflect::FieldKey<Secret::Hidden>\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0308,
        ),
        (
            "opaque type LocalInt(int)\ntype K = Reflect::FieldKey<LocalInt>\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0358,
        ),
        (
            "sub Secret { pub opaque type Hook(fn() -> ()) }\nfn f<T |> SharedObject>(x: T) -> T { x }\nfn g(h: Secret::Hook) -> Secret::Hook { f(h) }\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0301,
        ),
        (
            "type Marker\nfn f<T |> SharedObject>(x: T) -> T { x }\nfn main() -> () { let _ = f(Marker) }\n",
            Stage::Type,
            Code::E0301,
        ),
        (
            "type UserId(int)\nfn f<T |> SharedObject>(x: T) -> T { x }\nfn main() -> () { let _ = f(UserId::(1)) }\n",
            Stage::Type,
            Code::E0301,
        ),
        (
            "use ril/panic as Panic\nfn f<T |> SharedObject>(x: T) -> T { x }\nfn g(r: Panic::Report) -> Panic::Report { f(r) }\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0301,
        ),
    ] {
        let mut pkg = VirtualPackage::new(Unit::Bin);
        pkg.insert(pkg.entry.clone(), src.as_bytes().to_vec());
        let checked = Driver.check(&pkg, stage);
        assert!(
            checked
                .result
                .diagnostics
                .iter()
                .any(|d| d.code == Some(code)),
            "expected {code:?} at {stage:?} for `{src}`, got {:?}",
            checked.result.diagnostics
        );
    }

    // Positive self-hosted type-function & Nominal<pat> & TypeKind soundness tests
    let self_hosted_ok = r#"
        type UserId(int)
        type Box<T>(T)
        type Node(.{ val: int, next: ?Node })
        opaque type LocalRec(.{ host: str })
        sub Secret {
            pub opaque type HiddenShared(.{ n: int })
            pub opaque type HiddenValue(int)
            pub opaque type Hook(fn() -> ())
        }

        fn unwrap_box<T>(b: Box<T>) -> Inner<Box<T>> { inner(b) }
        fn check_shared<T |> SharedObject>(x: T) -> T { x }
        fn check_len<T |> LenTarget>(via x: T) -> int { len(x) }
        fn generic_kind<T>(x: Option<T>) -> int {
            let _ = x
            meta assert(Reflect::type_kind(<Option<T>>) == Reflect::TypeKind::Sum)
            meta assert(Reflect::type_kind(<Set<T>>) == Reflect::TypeKind::OpaqueShared)
            meta if <T> == <str> {
                meta compile_error("unreachable str branch")
            } else {
                meta {
                    var sum = 0
                    for 1..=4 as i {
                        sum += i
                    }
                    sum
                }
            }
        }

        type AnyRecMode = \T -> match <T> {
            <.{ let _ host: str, .. }> -> <str>
            _ -> <never>
        }
        meta let _ = assert(<AnyRecMode<.{ var host: str, port: int }>> == <str>)
        meta let _ = assert(<AnyRecMode<.{ host: str }>> == <str>)
        type IsNonEmptyTuple = \T -> match <T> {
            <(..)> -> <int>
            _ -> <never>
        }
        meta let _ = assert(<IsNonEmptyTuple<(int, str)>> == <int>)
        meta let _ = assert(<IsNonEmptyTuple<()>> == <never>)

        type InspectNominal = \T -> match <T> {
            <Nominal<let Payload>> -> <Payload>
            _ -> <never>
        }

        -- Nominal<pat> respects scope transparency
        meta let _ = assert(<InspectNominal<UserId>> == <int>)
        meta let _ = assert(<InspectNominal<LocalRec>> == <.{ host: str }>)
        meta let _ = assert(<InspectNominal<Secret::HiddenShared>> == <never>)

        -- TypeKind classification
        meta let _ = assert(Reflect::type_kind(<int>) == Reflect::TypeKind::Value)
        meta let _ = assert(Reflect::type_kind(<()>) == Reflect::TypeKind::Value)
        meta let _ = assert(Reflect::type_kind(<(int, str)>) == Reflect::TypeKind::Tuple)
        meta let _ = assert(Reflect::type_kind(<.{ a: int }>) == Reflect::TypeKind::Record)
        meta let _ = assert(Reflect::type_kind(<[]int>) == Reflect::TypeKind::Array)
        meta let _ = assert(Reflect::type_kind(<[str: int]>) == Reflect::TypeKind::Map)
        meta let _ = assert(Reflect::type_kind(<Option<int>>) == Reflect::TypeKind::Sum)
        meta let _ = assert(Reflect::type_kind(<UserId>) == Reflect::TypeKind::Nominal)
        meta let _ = assert(Reflect::type_kind(<LocalRec>) == Reflect::TypeKind::OpaqueShared)
        meta let _ = assert(Reflect::type_kind(<Secret::HiddenShared>) == Reflect::TypeKind::OpaqueShared)
        meta let _ = assert(Reflect::type_kind(<Secret::HiddenValue>) == Reflect::TypeKind::OpaqueValue)
        meta let _ = assert(Reflect::type_kind(<Secret::Hook>) == Reflect::TypeKind::Opaque)
        meta let _ = assert(Reflect::type_kind(<fn(int) -> int>) == Reflect::TypeKind::Fn)
        meta let _ = assert(Reflect::type_kind(<Derived<[]int>>) == Reflect::TypeKind::Derived)
        meta let _ = assert(Reflect::type_kind(<Type<int>>) == Reflect::TypeKind::Meta)
        meta let _ = assert(Reflect::type_kind(<FieldMode>) == Reflect::TypeKind::Meta)

        fn main() @io -> () {
            -- Inner / InnerTarget / Reflect::FieldKey / LenTarget are public and self-hosted
            let u: Inner<UserId> = 42
            assert(u == 42)
            assert(unwrap_box(Box::(7)) == 7)
            let k: Reflect::FieldKey<LocalRec> = "host"
            assert(k == "host")
            let _: Reflect::FieldKey<.{ a: int }> = "a"
            let _: Reflect::FieldKey<(int, str)> = 0
            let _: Reflect::FieldKey<()> = 0

            -- SharedObject accepts recursive nominals and shared-backed opaques
            let node = check_shared(Node::(.{ val: 1, next: None }))
            assert(inner(node).val == 1)
            let s = check_shared(Set::from_array([1, 2]))
            assert(check_len(s) == 2)
            let updated = derive([1, 2], \mut d -> {
                assert(len(ref d) == 2)
                Array::push(mut d, 3)
            })
            assert(len(updated) == 3)
            assert(generic_kind(Some(1)) == 10)
            let spaced = meta (1 + 2) * 3
            assert(spaced == 9)
            let fm = meta FieldMode::Var
            assert(fm == FieldMode::Var)
            println("self-hosted-ok")
        }
    "#;
    run_aot(self_hosted_ok, "self-hosted-ok\n")?;

    Ok(())
}
