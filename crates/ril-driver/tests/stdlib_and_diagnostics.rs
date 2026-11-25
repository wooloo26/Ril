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
            assert(Array::len(ref xs) == 2)
            Array::clear(mut xs)
            assert(Array::len(ref xs) == 0 && Array::pop(mut xs) == None)

            -- Map::{get, insert, remove, contains, clear, keys, values, len}
            let mut m: [str: int] = [:]
            Map::insert(mut m, "a", 1)
            Map::insert(mut m, "b", 2)
            assert(Map::len(ref m) == 2)
            assert(Map::contains(ref m, "a") && !Map::contains(ref m, "z"))
            assert(Map::get(ref m, "b") == Some(2))
            assert(Map::keys(ref m) == ["a", "b"])
            assert(Map::values(ref m) == [1, 2])
            assert(Map::remove(mut m, "a") == Some(1))
            assert(Map::remove(mut m, "a") == None)
            Map::clear(mut m)
            assert(Map::len(ref m) == 0)

            -- Set::{empty, from_array, insert, remove, contains, len}, clone, ==, for
            let mut s: Set<int> = Set::empty()
            Set::insert(mut s, 10)
            Set::insert(mut s, 20)
            Set::insert(mut s, 10)
            assert(len(ref s) == 2 && Set::len(ref s) == 2)
            assert(Set::contains(ref s, 10) && !Set::contains(ref s, 99))
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
            assert(inf > 1.0e300 && Numeric::trunc(inf) == None)

            let f_sub: fn(left: int, right: int) -> int = sub_named
            assert(f_sub(right: 3, left: 10) == 7)

            println("wave-b-ok")
        }
    "#;
    run_aot(source, "wave-b-ok\n")?;

    // Module-specific receiver checks and mode/orderable/mutability checks.
    for (src, code) in [
        (
            "fn main() -> () { let _ = Map::len(\"abc\") }\n",
            Code::E0301,
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
        nominal type UserId = int
        nominal type Config = .{ host: str = "localhost", port: int = 8080 }
        meta let DEFAULT_CFG = Config.{ port: 9000 }

        fn unwrap_copy<W |> NominalWrapper>(w: W) -> Unwrap<W> { inner(w) }
        fn coord_kind<T>(k: CoordKey<T>) -> CoordKey<T> { k }
        fn pair_only<T |> Tuple>(t: T) -> T { t }
        fn shared_only<T |> SharedObject>(v: T) -> T { v }
        fn len_only<T |> LenTarget>(v: T) -> int { len(v) }

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
            -- First-class bare nominal constructor
            let ids = Array::map([1, 2, 3], UserId)
            assert(inner(ids[0]) == 1 && inner(ids[2]) == 3)

            -- Prelude static checks & helpers
            assert(unwrap_copy(UserId(42)) == 42)
            assert(coord_kind<Config>("host") == "host")
            assert(coord_kind<(int, str)>(0) == 0)
            assert(pair_only((1, 2)) == (1, 2))
            assert(shared_only([1, 2]) == [1, 2])
            assert(len_only("abc") == 3)

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
            "fn f<T |> Tuple>(x: T) -> T { x }\nfn main() -> () { let _ = f(1) }\n",
            Code::E0301,
        ),
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
            "nominal type U = .{ id: int }\nnominal type V = .{ id: int }\nfn f(u: U) -> int { let V.{ id } = u; id }\nfn main() -> () {}\n",
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
fn wave_d_effects_guards_absorb_panic_and_concurrency() -> Result<(), String> {
    let source = r#"
        use ril/fiber
        use ril/channel

        type Box = .{ var v: int }
        eff Tag { fn mark() -> int }

        fn make_box() -> new Box { .{ var v: 7 } }
        fn take_plain(f: fn() -> Box) -> int { f().v }
        fn make_ref_reader(ref b: Box) &capture &return(ref b) -> new fn() &up(ref) -> int { \-> b.v }
        fn take_up(mut f: fn() &up -> int) &mut -> int { f() }
        fn ref_alias(ref a: Box, ref b: Box = a) -> int { b.v }
        fn sendable_eff(f: fn() @Tag -> int) -> bool {
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

            -- Fiber::Zip real alias + Fiber::map + Channel::drain + Sendable user eff
            let zipped: Fiber::Zip<int, str> = Fiber::run \-> Fiber::zip(\-> 1, \-> "ok")
            assert(zipped.first == 1 && zipped.second == "ok")
            let mapped = Fiber::run \-> Fiber::map([1, 2, 3], \x -> x * 2)
            assert(mapped == [2, 4, 6])

            let sum = Fiber::run \-> {
                let Channel::ChannelPair.{ mut tx, mut rx } = Channel::bounded(4)
                let Ok() = Channel::send(mut tx, 10) else { panic("send failed") }
                let Ok() = Channel::send(mut tx, 20) else { panic("send failed") }
                Channel::close(new tx)
                var acc = 0
                Channel::drain(new rx, \v -> { acc += v })
                acc
            }
            assert(sum == 30)
            assert(sendable_eff(\-> Tag::mark()))

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
            "type Box = .{ var v: int }\nfn ok_after(res: int, b: Box) -> ?() { if res == b.v { Some(()) } else { None } }\nfn f(new b: Box) -> ?int |> ok_after(b) { let _ = new b; Some(1) }\nfn main() -> () {}\n",
            Stage::Access,
            Code::E0549,
        ),
        (
            "fn main() -> () { let _ = absorb_panic(42) }\n",
            Stage::Type,
            Code::E0338,
        ),
        (
            "fn main() -> () { let _ = absorb_panic(\\x: int -> x) }\n",
            Stage::Type,
            Code::E0314,
        ),
        (
            "use ril/channel\nfn main() -> () { let Channel::ChannelPair.{ mut tx, mut rx } = Channel::bounded<int>(1); let _ = absorb_panic(\\-> Channel::close(new tx)); Channel::close_recv(new rx) }\n",
            Stage::Access,
            Code::E0608,
        ),
        (
            "use ril/fiber\nfn main() -> () { var n = 0; let _ = Fiber::run(\\-> Fiber::map([1, 2], \\x -> { n += x; x })) }\n",
            Stage::Access,
            Code::E0601,
        ),
        (
            "use ril/fiber\neff Tick { fn bump() -> int }\nfn main() -> () { var n = 0; with Tick::bump = \\-> { n += 1; n }; let _ = Fiber::run(\\-> Fiber::map([1, 2], \\_ -> Tick::bump())) }\n",
            Stage::Access,
            Code::E0615,
        ),
        (
            "use ril/fiber\nfn main() -> () { let _ = Fiber::run(\\-> Fiber::try_scope(\\mut _ -> 42)) }\n",
            Stage::Type,
            Code::E0301,
        ),
        (
            "use ril/channel\nfn main() -> () { let Channel::ChannelPair.{ mut tx, mut rx } = Channel::bounded(1); Channel::drain(new tx, \\_ -> ()); Channel::close_recv(new rx) }\n",
            Stage::Type,
            Code::E0301,
        ),
        (
            "use ril/fiber\nfn f(t: Fiber::Task<Fiber::Scope>) -> () { let _ = t }\nfn main() -> () {}\n",
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
    Ok(())
}

#[test]
fn wave_e_introspection_type_patterns_and_parser_conformance() -> Result<(), String> {
    let source = r#"
        nominal type Pair = (int, str)
        nominal type Config = .{ host: str = "localhost", port: int }
        nominal type Box<T> = .{ item: T }
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
        type Dict<K, M: MemberMode, V> = [K: M V]

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

            -- Runtime static folding of type_name, coords, variants, Reflect::has_default
            assert(type_name(<int>) == "int")
            assert(len(coords(<()>)) == 0)
            assert(len(coords(<Pair>)) == 2)
            assert(len(variants(<Shape>)) == 3)
            assert(Reflect::has_default(<Config>, "host"))
            assert(!Reflect::has_default(<Config>, "port"))

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
            Code::E0532,
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
            "meta let BAD = variants(<int>)\nfn main() -> () {}\n",
            Stage::Type,
            Code::E0301,
        ),
        (
            "nominal type Cfg = .{ host: str = \"a\" }\nmeta let BAD = Reflect::has_default(<Cfg>, \"missing\")\nfn main() -> () {}\n",
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
