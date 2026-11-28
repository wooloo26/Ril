#![forbid(unsafe_code)]
#![allow(clippy::expect_used, clippy::unwrap_used, clippy::indexing_slicing)]

use std::path::Path;

use ril_driver::{
    CompileOptions, Driver,
    inspect::{AtQuery, InspectQuery},
};
use ril_test::{Unit, VirtualPackage};
use serde_json::Value;

fn inspect_src(src: &str, unit: Unit, query: &InspectQuery) -> Value {
    let mut pkg = VirtualPackage::new(unit);
    pkg.insert(pkg.entry.clone(), src.as_bytes().to_vec());
    let compiler = Driver.with_options(CompileOptions::default());
    let report = compiler.inspect_package(&pkg, query);
    let json = report.to_json(false);
    serde_json::from_str(&json).expect("inspect must emit valid JSON")
}

#[test]
fn pure_and_total_functions_including_stdlib_combinators() {
    let src = r#"
fn clamp(x: int, lo: int, hi: int) -> int {
    if x < lo { lo } else if x > hi { hi } else { x }
}

fn map_plus_one(xs: []int) -> new []int {
    Array::map(xs, \x -> x + 1)
}

fn safe_div(a: int, b |> NonZero) -> int {
    a / b
}

fn main() -> () {
    let _ = clamp(5, 0, 10)
    let _ = map_plus_one([1, 2, 3])
    let _ = safe_div(10, 2)
}
"#;
    let out = inspect_src(src, Unit::Bin, &InspectQuery::default());
    assert_eq!(out["schema_version"], 1);
    assert_eq!(out["ok"], true);
    assert_eq!(out["stage"], "access");
    let syms = out["symbols"].as_array().expect("symbols");

    let find = |name: &str| {
        syms.iter()
            .find(|s| s["sym"] == name)
            .unwrap_or_else(|| panic!("missing symbol {name}: {out}"))
    };

    let clamp = find("clamp");
    assert_eq!(clamp["pure"], true);
    assert_eq!(clamp["total"], true);
    assert!(clamp.get("may_panic").is_none());
    assert!(clamp.get("may_abort").is_none());
    assert!(clamp.get("may_diverge").is_none());

    let safe_div = find("safe_div");
    assert_eq!(safe_div["pure"], true);
    assert_eq!(safe_div["total"], true);

    // Array::map uses `for`, so its own loop is terminating and panic-free;
    // with a pure total callback, `map_plus_one` has no panic and no divergence.
    let map_plus_one = find("map_plus_one");
    assert_eq!(map_plus_one["pure"], true);
    assert!(map_plus_one.get("may_panic").is_none());
    assert!(map_plus_one.get("may_diverge").is_none());
}

#[test]
fn panic_propagation_defer_double_panic_and_recover_panic_sealing() {
    let src = r#"
use ril/panic

fn read_head(xs: []int) -> int {
    match xs?[0] {
        Some(v) -> v
        None -> panic("empty")
    }
}

fn caller_panics(xs: []int) -> int {
    read_head(xs)
}

fn sealed_panic(xs: []int) -> new !<int, Panic::Error> {
    Panic::recover(\-> read_head(xs))
}

fn safe_defer(mut buf: []int, idx: int) -> int {
    defer Array::clear(mut buf)
    buf?[idx] ?? 0
}

fn recursive_boom(n: int) -> int {
    if n <= 0 { 0 } else { 1 + recursive_boom(n - 1) }
}

fn main() -> () {
    let mut a = [1, 2]
    let _ = caller_panics([1])
    match sealed_panic([1]) {
        Ok(_) -> ()
        Err(_) -> ()
    }
    let _ = safe_defer(mut a, 0)
    let _ = recursive_boom(3)
}
"#;
    let out = inspect_src(src, Unit::Bin, &InspectQuery::default());
    assert_eq!(out["ok"], true, "unexpected diagnostics: {out}");

    let syms = out["symbols"].as_array().expect("symbols");
    let find = |name: &str| syms.iter().find(|s| s["sym"] == name).unwrap();

    // Multi-hop shortest panic chain: caller_panics -> read_head -> panic -> cause: panic
    let caller = find("caller_panics");
    assert_eq!(caller["pure"], true);
    assert!(caller.get("total").is_none());
    let panic_chain = caller["may_panic"].as_array().expect("may_panic witness");
    assert_eq!(
        panic_chain.len(),
        3,
        "expected 3-hop chain: {panic_chain:?}"
    );
    assert_eq!(panic_chain[0]["call"], "read_head");
    assert_eq!(panic_chain[2]["cause"], "panic");

    // `Panic::recover` seals implicit `@panic` outside `defer`
    let sealed = find("sealed_panic");
    assert_eq!(sealed["pure"], true);
    assert_eq!(sealed["total"], true);
    assert!(sealed.get("may_panic").is_none());

    // `safe_defer` records mutated params, has no `may_panic` and no `defer_double_panic`
    let sd = find("safe_defer");
    assert_eq!(sd["mut"], serde_json::json!(["buf"]));
    assert!(sd.get("may_panic").is_none());
    assert!(sd.get("may_abort").is_none());

    // Recursive SCC -> `may_diverge` (recursion) AND `may_abort` (stack_overflow)
    let rec = find("recursive_boom");
    assert_eq!(rec["may_diverge"][0]["cause"], "recursion");
    assert_eq!(rec["may_abort"][0]["cause"], "stack_overflow");

    // Hard error E0627 statically prevents panic inside `defer` (eliminating double-panic abort)
    let bad_defer_src = r#"
fn dangerous_defer(mut buf: []int) -> () {
    defer assert(len(ref buf) == 0, "not empty")
    Array::clear(mut buf)
}
fn main() -> () {
    let mut a = [1, 2]
    dangerous_defer(mut a)
}
"#;
    let bad_out = inspect_src(bad_defer_src, Unit::Bin, &InspectQuery::default());
    assert_eq!(
        bad_out["ok"], false,
        "defer panic must be hard error E0627: {bad_out}"
    );
    let diags = bad_out["diagnostics"].as_array().expect("diagnostics");
    assert!(
        diags
            .iter()
            .any(|d| d["sev"] == "error" && d["code"] == "E0627"),
        "expected E0627 hard error on panicking defer, got {diags:?}"
    );
}

#[test]
fn sites_filters_and_partial_broken_file_contract() {
    let src = r#"
eff Emit {
    ctl send(v: int) -> ()
}

fn pick<T>(via xs: []T) -> infer ?T {
    xs?[0]
}

fn run(mut items: []int) -> int {
    var total = 0
    with {
        ctl Emit::send = \v, k -> {
            total += v
            if total < 10 { k() } else { unwind_ctl(k); total }
        }
        let h = pick(ref items) ?? 0
        Array::push(mut items, h)
        Emit::send(h)
        total
    }
}

fn main() -> () {
    let mut xs = [3, 4]
    let _ = run(mut xs)
}
"#;
    // Filter by `--symbol run`
    let q = InspectQuery {
        symbols: vec!["run".into()],
        ..InspectQuery::default()
    };
    let out = inspect_src(src, Unit::Bin, &q);
    assert_eq!(out["ok"], true, "unexpected diagnostics: {out}");
    let syms = out["symbols"].as_array().unwrap();
    assert_eq!(syms.len(), 1);
    assert_eq!(syms[0]["sym"], "run");
    assert_eq!(syms[0]["mut"], serde_json::json!(["items"]));

    let sites = out["sites"].as_array().expect("sites");
    assert!(
        sites
            .iter()
            .any(|s| s["kind"] == "with" && s["op"] == "ctl Emit::send")
    );
    assert!(sites.iter().any(|s| s["kind"] == "effect_call"
        && s["op"] == "ctl Emit::send"
        && s["bound_by"] != "caller"));
    assert!(
        sites
            .iter()
            .any(|s| s["kind"] == "via_call" && s["callee"] == "pick")
    );
    assert!(
        sites
            .iter()
            .any(|s| s["kind"] == "closure"
                && s["captures"].as_array().is_some_and(|c| !c.is_empty()))
    );

    // Broken file still produces valid JSON with `ok: false`, `stage: "type"`, and `partial: true`
    let broken =
        "fn ok_fn(x: int) -> int { x }\nfn bad() -> int { \"nope\" }\nfn main() -> () {}\n";
    let broken_out = inspect_src(broken, Unit::Bin, &InspectQuery::default());
    assert_eq!(broken_out["ok"], false);
    assert_eq!(broken_out["stage"], "type");
    assert!(!broken_out["diagnostics"].as_array().unwrap().is_empty());
    let ok_fn = broken_out["symbols"]
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s["sym"] == "ok_fn")
        .unwrap();
    assert_eq!(ok_fn["partial"], true);

    // `--at` parser & `--include` fail-fast validation
    let at = AtQuery::parse("src/main.ril:10-20").unwrap();
    assert_eq!(at.file.as_deref(), Some("src/main.ril"));
    assert_eq!((at.start_line, at.end_line), (10, 20));
    let reserved = InspectQuery {
        includes: vec!["via_domains".into()],
        ..InspectQuery::default()
    };
    assert!(reserved.validate().unwrap_err().contains("reserved"));
}

#[test]
fn cross_package_behavior_propagates_via_rili_without_changing_abi_hash() {
    let compiler = Driver.with_options(CompileOptions::default());

    let mut lib_v1 = VirtualPackage::new(Unit::Lib);
    lib_v1.entry = Path::new("pkg/math.ril").into();
    lib_v1.insert(
        Path::new("pkg/math.ril").into(),
        b"pub fn compute(a: int, b: int) -> int { a + b }\n".to_vec(),
    );
    let iface_v1 = compiler.interface(&lib_v1).expect("iface v1");
    assert!(
        iface_v1.behavior.is_empty(),
        "total fn omits empty behavior"
    );

    let mut lib_v2 = VirtualPackage::new(Unit::Lib);
    lib_v2.entry = Path::new("pkg/math.ril").into();
    lib_v2.insert(
        Path::new("pkg/math.ril").into(),
        b"pub fn compute(a: int, b: int) -> int { if b == 0 { panic(\"zero\") } else { a / b } }\n"
            .to_vec(),
    );
    let iface_v2 = compiler.interface(&lib_v2).expect("iface v2");
    assert_eq!(
        iface_v1.abi_hash, iface_v2.abi_hash,
        "behavior must NOT invalidate abi_hash"
    );
    assert!(
        iface_v2
            .behavior
            .values()
            .any(|b| b.may_panic && !b.may_diverge)
    );
    assert!(
        iface_v1.compare(&iface_v2).is_empty(),
        "behavior change must not trigger E0552"
    );

    // Downstream consumer importing `.rili` sees `may_panic` from `lib_v2`!
    let encoded = iface_v2.encode().expect("encode v2 .rili");
    let mut app = VirtualPackage::new(Unit::Bin);
    app.insert(Path::new("dep/math.rili").into(), encoded);
    app.insert(
        app.entry.clone(),
        b"use dep/math\nfn use_dep(x: int) -> int { Math::compute(x, 0) }\nfn main() -> () { let _ = use_dep(1) }\n".to_vec(),
    );
    let report = compiler.inspect_package(&app, &InspectQuery::default());
    let out: Value = serde_json::from_str(&report.to_json(false)).unwrap();
    let use_dep = out["symbols"]
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s["sym"] == "use_dep")
        .unwrap();
    assert!(
        use_dep.get("may_panic").is_some(),
        "expected cross-package may_panic propagation: {use_dep}"
    );
    assert!(use_dep.get("total").is_none());
}

#[test]
fn unreachable_preserves_total_behavior_and_is_allowed_in_defer() {
    let compiler = Driver.with_options(CompileOptions::default());
    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.insert(
        pkg.entry.clone(),
        br#"
type HttpClass(int) |> Between<100, 599>

fn total_with_dbm_exhaustiveness(x: int, c: HttpClass) -> int {
    let base = match inner(c) {
        100..=399 -> 1
        400..=599 -> 2
    }
    let sign = if x < 0 {
        -1
    } else if x == 0 {
        0
    } else if x > 0 {
        1
    }
    base + sign
}

fn main() -> () {
    let _ = total_with_dbm_exhaustiveness(1, HttpClass::(200))
}
"#
        .to_vec(),
    );
    let report = compiler.inspect_package(&pkg, &InspectQuery::default());
    let out: Value = serde_json::from_str(&report.to_json(false)).unwrap();
    assert_eq!(out["ok"], true, "expected ok inspect report: {out}");
    let sym = out["symbols"]
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s["sym"] == "total_with_dbm_exhaustiveness")
        .unwrap();
    assert_eq!(
        sym["total"], true,
        "DBM-exhaustive match/if must keep fn total: {sym}"
    );
    assert!(sym.get("may_panic").is_none());
    assert!(sym.get("may_abort").is_none());
    assert!(sym.get("may_diverge").is_none());
}
