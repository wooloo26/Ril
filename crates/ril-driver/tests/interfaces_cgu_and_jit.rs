use std::{fs, process::Command};

use ril_driver::{CompileOptions, Compiler, Driver, load_package};
use ril_sema::iface::Interface;
use ril_test::{Stage, Unit, VirtualPackage};

fn bin_package(source: &str) -> VirtualPackage {
    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.insert("pkg/main.ril".into(), source.as_bytes().to_vec());
    pkg
}

fn lib_package(source: &str) -> VirtualPackage {
    let mut pkg = VirtualPackage::new(Unit::Lib);
    pkg.entry = "pkg/lib.ril".into();
    pkg.insert("pkg/lib.ril".into(), source.as_bytes().to_vec());
    pkg
}

#[test]
fn binary_rili_v32_roundtrip_and_tamper_detection() -> Result<(), String> {
    let lib = lib_package(
        "pub fn double(x: int) -> int { x + x }\n\
         pub meta fn scale() -> int { 7 }\n",
    );
    let iface = Driver
        .interface(&lib)
        .map_err(|diags| format!("interface failed: {diags:?}"))?;
    assert_eq!(iface.format_version, 2);
    assert!(!iface.codegen_abi_hash.is_empty());

    let bin = iface.encode().map_err(|e| format!("encode failed: {e}"))?;
    assert!(bin.starts_with(b"RILI\0"), "expected binary RILI envelope");
    let decoded = Interface::decode(&bin).map_err(|e| format!("decode failed: {e}"))?;
    assert_eq!(decoded.abi_hash, iface.abi_hash);
    assert_eq!(decoded.codegen_abi_hash, iface.codegen_abi_hash);

    // Flip a payload byte and verify single-pass SHA-256 header rejects it.
    let mut tampered = bin.clone();
    if let Some(last) = tampered.last_mut() {
        *last ^= 0xFF;
    }
    assert!(
        Interface::decode(&tampered).is_err(),
        "tampered binary .rili must fail checksum verification"
    );

    // JSON wire encoding remains supported for human inspection.
    let json = iface
        .encode_json()
        .map_err(|e| format!("encode_json failed: {e}"))?;
    let from_json = Interface::decode(&json).map_err(|e| format!("decode json failed: {e}"))?;
    assert_eq!(from_json.abi_hash, iface.abi_hash);
    assert_eq!(from_json.codegen_abi_hash, iface.codegen_abi_hash);
    Ok(())
}

#[test]
fn opaque_type_dual_hash_early_cutoff_and_codegen_invalidation() -> Result<(), String> {
    let v1 = lib_package(
        "pub opaque type Token(.{ id: int })\n\
         pub fn make(n: int) -> new Token { Token::(.{ id: n }) }\n\
         pub fn read(t: Token) -> int { t.id }\n",
    );
    let v2 = lib_package(
        "pub opaque type Token(.{ id: int, tag: str })\n\
         pub fn make(n: int) -> new Token { Token::(.{ id: n, tag: \"v2\" }) }\n\
         pub fn read(t: Token) -> int { t.id }\n",
    );
    let iface_v1 = Driver
        .interface(&v1)
        .map_err(|d| format!("v1 interface failed: {d:?}"))?;
    let iface_v2 = Driver
        .interface(&v2)
        .map_err(|d| format!("v2 interface failed: {d:?}"))?;

    // Semantic ABI stays identical for downstream type/access early-cutoff.
    assert_eq!(iface_v1.abi_hash, iface_v2.abi_hash);
    // Codegen ABI changes because the underlying opaque representation changed!
    assert_ne!(iface_v1.codegen_abi_hash, iface_v2.codegen_abi_hash);

    let bin_v1 = iface_v1.encode().map_err(|e| e.to_string())?;
    let bin_v2 = iface_v2.encode().map_err(|e| e.to_string())?;

    let consumer_src = b"use dep/lib\npub fn check_it(n: int) -> int { Lib::read(Lib::make(n)) }\n";
    let mut consumer_v1 = VirtualPackage::new(Unit::Lib);
    consumer_v1.entry = "pkg/app.ril".into();
    consumer_v1.insert("pkg/app.ril".into(), consumer_src.to_vec());
    consumer_v1.insert("dep/lib.rili".into(), bin_v1);

    let mut consumer_v2 = VirtualPackage::new(Unit::Lib);
    consumer_v2.entry = "pkg/app.ril".into();
    consumer_v2.insert("pkg/app.ril".into(), consumer_src.to_vec());
    consumer_v2.insert("dep/lib.rili".into(), bin_v2);

    let compiler = Compiler::incremental(CompileOptions::default());
    let r1 = compiler.check(&consumer_v1, Stage::Access);
    assert!(
        r1.result.diagnostics.is_empty(),
        "{:?}",
        r1.result.diagnostics
    );
    compiler.reset_stats();

    let r2 = compiler.check(&consumer_v2, Stage::Access);
    assert!(
        r2.result.diagnostics.is_empty(),
        "{:?}",
        r2.result.diagnostics
    );
    let stats = compiler.stats().ok_or("missing stats")?;
    assert_eq!(
        stats.check_hits, 1,
        "opaque representation edit must hit downstream check cache via abi_hash early-cutoff"
    );
    assert_eq!(stats.type_misses, 0);
    Ok(())
}

#[test]
fn meta_fn_body_edit_invalidates_abi_hash() -> Result<(), String> {
    let v1 = lib_package("pub meta fn factor() -> int { 10 }\n");
    let v2 = lib_package("pub meta fn factor() -> int { 20 }\n");
    let i1 = Driver.interface(&v1).map_err(|d| format!("{d:?}"))?;
    let i2 = Driver.interface(&v2).map_err(|d| format!("{d:?}"))?;
    assert_ne!(
        i1.abi_hash, i2.abi_hash,
        "meta fn implementation change must invalidate abi_hash"
    );
    Ok(())
}

#[test]
fn canonical_symbols_and_multi_cgu_aot_link_and_run() -> Result<(), String> {
    let src = r#"
use ril/io
fn id<T>(x: T) -> T { x }
fn add_one(x: int) -> int { x + 1 }
fn mul_two(x: int) -> int { x * 2 }
fn combine(x: int) -> int {
    let a = id(add_one(x))
    let b = id(mul_two(a))
    let s = id("ok")
    b + len(s)
}
fn main() @io -> () {
    let res = combine(20)
    Io::println(String::inspect(res))
}
"#;
    let pkg = bin_package(src);
    let mir1 = Driver.lower(&pkg).map_err(|d| format!("{d:?}"))?;
    let mir2 = Driver.lower(&pkg).map_err(|d| format!("{d:?}"))?;
    let syms1: Vec<String> = mir1
        .function_symbols()
        .into_iter()
        .map(str::to_owned)
        .collect();
    let syms2: Vec<String> = mir2
        .function_symbols()
        .into_iter()
        .map(str::to_owned)
        .collect();
    assert_eq!(syms1, syms2, "canonical symbols must be deterministic");
    assert!(
        syms1.iter().all(|s| s.starts_with("_Ril_")),
        "expected _Ril_ canonical prefix on all symbols: {syms1:?}"
    );
    assert!(
        syms1.len() >= 5,
        "expected multiple lowered functions for multi-CGU test: {syms1:?}"
    );

    let compiler = Compiler::new(CompileOptions::default());
    let objects = compiler
        .compile_objects(&pkg, 3)
        .map_err(|d| format!("compile_objects failed: {d:?}"))?;
    assert_eq!(objects.len(), 3, "expected 3 distinct CGU object files");

    let dir = tempfile::tempdir().map_err(|e| e.to_string())?;
    let exe = dir.path().join("multi_cgu_bin");
    compiler
        .compile_aot_with_cgus(&pkg, &exe, &[], 3)
        .map_err(|d| format!("3-CGU AOT link failed: {d:?}"))?;

    let out = Command::new(&exe).output().map_err(|e| e.to_string())?;
    assert!(
        out.status.success(),
        "3-CGU binary failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "44");
    Ok(())
}

#[test]
fn in_process_jit_reentrant_execution() -> Result<(), String> {
    let compiler = Compiler::incremental(CompileOptions::default());
    for n in [10, 20, 30] {
        let pkg = bin_package(&format!(
            "fn main() -> () {{\n    let x = {n} + {n}\n    assert(x == {})\n}}\n",
            n * 2
        ));
        let status = compiler
            .execute_jit_in_process(&pkg)
            .map_err(|d| format!("in-process JIT failed for {n}: {d:?}"))?;
        assert_eq!(status, 0);
    }
    Ok(())
}

#[test]
fn ril_toml_manifest_dependency_resolution() -> Result<(), String> {
    let tmp = tempfile::tempdir().map_err(|e| e.to_string())?;
    let dep_dir = tmp.path().join("mathlib");
    let app_dir = tmp.path().join("app");
    fs::create_dir_all(dep_dir.join("src")).map_err(|e| e.to_string())?;
    fs::create_dir_all(app_dir.join("src")).map_err(|e| e.to_string())?;

    fs::write(
        dep_dir.join("src/calc.ril"),
        "pub fn triple(x: int) -> int { x * 3 }\n",
    )
    .map_err(|e| e.to_string())?;
    fs::write(
        app_dir.join("ril.toml"),
        "[package]\nname = \"app\"\nentry = \"src/main.ril\"\n\n[dependencies]\nmathlib = { path = \"../mathlib\" }\n",
    )
    .map_err(|e| e.to_string())?;
    fs::write(
        app_dir.join("src/main.ril"),
        "use mathlib/calc\nfn main() -> () {\n    assert(Calc::triple(14) == 42)\n}\n",
    )
    .map_err(|e| e.to_string())?;

    // Load directly from the package directory containing `ril.toml`.
    let pkg = load_package(&app_dir, Unit::Bin)?;
    let status = Compiler::new(CompileOptions::default())
        .execute_jit_in_process(&pkg)
        .map_err(|d| format!("ril.toml app failed: {d:?}"))?;
    assert_eq!(status, 0);
    Ok(())
}

#[test]
fn ril_toml_rejects_cyclic_and_self_package_dependencies() -> Result<(), String> {
    let tmp = tempfile::tempdir().map_err(|e| e.to_string())?;
    let pkg_a = tmp.path().join("pkg_a");
    let pkg_b = tmp.path().join("pkg_b");
    let self_pkg = tmp.path().join("self_pkg");
    fs::create_dir_all(pkg_a.join("src")).map_err(|e| e.to_string())?;
    fs::create_dir_all(pkg_b.join("src")).map_err(|e| e.to_string())?;
    fs::create_dir_all(self_pkg.join("src")).map_err(|e| e.to_string())?;

    fs::write(pkg_a.join("src/main.ril"), "fn main() -> () {}\n").map_err(|e| e.to_string())?;
    fs::write(pkg_b.join("src/lib.ril"), "pub fn v() -> int { 1 }\n").map_err(|e| e.to_string())?;
    fs::write(self_pkg.join("src/main.ril"), "fn main() -> () {}\n").map_err(|e| e.to_string())?;

    // A -> B -> A cycle
    fs::write(
        pkg_a.join("ril.toml"),
        "[package]\nname = \"pkg_a\"\nentry = \"src/main.ril\"\n\n[dependencies]\npkg_b = { path = \"../pkg_b\" }\n",
    )
    .map_err(|e| e.to_string())?;
    fs::write(
        pkg_b.join("ril.toml"),
        "[package]\nname = \"pkg_b\"\nentry = \"src/lib.ril\"\n\n[dependencies]\npkg_a = { path = \"../pkg_a\" }\n",
    )
    .map_err(|e| e.to_string())?;

    let err = load_package(&pkg_a, Unit::Bin)
        .err()
        .ok_or("expected cyclic ril.toml dependency error")?;
    assert!(
        err.contains("cyclic package dependency"),
        "unexpected error: {err}"
    );

    // Self-dependency A -> A
    fs::write(
        self_pkg.join("ril.toml"),
        "[package]\nname = \"self_pkg\"\nentry = \"src/main.ril\"\n\n[dependencies]\nself_pkg = { path = \".\" }\n",
    )
    .map_err(|e| e.to_string())?;
    let self_err = load_package(&self_pkg, Unit::Bin)
        .err()
        .ok_or("expected self ril.toml dependency error")?;
    assert!(
        self_err.contains("cyclic package dependency"),
        "unexpected self-dep error: {self_err}"
    );
    Ok(())
}
