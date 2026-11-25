#![forbid(unsafe_code)]

use std::path::PathBuf;

use ril_base::diag::Code;
use ril_driver::{CompileOptions, Driver};
use ril_test::{Stage, Unit, VirtualPackage};

#[test]
fn incremental_reuses_unchanged_files_and_invalidates_on_source_edit() {
    let compiler = Driver.incremental(CompileOptions::default());
    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.insert(
        PathBuf::from("pkg/math.ril"),
        b"pub fn add(a: int, b: int) -> int { a + b }\n".to_vec(),
    );
    pkg.insert(
        pkg.entry.clone(),
        b"use pkg/math\nfn main() -> () { let _ = Math::add(1, 2) }\n".to_vec(),
    );

    // Cold run: parses both files, type/access/mir misses.
    let first = compiler.check(&pkg, Stage::Access);
    assert!(first.result.diagnostics.is_empty());
    let stats = compiler.stats().unwrap();
    assert_eq!(stats.parse_misses, 2);
    assert_eq!(stats.parse_hits, 0);
    assert_eq!(stats.type_misses, 1);
    assert_eq!(stats.access_misses, 1);

    // Identical re-query hits check cache immediately.
    compiler.reset_stats();
    let second = compiler.check(&pkg, Stage::Access);
    assert!(second.result.diagnostics.is_empty());
    let stats = compiler.stats().unwrap();
    assert_eq!(stats.check_hits, 1);
    assert_eq!(stats.parse_misses, 0);
    assert_eq!(stats.type_misses, 0);
    assert_eq!(stats.access_misses, 0);

    // Edit pkg/main.ril only -> pkg/math.ril hits parse cache; downstream recomputes.
    compiler.reset_stats();
    pkg.insert(
        pkg.entry.clone(),
        b"use pkg/math\nfn main() -> () { let _ = Math::add(3, 4) }\n".to_vec(),
    );
    let third = compiler.check(&pkg, Stage::Access);
    assert!(third.result.diagnostics.is_empty());
    let stats = compiler.stats().unwrap();
    assert_eq!(
        stats.parse_hits, 1,
        "unchanged pkg/math.ril should hit parse cache"
    );
    assert_eq!(stats.parse_misses, 1, "edited pkg/main.ril should re-parse");
    assert_eq!(stats.type_misses, 1);
    assert_eq!(stats.access_misses, 1);

    // Introduce a type error in pkg/main.ril -> invalidated and error reported.
    pkg.insert(
        pkg.entry.clone(),
        b"use pkg/math\nfn main() -> () { let _ = Math::add(3, \"bad\") }\n".to_vec(),
    );
    let fourth = compiler.check(&pkg, Stage::Access);
    assert!(
        fourth
            .result
            .diagnostics
            .iter()
            .any(|diag| diag.code == Some(Code::E0301))
    );
}

#[test]
fn incremental_invalidates_on_dependency_interface_change_and_reuses_same_abi_hash() {
    let mut dep_v1 = VirtualPackage::new(Unit::Lib);
    dep_v1.entry = PathBuf::from("pkg/cell.ril");
    dep_v1.insert(
        dep_v1.entry.clone(),
        b"pub type Cell = .{ var count: int }\npub fn read(via c: Cell) -> int { c.count }\n"
            .to_vec(),
    );
    let iface_v1 = Driver.interface(&dep_v1).unwrap().encode().unwrap();
    // Reformat JSON without changing semantics/abi_hash.
    let parsed_json: serde_json::Value = serde_json::from_slice(&iface_v1).unwrap();
    let iface_v1_compact = serde_json::to_vec(&parsed_json).unwrap();
    assert_ne!(iface_v1, iface_v1_compact);

    let mut dep_v2 = VirtualPackage::new(Unit::Lib);
    dep_v2.entry = PathBuf::from("pkg/cell.ril");
    dep_v2.insert(
        dep_v2.entry.clone(),
        b"pub type Cell = .{ var count: int }\npub fn read(via c: Cell) -> int { c.count += 1; c.count }\n"
            .to_vec(),
    );
    let iface_v2 = Driver.interface(&dep_v2).unwrap().encode().unwrap();

    let compiler = Driver.incremental(CompileOptions::default());
    let mut client = VirtualPackage::new(Unit::Lib);
    client.insert(PathBuf::from("dep/cell.rili"), iface_v1);
    client.insert(
        client.entry.clone(),
        b"use dep/cell\nfn use_cell(ref c: Cell::Cell) -> int { Cell::read(ref c) }\n".to_vec(),
    );

    assert!(
        compiler
            .check(&client, Stage::Access)
            .result
            .diagnostics
            .is_empty()
    );

    // Compact-formatted .rili with identical ABI hash still hits downstream check cache.
    compiler.reset_stats();
    client.insert(PathBuf::from("dep/cell.rili"), iface_v1_compact);
    assert!(
        compiler
            .check(&client, Stage::Access)
            .result
            .diagnostics
            .is_empty()
    );
    let stats = compiler.stats().unwrap();
    assert_eq!(stats.interface_decode_misses, 1);
    assert_eq!(stats.check_hits, 1);
    assert_eq!(stats.type_misses, 0);
    assert_eq!(stats.access_misses, 0);

    // Tightened v2 .rili changes abi_hash -> invalidates and rejects `ref c` with E0520.
    compiler.reset_stats();
    client.insert(PathBuf::from("dep/cell.rili"), iface_v2);
    let checked = compiler.check(&client, Stage::Access);
    assert!(
        checked
            .result
            .diagnostics
            .iter()
            .any(|diag| diag.code == Some(Code::E0520)),
        "{:?}",
        checked.result.diagnostics
    );
    let stats = compiler.stats().unwrap();
    assert_eq!(stats.check_misses, 1);
    assert_eq!(stats.access_misses, 1);
}

#[test]
fn incremental_invalidates_only_affected_stages_on_option_and_budget_changes() {
    let base = Driver.incremental(CompileOptions {
        opt_stack_promote: false,
        ..CompileOptions::default()
    });
    let opt = base.with_options(CompileOptions {
        opt_stack_promote: true,
        ..CompileOptions::default()
    });

    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.insert(
        pkg.entry.clone(),
        b"type P = .{ x: int, y: int }\nfn main() -> () { let p = P.{ x: 1, y: 2 }; let _ = p.x + p.y }\n"
            .to_vec(),
    );

    let base_mir = format!("{:#?}", base.lower_arc(&pkg).unwrap());
    assert!(base_mir.contains("ril_rt_record"));

    // Toggling opt_stack_promote reuses Type & Access, invalidates MIR & Object!
    base.reset_stats();
    let opt_mir = format!("{:#?}", opt.lower_arc(&pkg).unwrap());
    assert!(!opt_mir.contains("ril_rt_record"));
    let stats = base.stats().unwrap();
    assert_eq!(stats.type_hits, 1);
    assert_eq!(stats.access_hits, 1);
    assert_eq!(stats.type_misses, 0);
    assert_eq!(stats.access_misses, 0);
    assert_eq!(stats.mir_misses, 1);

    // Re-running opt hits MIR cache.
    base.reset_stats();
    let _ = opt.lower_arc(&pkg).unwrap();
    assert_eq!(base.stats().unwrap().mir_hits, 1);

    // Budget change reuses Parse cache, invalidates Type cache!
    let mut meta_pkg = VirtualPackage::new(Unit::Lib);
    meta_pkg.budget = Some(5);
    meta_pkg.insert(
        meta_pkg.entry.clone(),
        b"meta fn spin(n: int) -> int { var i = 0; while i < n { i += 1 }; i }\nmeta let TOTAL = spin(20)\n"
            .to_vec(),
    );
    let tight = base.check(&meta_pkg, Stage::Type);
    assert!(
        tight
            .result
            .diagnostics
            .iter()
            .any(|diag| diag.code == Some(Code::E0811))
    );

    base.reset_stats();
    meta_pkg.budget = Some(500);
    let relaxed = base.check(&meta_pkg, Stage::Type);
    assert!(relaxed.result.diagnostics.is_empty());
    let stats = base.stats().unwrap();
    assert_eq!(
        stats.parse_hits, 1,
        "budget change should reuse parsed file"
    );
    assert_eq!(
        stats.type_misses, 1,
        "budget change must invalidate type check"
    );
}

#[test]
fn disk_incremental_cache_persists_across_sessions_and_invalidates_on_changes() {
    let dir = tempfile::tempdir().unwrap();
    let cache_dir = dir.path().join("cache");

    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.insert(
        pkg.entry.clone(),
        b"type P = .{ x: int }\nfn main() -> () { let p = P.{ x: 7 }; let _ = p.x }\n".to_vec(),
    );

    // Cold session populates check + object disk cache.
    let cold = Driver.with_disk_cache(
        CompileOptions {
            opt_stack_promote: false,
            ..CompileOptions::default()
        },
        cache_dir.clone(),
    );
    assert!(
        cold.check(&pkg, Stage::Access)
            .result
            .diagnostics
            .is_empty()
    );
    let obj1 = cold.compile_object(&pkg).unwrap();
    assert!(!obj1.is_empty());
    assert!(cold.stats().unwrap().disk_misses >= 2);

    // Fresh session hits disk cache for check and object.
    let warm = Driver.with_disk_cache(
        CompileOptions {
            opt_stack_promote: false,
            ..CompileOptions::default()
        },
        cache_dir.clone(),
    );
    assert!(
        warm.check(&pkg, Stage::Access)
            .result
            .diagnostics
            .is_empty()
    );
    let obj2 = warm.compile_object(&pkg).unwrap();
    assert_eq!(obj1.as_slice(), obj2.as_slice());
    let stats = warm.stats().unwrap();
    assert_eq!(stats.disk_hits, 2);
    assert_eq!(stats.type_misses, 0);
    assert_eq!(stats.mir_misses, 0);

    // Option change misses disk cache for object, produces different promoted object.
    let opt_session = Driver.with_disk_cache(
        CompileOptions {
            opt_stack_promote: true,
            ..CompileOptions::default()
        },
        cache_dir.clone(),
    );
    let obj_opt = opt_session.compile_object(&pkg).unwrap();
    assert_ne!(obj1.as_slice(), obj_opt.as_slice());
    assert_eq!(opt_session.stats().unwrap().disk_misses, 1);

    // Source change misses disk cache and reports new diagnostic.
    pkg.insert(
        pkg.entry.clone(),
        b"fn main() -> () { let x: int = \"bad\" }\n".to_vec(),
    );
    let invalid = Driver.with_disk_cache(CompileOptions::default(), cache_dir);
    let checked = invalid.check(&pkg, Stage::Access);
    assert!(
        checked
            .result
            .diagnostics
            .iter()
            .any(|diag| diag.code == Some(Code::E0301))
    );
    assert_eq!(invalid.stats().unwrap().disk_misses, 1);
}
