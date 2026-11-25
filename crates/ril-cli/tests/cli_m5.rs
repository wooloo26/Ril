#![forbid(unsafe_code)]

use std::{fs, process::Command};

fn ril_bin() -> &'static str {
    env!("CARGO_BIN_EXE_ril")
}

#[test]
fn cli_opt_stack_promote_matches_jit_and_aot_and_emits_promoted_ir() {
    let dir = tempfile::tempdir().unwrap();
    let src = dir.path().join("prog.ril");
    fs::write(
        &src,
        r#"
type Point = .{ var x: int, var y: int }
fn main() @io -> () {
    var total = 0
    for 0..40 as i {
        let mut p = Point.{ x: i, y: i + 1 }
        p.x += p.y
        total += p.x
    }
    println(String::inspect(total))
}
"#,
    )
    .unwrap();

    for backend in ["jit", "aot"] {
        for flag in [None, Some("--opt-stack-promote")] {
            let mut cmd = Command::new(ril_bin());
            cmd.args(["run", "--backend", backend]);
            if let Some(flag) = flag {
                cmd.arg(flag);
            }
            cmd.arg(&src);
            let output = cmd.output().unwrap();
            assert!(
                output.status.success(),
                "{backend} {flag:?} failed: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert_eq!(String::from_utf8_lossy(&output.stdout), "1600\n");
        }
    }

    let base_ir = Command::new(ril_bin())
        .args(["emit-ir", "--format", "mir"])
        .arg(&src)
        .output()
        .unwrap();
    let opt_ir = Command::new(ril_bin())
        .args(["emit-ir", "--format", "mir", "--opt-stack-promote"])
        .arg(&src)
        .output()
        .unwrap();
    assert!(base_ir.status.success() && opt_ir.status.success());
    assert!(String::from_utf8_lossy(&base_ir.stdout).contains("ril_rt_record"));
    assert!(!String::from_utf8_lossy(&opt_ir.stdout).contains("ril_rt_record"));
}

#[test]
fn cli_incremental_cache_reuses_and_invalidates_on_source_dep_and_option_changes() {
    let dir = tempfile::tempdir().unwrap();
    let cache = dir.path().join("cache");
    let dep_dir = dir.path().join("dep");
    let pkg_dir = dir.path().join("pkg");
    fs::create_dir_all(&dep_dir).unwrap();
    fs::create_dir_all(&pkg_dir).unwrap();

    let dep_src = dep_dir.join("cell.ril");
    let dep_rili = dep_dir.join("cell.rili");
    fs::write(
        &dep_src,
        "pub type Cell = .{ var count: int }\npub fn read(via c: Cell) -> int { c.count }\n",
    )
    .unwrap();
    let emit = Command::new(ril_bin())
        .args(["check", "--unit", "lib", "--emit-interface"])
        .arg(&dep_rili)
        .arg("--incremental")
        .arg(&cache)
        .arg(&dep_src)
        .output()
        .unwrap();
    assert!(
        emit.status.success(),
        "{}",
        String::from_utf8_lossy(&emit.stderr)
    );
    // Remove dep source so client consumes dep/cell.rili exclusively.
    fs::remove_file(&dep_src).unwrap();

    let client = pkg_dir.join("main.ril");
    fs::write(
        &client,
        "use dep/cell\nfn use_cell(ref c: Cell::Cell) -> int { Cell::read(ref c) }\n",
    )
    .unwrap();

    // Cold and warm check with --incremental.
    for _ in 0..2 {
        let out = Command::new(ril_bin())
            .args(["check", "--unit", "lib", "--incremental"])
            .arg(&cache)
            .arg(&client)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
    }

    // Update dep/cell.rili to require mutation -> client check must invalidate and fail with E0520.
    fs::write(
        &dep_src,
        "pub type Cell = .{ var count: int }\npub fn read(via c: Cell) -> int { c.count += 1; c.count }\n",
    )
    .unwrap();
    let emit_v2 = Command::new(ril_bin())
        .args(["check", "--unit", "lib", "--emit-interface"])
        .arg(&dep_rili)
        .arg("--incremental")
        .arg(&cache)
        .arg(&dep_src)
        .output()
        .unwrap();
    assert!(emit_v2.status.success());
    fs::remove_file(&dep_src).unwrap();

    let failed = Command::new(ril_bin())
        .args(["check", "--unit", "lib", "--incremental"])
        .arg(&cache)
        .arg(&client)
        .output()
        .unwrap();
    assert!(!failed.status.success());
    assert!(String::from_utf8_lossy(&failed.stderr).contains("E0520"));

    // Build executable with --incremental, then edit source and toggle --opt-stack-promote.
    let app = pkg_dir.join("app.ril");
    let exe = dir.path().join("app_bin");
    fs::write(&app, "fn main() @io -> () { println(\"v1\") }\n").unwrap();
    for flag in [None, Some("--opt-stack-promote")] {
        let mut cmd = Command::new(ril_bin());
        cmd.args(["build", "--incremental"])
            .arg(&cache)
            .arg("-o")
            .arg(&exe);
        if let Some(flag) = flag {
            cmd.arg(flag);
        }
        cmd.arg(&app);
        let built = cmd.output().unwrap();
        assert!(
            built.status.success(),
            "{}",
            String::from_utf8_lossy(&built.stderr)
        );
        let run = Command::new(&exe).output().unwrap();
        assert_eq!(String::from_utf8_lossy(&run.stdout), "v1\n");
    }

    fs::write(&app, "fn main() @io -> () { println(\"v2\") }\n").unwrap();
    let rebuilt = Command::new(ril_bin())
        .args(["build", "--incremental"])
        .arg(&cache)
        .arg("-o")
        .arg(&exe)
        .arg(&app)
        .output()
        .unwrap();
    assert!(rebuilt.status.success());
    let run = Command::new(&exe).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), "v2\n");
}
