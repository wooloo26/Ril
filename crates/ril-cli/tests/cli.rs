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
use ril/io
type Point = .{ var x: int, var y: int }
fn main() @io -> () {
    var total = 0
    for 0..40 as i {
        let mut p = Point.{ x: i, y: i + 1 }
        p.x += p.y
        total += p.x
    }
    Io::println(String::inspect(total))
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
    fs::write(
        &app,
        "use ril/io\nfn main() @io -> () { Io::println(\"v1\") }\n",
    )
    .unwrap();
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

    fs::write(
        &app,
        "use ril/io\nfn main() @io -> () { Io::println(\"v2\") }\n",
    )
    .unwrap();
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

#[test]
fn cli_fmt_check_std_examples_run_hello_and_spawn_lsp() {
    use std::io::Write as _;
    use std::process::Stdio;

    let repo_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let std_dir = repo_root.join("std");
    let examples_dir = repo_root.join("examples");
    let hello_dir = examples_dir.join("hello");

    // 1. Verify `ril fmt --check` passes on 100% of std/ and examples/
    let fmt_check = Command::new(ril_bin())
        .args(["fmt", "--check"])
        .arg(&std_dir)
        .arg(&examples_dir)
        .output()
        .unwrap();
    assert!(
        fmt_check.status.success(),
        "ril fmt --check failed:\n{}",
        String::from_utf8_lossy(&fmt_check.stderr)
    );

    // 2. Run multi-module `examples/hello` package via `ril run`
    let run_hello = Command::new(ril_bin())
        .arg("run")
        .arg(&hello_dir)
        .output()
        .unwrap();
    assert!(
        run_hello.status.success(),
        "ril run examples/hello failed:\n{}",
        String::from_utf8_lossy(&run_hello.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&run_hello.stdout), "hello-ok\n");

    // 3. Spawn the real `ril lsp` binary over stdio and verify initialize + didOpen + shutdown
    let main_path = hello_dir.join("src/main.ril").canonicalize().unwrap();
    let main_text = fs::read_to_string(&main_path).unwrap();
    let mut child = Command::new(ril_bin())
        .arg("lsp")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let frame = |body: &str| format!("Content-Length: {}\r\n\r\n{body}", body.len());
    let init = r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#;
    let open = format!(
        r#"{{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{{"textDocument":{{"uri":"file://{}","languageId":"ril","version":1,"text":{}}}}}}}"#,
        main_path.display(),
        serde_json_escape(&main_text)
    );
    let shutdown = r#"{"jsonrpc":"2.0","id":2,"method":"shutdown","params":null}"#;
    let exit = r#"{"jsonrpc":"2.0","method":"exit"}"#;
    {
        let mut stdin = child.stdin.take().unwrap();
        stdin
            .write_all(
                format!(
                    "{}{}{}{}",
                    frame(init),
                    frame(&open),
                    frame(shutdown),
                    frame(exit)
                )
                .as_bytes(),
            )
            .unwrap();
    }
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "ril lsp exited with {:?}: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("\"hoverProvider\":true"));
    assert!(stdout.contains("\"diagnostics\":[]"));
}

#[test]
fn cli_test_doc_validates_stdlib_and_rejects_broken_examples() {
    let repo_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let std_dir = repo_root.join("std");
    let std_out = Command::new(ril_bin())
        .args(["test", "--doc"])
        .arg(&std_dir)
        .output()
        .unwrap();
    assert!(
        std_out.status.success(),
        "ril test --doc std failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&std_out.stdout),
        String::from_utf8_lossy(&std_out.stderr)
    );
    let stdout = String::from_utf8_lossy(&std_out.stdout);
    assert!(
        stdout.contains("0 failed") && !stdout.starts_with("0 passed"),
        "unexpected ril test --doc std output: {stdout}"
    );

    let dir = tempfile::tempdir().unwrap();
    let bad = dir.path().join("bad_doc.ril");
    fs::write(
        &bad,
        "-- Broken example\n--\n-- ```ril\n-- @Tag(\"pk\") type User(.{ id: int })\n-- ```\npub fn ok() -> () {}\n",
    )
    .unwrap();
    let bad_out = Command::new(ril_bin())
        .args(["test", "--doc"])
        .arg(&bad)
        .output()
        .unwrap();
    assert!(
        !bad_out.status.success(),
        "expected broken doc example to fail, got stdout: {}",
        String::from_utf8_lossy(&bad_out.stdout)
    );

    let ignored = dir.path().join("ignored_doc.ril");
    fs::write(
        &ignored,
        "-- Ignored pseudocode + checked no_run\n--\n-- ```ril,ignore\n-- @NotRealRil syntax\n-- ```\n--\n-- ```ril,no_run\n-- let x = 1 + 2\n-- ```\npub fn ok() -> () {}\n",
    )
    .unwrap();
    let ok_out = Command::new(ril_bin())
        .args(["test", "--doc"])
        .arg(&ignored)
        .output()
        .unwrap();
    assert!(
        ok_out.status.success(),
        "expected ignore + no_run doc test to pass: {}",
        String::from_utf8_lossy(&ok_out.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&ok_out.stdout),
        "1 passed, 0 failed\n"
    );
}

fn serde_json_escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for ch in text.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
