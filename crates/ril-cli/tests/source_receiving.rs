//! Pending native gate for original-source receiving. Each entry uses a fresh
//! CLI, executable and directory; all diagnostics, NI and timeouts are failures.
use std::{
    fs,
    process::{Child, Command, Stdio},
    thread,
    time::{Duration, Instant},
};

fn source_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/source-receiving.ril::source-receiving-native")
}

fn executes(entry: &str) {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("program.ril");
    let stdout = directory.path().join("stdout.json");
    let stderr = directory.path().join("stderr.log");
    fs::write(&input, source_fixture()).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_ril"));
    command
        .arg("test")
        .arg(input)
        .args(["--entry", entry, "--json"])
        .stdout(Stdio::from(fs::File::create(&stdout).unwrap()))
        .stderr(Stdio::from(fs::File::create(&stderr).unwrap()));
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        command.process_group(0);
    }
    #[cfg(windows)]
    {
        use std::os::windows::process::CommandExt;
        command.creation_flags(0x0800_0000);
    }
    let mut child = command.spawn().unwrap();
    let deadline = Instant::now() + Duration::from_secs(20);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() >= deadline {
            terminate_tree(&mut child);
            panic!("receiving entry {entry} exceeded 20 seconds");
        }
        thread::sleep(Duration::from_millis(10));
    };
    let output = fs::read(&stdout).unwrap();
    let error_output = fs::read_to_string(&stderr).unwrap();
    let report: serde_json::Value = serde_json::from_slice(&output).unwrap_or_else(|error| {
        panic!(
            "{entry}: {error}\n{}\n{error_output}",
            String::from_utf8_lossy(&output)
        )
    });
    assert!(status.success(), "{entry}: {report}\n{error_output}");
    assert_eq!(report["status"], "executed", "{entry}: {report}");
    assert_eq!(report["runtime"], "returned-unit", "{entry}: {report}");
    assert_eq!(report["exit"], 0, "{entry}: {report}");
}

fn terminate_tree(child: &mut Child) {
    #[cfg(windows)]
    {
        use std::os::windows::process::CommandExt;
        let _ = Command::new("taskkill")
            .args(["/PID", &child.id().to_string(), "/T", "/F"])
            .creation_flags(0x0800_0000)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
    }
    #[cfg(unix)]
    {
        let _ = Command::new("kill")
            .args(["-KILL", "--", &format!("-{}", child.id())])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
    }
    let _ = child.kill();
    let _ = child.wait();
}

#[test]
fn fresh_fixed_array_executes() {
    executes("test_fresh_fixed");
}
#[test]
fn fresh_empty_tuple_and_typed_record_execute() {
    executes("test_empty_composites");
}
#[test]
fn correct_named_and_contextual_callback_execute() {
    executes("test_callback");
}
#[test]
fn if_match_and_explicit_returns_execute() {
    executes("test_return_branches");
}
#[test]
fn ordinary_inferred_calls_execute() {
    executes("test_ordinary");
}
#[test]
fn actual_default_and_supplied_calls_execute() {
    executes("test_default");
}
#[test]
fn explicit_generic_calls_execute() {
    executes("test_explicit_generic");
}
