use std::{
    fs,
    process::{Child, Command, Stdio},
    thread,
    time::{Duration, Instant},
};

// Preserve the original split program, including both forwarding wrappers.
// Each test verifies this complete source in a fresh CLI process before running
// its selected entry. The original single-entry proof-budget gap is not run.
const SOURCE: &str = include_str!(
    "../../ril-compiler/tests/fixtures/channel_message_optional_callback_source_index_checked.ril"
);

fn executes(entry: &str) {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("program.ril");
    let stdout = directory.path().join("stdout.json");
    let stderr = directory.path().join("stderr.log");
    fs::write(&input, SOURCE).unwrap();
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
            panic!("source-index entry {entry} exceeded 20 seconds");
        }
        thread::sleep(Duration::from_millis(10));
    };
    let output = fs::read(&stdout).unwrap();
    let report: serde_json::Value = serde_json::from_slice(&output).unwrap_or_else(|error| {
        panic!(
            "{entry}: {error}\n{}\n{}",
            String::from_utf8_lossy(&output),
            fs::read_to_string(&stderr).unwrap()
        )
    });
    assert!(status.success(), "{entry}: {report}");
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
fn preserved_split_alias_route_executes_all_three_optional_inputs() {
    executes("test_native");
}

#[test]
fn preserved_split_named_forwarding_executes_all_three_optional_inputs() {
    executes("test_named_native");
}

#[test]
fn preserved_split_singleton_map_executes_all_three_optional_inputs() {
    executes("test_single_map_native");
}
