use std::{
    fs,
    process::{Child, Command, Stdio},
    thread,
    time::{Duration, Instant},
};

pub fn executes(source: &str, label: &str) {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("program.ril");
    let stdout = directory.path().join("stdout.json");
    let stderr = directory.path().join("stderr.log");
    fs::write(&input, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_ril"));
    command
        .arg("test")
        .arg(input)
        .args(["--entry", "test_native", "--json"])
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
            panic!("native case {label} exceeded 20 seconds");
        }
        thread::sleep(Duration::from_millis(10));
    };
    let output = fs::read(&stdout).unwrap();
    let report: serde_json::Value = serde_json::from_slice(&output).unwrap_or_else(|error| {
        panic!(
            "{label}: {error}\n{}\n{}",
            String::from_utf8_lossy(&output),
            fs::read_to_string(&stderr).unwrap()
        )
    });
    assert!(status.success(), "{label}: {report}");
    assert_eq!(report["status"], "executed", "{label}: {report}");
    assert_eq!(report["runtime"], "returned-unit", "{label}: {report}");
    assert_eq!(report["exit"], 0, "{label}: {report}");
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
