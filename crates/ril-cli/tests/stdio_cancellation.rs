//! Cancellation must reap the blocked host transfer before a scope can return.
use std::{
    fs,
    process::{Command, Stdio},
    time::{Duration, Instant},
};

fn source(operation: &str) -> String {
    format!(
        r#"
use ril/concurrent::{{scope, TaskFault}}
use ril/io
use ril/time
pub fn main() @Async {{
    let result = scope \mut s -> {{
        s.fork(\-> {{ Time::sleep(Time::duration_nanos(100000000i64)); panic("child") }})
        {operation}
        panic("blocked transfer returned before cancellation")
        Ok()
    }}
    assert(result is Err(TaskFault::Panicked(_)))
}}
"#
    )
}

fn cancels(operation: &str) {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("stdio.ril");
    let executable = directory
        .path()
        .join(if cfg!(windows) { "stdio.exe" } else { "stdio" });
    fs::write(&input, source(operation)).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("build")
        .arg(input)
        .args(["--unit", "executable", "--output"])
        .arg(&executable)
        .arg("--json")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let errors = directory.path().join("stderr");
    let mut child = Command::new(executable)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(fs::File::create(&errors).unwrap())
        .spawn()
        .unwrap();
    // Keep both ends alive: no EOF or drained output may unblock the request.
    let deadline = Instant::now() + Duration::from_secs(5);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("cancellation did not reap the blocked standard stream transfer");
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    assert!(status.success(), "{}", fs::read_to_string(errors).unwrap());
}

#[test]
fn child_failure_cancels_standard_input_without_fabricating_eof() {
    cancels("let result = Io::stdin_read(1); assert(result is Ok(_))");
}

#[test]
fn child_failure_cancels_standard_output_without_a_drain() {
    let payload = "x".repeat(1024 * 1024);
    cancels(&format!(
        "loop {{ let progress = Io::stdout_write(b\"{payload}\"); assert(progress.error == None) }}"
    ));
}

#[test]
fn child_failure_cancels_print_and_println_through_the_host_bridge() {
    let payload = serde_json::to_string(&"x".repeat(1024 * 1024)).unwrap();
    for operation in ["print", "println"] {
        cancels(&format!("{operation}({payload})"));
    }
}
