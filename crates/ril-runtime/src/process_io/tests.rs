use super::*;
use std::process::Stdio;
fn fixture(mode: &str) -> Command {
    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args([
            "--exact",
            "process_io::tests::child_fixture",
            "--ignored",
            "--nocapture",
        ])
        .env("RIL_PROCESS_IO_FIXTURE", mode)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    command
}
#[test]
#[ignore = "invoked in a separate process by the transfer and cancellation tests"]
fn child_fixture() {
    let Ok(mode) = std::env::var("RIL_PROCESS_IO_FIXTURE") else {
        return;
    };
    match mode.as_str() {
        "duplex" => {
            std::io::stdout()
                .lock()
                .write_all(&vec![b'o'; 128 * 1024])
                .unwrap();
            std::io::stderr()
                .lock()
                .write_all(&vec![b'e'; 128 * 1024])
                .unwrap();
            let mut input = vec![];
            std::io::stdin().read_to_end(&mut input).unwrap();
            assert_eq!(input, vec![b'i'; 1024 * 1024]);
            println!("input={}", input.len());
            std::process::exit(7);
        }
        "limit" => {
            std::io::stdout()
                .lock()
                .write_all(&vec![b'o'; 50_000])
                .unwrap();
            std::io::stderr()
                .lock()
                .write_all(&vec![b'e'; 50_000])
                .unwrap();
            thread::sleep(Duration::from_secs(30));
        }
        "sleep" => thread::sleep(Duration::from_secs(30)),
        "signal_sleep" => {
            std::fs::write(
                std::env::var_os("RIL_PROCESS_IO_READY").expect("ready path"),
                b"ready",
            )
            .unwrap();
            thread::sleep(Duration::from_secs(30));
        }
        _ => panic!("unknown isolated process fixture"),
    }
}
#[test]
fn data_input_and_both_captures_are_pumped_concurrently_without_deadlock() {
    let output = run(
        fixture("duplex"),
        Some(vec![b'i'; 1024 * 1024]),
        1024 * 1024,
        Arc::new(Cancellation::default()),
    )
    .unwrap();
    assert_eq!(output.status.code(), Some(7));
    assert!(String::from_utf8_lossy(&output.stdout).contains("input=1048576"));
    assert_eq!(output.stderr, vec![b'e'; 128 * 1024]);
}
#[test]
fn combined_capture_limit_terminates_reaps_and_joins_all_transfers() {
    let started = std::time::Instant::now();
    let request = Arc::new(Cancellation::default());
    let output = run(fixture("limit"), Some(vec![]), 80_000, request.clone());
    assert!(matches!(output, Err(RunError::CaptureLimit)), "{output:?}");
    assert!(started.elapsed() < Duration::from_secs(5));
    assert!(
        !request.requested(),
        "capture limit is an ordinary failure, not task cancellation"
    );
}
#[test]
fn cancellation_wakes_a_blocked_input_worker_and_reaps_the_child() {
    let cancel = Arc::new(Cancellation::default());
    let request = cancel.clone();
    let canceller = thread::spawn(move || {
        thread::sleep(Duration::from_millis(100));
        request.request();
    });
    let started = std::time::Instant::now();
    let output = run(
        fixture("sleep"),
        Some(vec![b'x'; 2 * 1024 * 1024]),
        1024 * 1024,
        cancel,
    );
    canceller.join().unwrap();
    assert!(matches!(output, Err(RunError::Cancelled)), "{output:?}");
    assert!(started.elapsed() < Duration::from_secs(5));
}
