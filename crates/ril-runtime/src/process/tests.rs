use super::*;
fn tag(runtime: &Runtime, value: Handle, expected: &str) -> Vec<Handle> {
    let Object::Variant { tag, fields } = runtime.heap.get(value).unwrap() else {
        panic!("expected variant");
    };
    assert_eq!(tag, expected);
    fields.clone()
}
fn command(runtime: &mut Runtime, mode: &str) -> Handle {
    let path = runtime
        .allocate(Object::Path(NativeString::from_os(
            std::env::current_exe().unwrap().as_os_str(),
        )))
        .unwrap();
    let args = [
        "--exact",
        "process_io::tests::child_fixture",
        "--ignored",
        "--nocapture",
    ]
    .into_iter()
    .map(|arg| {
        runtime
            .allocate(Object::NativeString(NativeString::from_text(arg)))
            .unwrap()
    })
    .collect();
    let args = runtime.allocate(Object::Array(args)).unwrap();
    let command = runtime
        .process_builtin("Process::command", &[path, args])
        .unwrap();
    let key = runtime
        .allocate(Object::NativeString(NativeString::from_text(
            "RIL_PROCESS_IO_FIXTURE",
        )))
        .unwrap();
    let value = runtime
        .allocate(Object::NativeString(NativeString::from_text(mode)))
        .unwrap();
    let pair = runtime.allocate(Object::Tuple(vec![key, value])).unwrap();
    let env = runtime.allocate(Object::Array(vec![pair])).unwrap();
    let env = runtime.variant("Some", vec![env]).unwrap();
    runtime.set_field(command, "env".into(), env).unwrap();
    command
}
#[test]
fn native_process_output_preserves_unsigned_status_and_separate_capture_bytes() {
    let mut runtime = Runtime::default();
    let command = command(&mut runtime, "duplex");
    let capture = runtime
        .variant("Process::OutputMode::Capture", vec![])
        .unwrap();
    runtime
        .set_field(command, "stdout".into(), capture)
        .unwrap();
    runtime
        .set_field(command, "stderr".into(), capture)
        .unwrap();
    let data = runtime
        .allocate(Object::Bytes(vec![b'i'; 1024 * 1024].into()))
        .unwrap();
    let input = runtime.variant("Process::Input::Data", vec![data]).unwrap();
    runtime.set_field(command, "input".into(), input).unwrap();
    let result = runtime.process_builtin("Process::run", &[command]).unwrap();
    let output = tag(&runtime, result, "Ok")[0];
    let status = runtime.field(output, "status").unwrap();
    let code = tag(&runtime, status, "Process::ExitStatus::Exited")[0];
    assert_eq!(runtime.as_integer(code).unwrap(), 7);
    let success = runtime
        .process_builtin("Process::success", &[status])
        .unwrap();
    assert!(!runtime.truth(success).unwrap());
    let stderr = runtime.field(output, "stderr").unwrap();
    assert_eq!(runtime.as_bytes(stderr).unwrap(), vec![b'e'; 128 * 1024]);
}
#[test]
fn standalone_child_cannot_copy_and_repeated_wait_observes_the_same_real_status() {
    let mut runtime = Runtime::default();
    let command = command(&mut runtime, "sleep");
    let null = runtime
        .variant("Process::OutputMode::Null", vec![])
        .unwrap();
    runtime.set_field(command, "stdout".into(), null).unwrap();
    runtime.set_field(command, "stderr".into(), null).unwrap();
    let result = runtime
        .process_builtin("Process::spawn", &[command])
        .unwrap();
    let child = tag(&runtime, result, "Ok")[0];
    assert_eq!(
        runtime.heap.deep_clone(child),
        Err(crate::heap::HeapError::NonClonable)
    );
    let result = runtime
        .process_builtin("Process::terminate", &[child])
        .unwrap();
    tag(&runtime, result, "Ok");
    let first = runtime.process_builtin("Process::wait", &[child]).unwrap();
    let second = runtime.process_builtin("Process::wait", &[child]).unwrap();
    assert!(runtime.heap.structurally_equal(first, second).unwrap());
    assert!(runtime.children[0].lock().unwrap().observed.is_some());
}
#[test]
fn invalid_commands_never_launch_and_negative_limit_precedes_validation() {
    let mut runtime = Runtime::default();
    let path = runtime
        .allocate(Object::Path(NativeString::from_text("invalid\0path")))
        .unwrap();
    let arguments = runtime.allocate(Object::Array(vec![])).unwrap();
    let command = runtime
        .process_builtin("Process::command", &[path, arguments])
        .unwrap();
    let result = runtime.process_builtin("Process::run", &[command]).unwrap();
    let error = tag(&runtime, result, "Err")[0];
    tag(&runtime, error, "Process::ProcessError::InvalidCommand");
    let negative = runtime.int(-1).unwrap();
    assert_eq!(
        runtime
            .process_builtin("Process::run", &[command, negative])
            .unwrap_err()
            .tag,
        ril_runtime_api::abi::OutcomeTag::LanguagePanic
    );
    assert!(runtime.children.is_empty());
}

#[test]
fn cancelling_an_active_wait_keeps_the_child_authority_for_owning_cleanup() {
    use std::{
        sync::mpsc,
        time::{Duration, Instant},
    };
    let mut runtime = Runtime::default();
    let command = command(&mut runtime, "sleep");
    let null = runtime
        .variant("Process::OutputMode::Null", vec![])
        .unwrap();
    runtime.set_field(command, "stdout".into(), null).unwrap();
    runtime.set_field(command, "stderr".into(), null).unwrap();
    let result = runtime
        .process_builtin("Process::spawn", &[command])
        .unwrap();
    let child = tag(&runtime, result, "Ok")[0];
    let authority = runtime.children[0].clone();
    let request = host::prepare(&mut runtime, "Process::wait", &[child]).unwrap();
    let (send, answer) = mpsc::channel();
    let worker = std::thread::spawn(move || {
        send.send(request.perform().map(|_| ()).map_err(|error| error.tag))
            .unwrap();
    });
    // The host mutex proves the wait actually started; no timing sleep is used
    // to guess whether cancellation happened before invocation.
    let start = Instant::now();
    let mut waiting = false;
    while start.elapsed() < Duration::from_secs(3) {
        if authority.try_lock().is_err() {
            waiting = true;
            break;
        }
        std::thread::yield_now();
    }
    runtime.cancellation.request();
    let observed = answer.recv_timeout(Duration::from_secs(3));
    worker.join().unwrap();
    // Cancellation does not terminate a standalone wait's child. The owner
    // still has real cleanup authority even with its token already cancelled.
    assert!(runtime.release_child(child).unwrap());
    assert!(authority.lock().unwrap().observed.is_some());
    assert!(waiting);
    assert_eq!(
        observed.unwrap(),
        Err(ril_runtime_api::abi::OutcomeTag::Cancelled)
    );
}
