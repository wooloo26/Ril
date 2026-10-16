use super::*;
use ril_runtime_api::foreign::{CallbackSlot, EntryKind, ProviderConfig, Signature, TypeNode};
use std::{
    fs,
    path::Path,
    process::Command,
    sync::OnceLock,
    time::{Duration, Instant},
};

const PROVIDER: &str = r###"
use std::{io::{Read,Write},path::Path,time::Duration};
fn send(message:&str){let mut out=std::io::stdout().lock();out.write_all(&(message.len() as u64).to_le_bytes()).unwrap();out.write_all(message.as_bytes()).unwrap();out.flush().unwrap();}
fn read()->String{let mut input=std::io::stdin().lock();let mut header=[0;8];input.read_exact(&mut header).unwrap();let mut bytes=vec![0;u64::from_le_bytes(header) as usize];input.read_exact(&mut bytes).unwrap();String::from_utf8(bytes).unwrap()}
fn wait(path:&str){while !Path::new(path).exists(){std::thread::sleep(Duration::from_millis(2));}}
fn main(){
 let args=std::env::args().collect::<Vec<_>>();let mode=&args[1];let ready=&args[2];let release=&args[3];
 std::fs::write(ready,std::process::id().to_string()).unwrap();
 if mode=="handshake"{wait(release);}
 send(r#"{"kind":"ready","version":1}"#);
 let input=read();let call=input.split("\"call\":").nth(1).unwrap().split(|c:char|!c.is_ascii_digit()).next().unwrap();
 if mode=="wait"{std::fs::write(format!("{ready}.waiting"),"").unwrap();loop{std::thread::sleep(Duration::from_secs(1));}}
 if mode=="callback"||mode=="abort"{
  send(&format!(r#"{{"kind":"callback","call":{call},"request":1,"token":1,"arguments":{{"nodes":[],"roots":[]}}}}"#));
  let reply=read();assert!(reply.contains("callback_return"));
 }
 send(&format!(r#"{{"kind":"return","call":{call},"values":{{"nodes":[{{"kind":"unit"}}],"roots":[0]}}}}"#));
 if mode=="finish"{wait(release);}
}
"###;

fn provider() -> &'static Path {
    static BUILT: OnceLock<(tempfile::TempDir, std::path::PathBuf)> = OnceLock::new();
    &BUILT
        .get_or_init(|| {
            let directory = tempfile::tempdir().unwrap();
            let source = directory.path().join("provider.rs");
            let executable = directory.path().join(if cfg!(windows) {
                "provider.exe"
            } else {
                "provider"
            });
            fs::write(&source, PROVIDER).unwrap();
            let output = Command::new(std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into()))
                .args(["--edition=2024", "--crate-name=ril_pending_foreign_fixture"])
                .arg(source)
                .arg("-o")
                .arg(&executable)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            (directory, executable)
        })
        .1
}
fn entered(mode: &str, directory: &Path) -> (u64, Handle, Handle) {
    ril_rt_init();
    let binding = BoundCall {
        declaration: "foreign::pending".into(),
        export: "pending".into(),
        kind: EntryKind::Function,
        static_arguments: vec![],
        provider: ProviderConfig {
            id: "pending".into(),
            program: provider().into(),
            args: vec![
                mode.into(),
                directory.join("started").display().to_string(),
                directory.join("release").display().to_string(),
            ],
            max_frame_bytes: 4096,
        },
        signature: Signature {
            arena: vec![TypeNode::Unit, TypeNode::Callback],
            parameters: vec![1],
            result: 0,
            callbacks: vec![CallbackSlot {
                argument: 0,
                path: vec![],
                mutable: false,
                parameters: vec![],
                result: 0,
            }],
        },
    };
    let (arguments, continuation, callback) = with_runtime(|runtime| {
        runtime.foreign_bindings = Arc::new(vec![Arc::new(binding)]);
        let callback = runtime.allocate(Object::Builtin("clone".into())).unwrap();
        let arguments = runtime.allocate(Object::Tuple(vec![callback])).unwrap();
        let index = runtime.integer(0, 64, true).unwrap();
        let arguments = runtime
            .allocate(Object::Tuple(vec![index, arguments]))
            .unwrap();
        let continuation = runtime
            .allocate(Object::CpsContinuation {
                state: Continuation::End,
                used: false,
            })
            .unwrap();
        (arguments, continuation, callback)
    });
    let step = enter(arguments, continuation, Handle::INVALID);
    with_runtime(|runtime| {
        let Object::CpsStep(Step::Foreign { call }) = runtime.heap.get(Handle(step)).unwrap()
        else {
            panic!("foreign entry: {:?}", runtime.fault)
        };
        (*call, runtime.foreign_calls[call].activation, callback)
    })
}
fn until<T>(mut operation: impl FnMut(&mut Context<'_>) -> Poll<T>) -> T {
    let deadline = Instant::now() + Duration::from_secs(10);
    let mut context = Context::from_waker(std::task::Waker::noop());
    loop {
        if let Poll::Ready(value) = operation(&mut context) {
            return value;
        }
        assert!(Instant::now() < deadline, "foreign wait did not complete");
        std::thread::sleep(Duration::from_millis(1));
    }
}
fn assert_live_callback(call: u64, callback: Handle) {
    with_runtime(|runtime| {
        runtime.statement_end();
        runtime.collect().unwrap();
        assert!(runtime.heap.get(callback).is_ok());
        assert!(runtime.foreign_calls.contains_key(&call));
    });
}
fn close(activation: Handle) {
    let mut pending = prepare_close(activation).unwrap();
    until(|context| poll_close(&mut pending, context)).unwrap();
    assert!(!needs_close(activation));
}

#[test]
fn handshake_and_final_exit_waits_suspend_and_keep_precise_roots() {
    for mode in ["handshake", "finish"] {
        let directory = tempfile::tempdir().unwrap();
        let (call, activation, callback) = entered(mode, directory.path());
        let mut pending = prepare(call).unwrap();
        assert!(prepare(call).is_err(), "a wait cannot start twice");
        let mut context = Context::from_waker(std::task::Waker::noop());
        if mode == "finish" {
            let step = until(|cx| poll(&mut pending, cx));
            with_runtime(|runtime| {
                assert!(
                    matches!(runtime.heap.get(Handle(step)),Ok(Object::CpsStep(Step::Foreign{call:next}))if *next==call)
                )
            });
            pending = prepare(call).unwrap();
        }
        assert!(
            poll(&mut pending, &mut context).is_pending(),
            "provider is behind an unreleased barrier"
        );
        assert_live_callback(call, callback);
        fs::write(directory.path().join("release"), "").unwrap();
        let step = until(|cx| poll(&mut pending, cx));
        assert_ne!(step, 0);
        if mode == "handshake" {
            pending = prepare(call).unwrap();
            assert_ne!(until(|cx| poll(&mut pending, cx)), 0);
        }
        assert!(
            !needs_close(activation),
            "only a reaped successful provider may disappear"
        );
    }
}

#[test]
fn callbacks_resume_on_the_owner_and_abandonment_awaits_transport_close() {
    for mode in ["callback", "abort"] {
        let directory = tempfile::tempdir().unwrap();
        let (call, activation, callback) = entered(mode, directory.path());
        let mut pending = prepare(call).unwrap();
        let step = until(|cx| poll(&mut pending, cx));
        with_runtime(|runtime| {
            assert!(
                matches!(runtime.heap.get(Handle(step)),Ok(Object::CpsStep(Step::Call{callable,callback_entry:true,..}))if *callable==callback)
            );
            assert!(matches!(
                runtime.foreign_calls[&call].transport,
                Transport::Callback(_)
            ));
        });
        assert_live_callback(call, callback);
        if mode == "abort" {
            let mut pending = prepare_close(activation).unwrap();
            assert_live_callback(call, callback);
            until(|cx| poll_close(&mut pending, cx)).unwrap();
            assert!(!needs_close(activation));
        } else {
            let value = with_runtime(|runtime| runtime.unit().unwrap());
            assert_ne!(callback_return(call, 1, value), 0);
            pending = prepare(call).unwrap();
            assert_ne!(until(|cx| poll(&mut pending, cx)), 0);
            pending = prepare(call).unwrap();
            assert_ne!(until(|cx| poll(&mut pending, cx)), 0);
            assert!(!needs_close(activation));
        }
    }
}

#[test]
fn cancellation_waits_for_provider_shutdown_before_removing_managed_state() {
    let directory = tempfile::tempdir().unwrap();
    let (call, activation, callback) = entered("wait", directory.path());
    let mut pending = prepare(call).unwrap();
    until(|context| {
        assert!(poll(&mut pending, context).is_pending());
        if directory.path().join("started.waiting").exists() {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    });
    assert_live_callback(call, callback);
    with_runtime(|runtime| runtime.cancellation.request());
    assert_eq!(until(|cx| poll(&mut pending, cx)), 0);
    with_runtime(|runtime| {
        assert_eq!(runtime.fault.as_ref().unwrap().tag, OutcomeTag::Cancelled);
        assert!(matches!(
            runtime.foreign_calls[&call].transport,
            Transport::Closed
        ));
    });
    close(activation);
}

#[test]
fn an_abandoned_unstarted_request_never_spawns_a_provider() {
    let directory = tempfile::tempdir().unwrap();
    let (call, activation, callback) = entered("wait", directory.path());
    assert_live_callback(call, callback);
    close(activation);
    assert!(!directory.path().join("started").exists());
    assert!(prepare(call).is_err());
}
