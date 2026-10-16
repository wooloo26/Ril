use super::*;
use ril_runtime_api::foreign::{Argument, EntryKind, Graph, Node, PROTOCOL_VERSION};
use std::{fs, path::Path, time::Instant};

const FIXTURE: &str = r###"
use std::io::{Read,Write};
fn send(message:&str){let mut out=std::io::stdout().lock();out.write_all(&(message.len() as u64).to_le_bytes()).unwrap();out.write_all(message.as_bytes()).unwrap();out.flush().unwrap();}
fn receive()->String{let mut input=std::io::stdin().lock();let mut header=[0;8];input.read_exact(&mut header).unwrap();let mut bytes=vec![0;u64::from_le_bytes(header) as usize];input.read_exact(&mut bytes).unwrap();String::from_utf8(bytes).unwrap()}
fn main(){
 std::env::set_current_dir(std::env::current_exe().unwrap().parent().unwrap()).unwrap();
 let mode=std::env::args().nth(1).unwrap();
 if mode=="malformed"{send(r#"{"kind":"ready","version":1,"unknown":true}"#);return;}
 send(r#"{"kind":"ready","version":1}"#);
 if mode=="oversize"{std::io::stdout().write_all(&4096u64.to_le_bytes()).unwrap();std::io::stdout().flush().unwrap();std::thread::sleep(std::time::Duration::from_secs(30));return;}
 let request=receive();assert!(request.contains("foreign::value"));
 if mode=="crash"{std::process::abort();}
 if mode=="wait"{loop{std::thread::sleep(std::time::Duration::from_secs(1));}}
 if mode=="truncated"{let mut out=std::io::stdout();out.write_all(&50u64.to_le_bytes()).unwrap();out.write_all(b"x").unwrap();return;}
 if mode=="callback"{
   send(r#"{"kind":"callback","call":7,"request":1,"token":3,"arguments":{"nodes":[{"kind":"string","value":"hello"}],"roots":[0]}}"#);
   let answer=receive();assert!(answer.contains("callback_return"));assert!(answer.contains("HELLO"));
 }
 send(r#"{"kind":"return","call":7,"values":{"nodes":[{"kind":"array","value":[0,1,1]},{"kind":"integer","value":{"decimal":"42","bits":64,"signed":true}}],"roots":[0]}}"#);
 if mode=="exit-failure"{std::process::exit(17);}
}
"###;

fn build(directory: &Path) -> std::path::PathBuf {
    let source = directory.join("provider.rs");
    let executable = directory.join(if cfg!(windows) {
        "provider.exe"
    } else {
        "provider"
    });
    fs::write(&source, FIXTURE).unwrap();
    let rustc = std::env::var_os("RUSTC")
        .or_else(|| {
            std::env::var_os("CARGO").and_then(|cargo| {
                let cargo = std::path::PathBuf::from(cargo);
                let compiler =
                    cargo
                        .parent()?
                        .join(if cfg!(windows) { "rustc.exe" } else { "rustc" });
                compiler.is_file().then(|| compiler.into_os_string())
            })
        })
        .unwrap_or_else(|| "rustc".into());
    let output = Command::new(rustc)
        .arg("--edition=2024")
        .arg("--crate-name=ril_provider_fixture")
        .arg(&source)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    executable
}
fn config(executable: &Path, mode: &str) -> ProviderConfig {
    ProviderConfig {
        id: "fixture".into(),
        program: executable.into(),
        args: vec![mode.into()],
        max_frame_bytes: 1024,
    }
}
fn invocation() -> ClientMessage {
    ClientMessage::Invoke {
        version: PROTOCOL_VERSION,
        call: 7,
        entry: EntryKind::Function,
        declaration: "foreign::value".into(),
        export: "value".into(),
        static_arguments: vec![],
        signature: ril_runtime_api::foreign::Signature {
            arena: vec![
                ril_runtime_api::foreign::TypeNode::Callback,
                ril_runtime_api::foreign::TypeNode::Unit,
            ],
            parameters: vec![0],
            result: 1,
            callbacks: vec![],
        },
        values: Graph {
            nodes: vec![Node::Unit],
            roots: vec![0],
        },
        arguments: vec![Argument::Callback(3)],
    }
}

#[test]
fn native_provider_protocol_reaps_returns_callbacks_traps_and_cancelled_waits() {
    let directory = tempfile::tempdir().unwrap();
    let executable = build(directory.path());
    for mode in [
        "normal",
        "callback",
        "exit-failure",
        "truncated",
        "crash",
        "wait",
        "oversize",
        "malformed",
    ] {
        let cancellation = Arc::new(Cancellation::default());
        let mut session = Session::start(&config(&executable, mode), cancellation.clone()).unwrap();
        if mode == "malformed" {
            assert!(matches!(session.next(), Err(Failure::Binding(_))));
            assert!(session.closed && session.status.is_some());
            continue;
        }
        assert_eq!(
            session.next().unwrap(),
            ProviderMessage::Ready {
                version: PROTOCOL_VERSION
            }
        );
        if mode == "oversize" {
            assert!(
                matches!(session.next(), Err(Failure::Binding(message)) if message.contains("limit"))
            );
            assert!(session.closed && session.status.is_some());
            continue;
        }
        session.send(&invocation()).unwrap();
        if mode == "wait" {
            let cancel = thread::spawn(move || {
                thread::sleep(Duration::from_millis(30));
                cancellation.request();
            });
            let start = Instant::now();
            assert_eq!(session.next().unwrap_err(), Failure::Cancelled);
            assert!(start.elapsed() < Duration::from_secs(5));
            cancel.join().unwrap();
        } else if matches!(mode, "crash" | "truncated") {
            assert!(matches!(session.next(), Err(Failure::Binding(_))));
        } else {
            if mode == "callback" {
                let ProviderMessage::Callback {
                    call,
                    request,
                    token,
                    arguments,
                } = session.next().unwrap()
                else {
                    panic!("callback request")
                };
                assert_eq!((call, request, token), (7, 1, 3));
                arguments.validate().unwrap();
                session
                    .send(&ClientMessage::CallbackReturn {
                        call,
                        request,
                        values: Graph {
                            nodes: vec![Node::String("HELLO".into())],
                            roots: vec![0],
                        },
                    })
                    .unwrap();
            }
            let ProviderMessage::Return { call, values } = session.next().unwrap() else {
                panic!("ordinary return")
            };
            assert_eq!(call, 7);
            values.validate().unwrap();
            assert_eq!(values.nodes[0], Node::Array(vec![0, 1, 1]));
            if mode == "exit-failure" {
                assert!(matches!(session.finish(), Err(Failure::Binding(_))));
            } else {
                session.finish().unwrap();
            }
        }
        assert!(
            session.closed && session.status.is_some() && session.workers.is_empty(),
            "{mode}"
        );
    }
    let mut session = Session::start(&config(&executable, "wait"), Arc::default()).unwrap();
    session.next().unwrap();
    session.send(&invocation()).unwrap();
    session.abort().unwrap();
    assert!(session.closed && session.status.is_some() && session.workers.is_empty());
    let cancellation = Arc::new(Cancellation::default());
    let mut session = Session::start(&config(&executable, "wait"), cancellation.clone()).unwrap();
    session.next().unwrap();
    session.send(&invocation()).unwrap();
    let (wake, _received) = mpsc::channel();
    session
        .worker("injected-foreign-transport-panic", wake, || {
            panic!("injected runtime transport panic")
        })
        .unwrap();
    cancellation.request();
    assert!(matches!(session.next(), Err(Failure::Internal(_))));
    assert!(session.closed && session.status.is_some() && session.workers.is_empty());
}

#[test]
fn manifest_duplicate_bindings_and_outgoing_frame_limits_fail_explicitly() {
    assert!(serde_json::from_str::<ril_runtime_api::foreign::Manifest>(r#"{"version":1,"providers":[{"id":"test","program":"provider","bindings":{"foreign::value":"a","foreign::value":"b"}}]}"#).is_err());
    let message = ClientMessage::CallbackReturn {
        call: 1,
        request: 1,
        values: Graph {
            roots: vec![0],
            nodes: vec![Node::String("x".repeat(4096))],
        },
    };
    assert!(
        matches!(encode(&message, 1024), Err(Failure::Binding(message)) if message.contains("limit"))
    );
}
