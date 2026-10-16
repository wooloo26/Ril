//! Real host waits must stop and join before structured cancellation completes.
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{Duration, Instant},
};

fn build(directory: &Path, path: &Path, operation: &str) -> PathBuf {
    let path = serde_json::to_string(&path.to_string_lossy()).unwrap();
    let operation = operation.replace("PATH", &path);
    let source = format!(
        r#"
use ril/file
use ril/path
use ril/concurrent::{{scope, TaskFault}}
use ril/time
pub fn main() @Async {{
    let result = scope \mut s -> {{
        s.fork(\-> {{ Time::sleep(Time::duration_nanos(100000000i64)); panic("cancel filesystem") }})
        {operation}
        panic("filesystem wait returned before cancellation")
        Ok()
    }}
    match result {{
        Err(TaskFault::Panicked(info)) -> assert(info.message == "cancel filesystem"),
        _ -> panic("filesystem cancellation did not preserve the child fault"),
    }}
}}
"#
    );
    let source_path = directory.join("filesystem.ril");
    let executable = directory.join(if cfg!(windows) {
        "filesystem.exe"
    } else {
        "filesystem"
    });
    fs::write(&source_path, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("build")
        .arg(source_path)
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
    executable
}

fn execute(executable: &Path, directory: &Path) {
    let errors = directory.join("stderr");
    let mut child = Command::new(executable)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(fs::File::create(&errors).unwrap())
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(8);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("filesystem cancellation did not stop and join its host operation");
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    assert!(status.success(), "{}", fs::read_to_string(errors).unwrap());
}

#[cfg(target_os = "linux")]
#[test]
fn native_fifo_open_and_whole_file_open_waits_are_cancelled() {
    for operation in [
        "let scoped mut file = File::open_path(Path::from_string(PATH), File::OpenMode::Read) ?? \\error -> panic(error.message)",
        "let result = File::read_bytes(Path::from_string(PATH)); assert(result is Ok(_))",
        "let result = File::write_bytes(Path::from_string(PATH), b\"x\"); assert(result is Ok())",
    ] {
        let directory = tempfile::tempdir().unwrap();
        let fifo = directory.path().join("blocked.fifo");
        assert!(
            Command::new("mkfifo")
                .arg(&fifo)
                .status()
                .unwrap()
                .success()
        );
        let executable = build(directory.path(), &fifo, operation);
        execute(&executable, directory.path());
    }
}

#[cfg(windows)]
#[test]
fn native_whole_named_pipe_read_cancels_after_a_prefix_without_waiting_for_eof() {
    use std::io::{BufRead, BufReader};
    // The fixture is a separate native process so its ordinary pipe writer can
    // remain alive until the Ril executable has completed cancellation.
    const HELPER: &str = r#"
use std::{ffi::c_void,io::{Read,Write},os::windows::io::FromRawHandle};
#[link(name="kernel32")]
unsafe extern "system"{
 fn CreateNamedPipeW(name:*const u16,access:u32,mode:u32,max:u32,out:u32,input:u32,timeout:u32,security:*const c_void)->*mut c_void;
 fn ConnectNamedPipe(handle:*mut c_void,overlapped:*mut c_void)->i32;
}
fn main(){
 let path=std::env::args().nth(1).unwrap();let marker=std::env::args().nth(2).unwrap();
 let name:Vec<u16>=path.encode_utf16().chain([0]).collect();
 let handle=unsafe{CreateNamedPipeW(name.as_ptr(),2,8,1,65536,65536,0,std::ptr::null())};
 assert_ne!(handle as isize,-1,"{}",std::io::Error::last_os_error());
 println!("ready");std::io::stdout().flush().unwrap();
 let connected=unsafe{ConnectNamedPipe(handle,std::ptr::null_mut())};
 assert!(connected!=0||std::io::Error::last_os_error().raw_os_error()==Some(535));
 let mut file=unsafe{std::fs::File::from_raw_handle(handle)};
 file.write_all(b"prefix").unwrap();std::fs::write(marker,b"connected").unwrap();
 let mut hold=[0];let _=std::io::stdin().read(&mut hold);
}
"#;
    struct Helper(std::process::Child);
    impl Drop for Helper {
        fn drop(&mut self) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
    let directory = tempfile::tempdir().unwrap();
    let pipe = PathBuf::from(format!(
        r"\\.\pipe\ril-filesystem-{}-{}",
        std::process::id(),
        directory.path().file_name().unwrap().to_string_lossy()
    ));
    let executable = build(
        directory.path(),
        &pipe,
        "let result = File::read_bytes(Path::from_string(PATH)); assert(result is Ok(_))",
    );
    let source = directory.path().join("pipe.rs");
    let helper_exe = directory.path().join("pipe.exe");
    fs::write(&source, HELPER).unwrap();
    let output = Command::new("rustc")
        .args(["--edition=2024", "--crate-name=ril_pipe_fixture"])
        .arg(source)
        .arg("-o")
        .arg(&helper_exe)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let marker = directory.path().join("connected");
    let mut helper = Helper(
        Command::new(helper_exe)
            .arg(&pipe)
            .arg(&marker)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap(),
    );
    let mut ready = String::new();
    BufReader::new(helper.0.stdout.take().unwrap())
        .read_line(&mut ready)
        .unwrap();
    assert_eq!(ready.trim(), "ready");
    execute(&executable, directory.path());
    assert_eq!(fs::read(marker).unwrap(), b"connected");
}
