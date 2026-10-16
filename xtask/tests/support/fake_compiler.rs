//! Subprocess fixture only: this program does not parse or implement Ril.
use std::{
    env, fs,
    io::{self, Read, Write},
    path::{Path, PathBuf},
    process::{self, Command, Stdio},
    thread,
    time::Duration,
};

fn option(args: &[String], name: &str) -> String {
    args.windows(2)
        .find(|pair| pair[0] == name)
        .map(|pair| pair[1].clone())
        .unwrap()
}

fn response(status: &str, fields: &str, exit: i32) -> ! {
    println!("{{\"status\":\"{status}\"{fields}}}");
    process::exit(exit)
}

fn quoted_path(path: &Path) -> String {
    path.to_string_lossy()
        .replace('\\', "\\\\")
        .replace('"', "\\\"")
}

fn settings_path(executable: &Path) -> PathBuf {
    executable.with_extension("settings")
}

fn main() {
    let args: Vec<_> = env::args().skip(1).collect();
    if args.first().is_some_and(|arg| arg == "--descendant") {
        let marker = Path::new(&args[1]);
        fs::write(marker, "alive").unwrap();
        loop {
            thread::sleep(Duration::from_millis(25));
            fs::write(marker, "alive").unwrap();
        }
    }
    let executable = env::current_exe().unwrap();
    if settings_path(&executable).exists() {
        let source = fs::read_to_string(settings_path(&executable)).unwrap();
        if source.contains("program-input") {
            assert_eq!(args, ["a b", "", "quoted\"value", "trailing\\"]);
            assert_eq!(env::var("RIL_HARNESS_EMPTY").unwrap(), "");
            assert!(env::var_os("RIL_HARNESS_ABSENT").is_none());
            let mut stdin = Vec::new();
            io::stdin().read_to_end(&mut stdin).unwrap();
            assert_eq!(stdin, [0, 255, 13, 10]);
            io::stdout().write_all(&[0, 255, 13, 10]).unwrap();
            io::stderr().write_all(b"err\r\n").unwrap();
        }
        if source.contains("program-failure") {
            process::exit(1);
        }
        return;
    }
    let phase = &args[0];
    let source = fs::read(&args[1]).unwrap();
    let source = String::from_utf8_lossy(&source);
    let unit = option(&args, "--unit");
    let _target = option(&args, "--target");
    assert!(args.iter().any(|arg| arg == "--json"));
    if phase == "check" {
        if source.contains("check-unit-executable") {
            assert_eq!(unit, "executable");
        }
        if source.contains("check-unit-library") {
            assert_eq!(unit, "library");
        }
        if source.contains("pointer-layout") {
            assert_eq!(option(&args, "--target"), "pointer32");
        }
        if source.contains("isolated-workspace") {
            assert!(!Path::new("touched").exists());
            fs::write("touched", "1").unwrap();
        }
        if source.contains("invalid-json") {
            print!("not JSON");
            return;
        }
        if source.contains("status-exit-mismatch") {
            response("accepted", "", 1);
        }
        if source.contains("compiler-crash") {
            process::exit(101);
        }
        if source.contains("compiler-timeout") {
            thread::sleep(Duration::from_secs(30));
        }
        if source.contains("descendant-timeout") {
            let marker = source
                .lines()
                .find_map(|line| line.strip_prefix("-- descendant-marker:"))
                .unwrap();
            let mut descendant = Command::new(&executable)
                .arg("--descendant")
                .arg(marker)
                .stdin(Stdio::null())
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .spawn()
                .unwrap();
            thread::sleep(Duration::from_secs(30));
            let _ = descendant.wait();
        }
        if source.contains("check-unimplemented") {
            response("not-implemented", ",\"reason\":\"fixture\"", 2);
        }
        if source.contains("check-unsupported") {
            response("unsupported-environment", "", 2);
        }
        if source.contains("check-reject") {
            response(
                "rejected",
                ",\"diagnostics\":[{\"code\":\"E0520\",\"severity\":\"error\"}]",
                1,
            );
        }
        response("accepted", "", 0);
    }
    if phase == "build" {
        if source.contains("build-unimplemented") {
            response("not-implemented", "", 2);
        }
        assert_eq!(unit, "executable");
        let output = PathBuf::from(option(&args, "--output"));
        fs::copy(&executable, &output).unwrap();
        fs::write(settings_path(&output), source.as_bytes()).unwrap();
        response(
            "built",
            &format!(",\"artifact\":{{\"path\":\"{}\"}}", quoted_path(&output)),
            0,
        );
    }
    if phase == "test" {
        assert_eq!(unit, "library");
        assert_eq!(option(&args, "--entry"), "test_fixture");
        if source.contains("helper-required") {
            assert!(Path::new("helper.exe").is_file());
        }
        if source.contains("test-unimplemented") {
            response("not-implemented", "", 2);
        }
        if source.contains("test-input") {
            let trailing = args.iter().position(|arg| arg == "--").unwrap();
            assert_eq!(&args[trailing + 1..], ["a b", ""]);
            assert_eq!(env::var("RIL_HARNESS_EMPTY").unwrap(), "");
            assert!(env::var_os("RIL_HARNESS_ABSENT").is_none());
            let mut stdin = Vec::new();
            io::stdin().read_to_end(&mut stdin).unwrap();
            assert_eq!(stdin, [0, 255, 13, 10]);
        }
        if source.contains("panic-setup") {
            response(
                "executed",
                ",\"runtime\":\"language-panic\",\"origin\":\"fixture-setup\"",
                0,
            );
        }
        if source.contains("panic-operation") {
            response(
                "executed",
                ",\"runtime\":\"language-panic\",\"origin\":\"designated-operation\"",
                0,
            );
        }
        if source.contains("returned-err") {
            response("executed", ",\"runtime\":\"returned-err\"", 0);
        }
        if source.contains("missing-runtime") {
            response("executed", "", 0);
        }
        response(
            "executed",
            ",\"runtime\":\"returned-unit\",\"stdout\":[],\"stderr\":[]",
            0,
        );
    }
    panic!("unknown fixture phase");
}
