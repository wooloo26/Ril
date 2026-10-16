//! Host-only source functions must retain the continuation all the way through
//! named helpers, callable interfaces, defaults, and structured callbacks.
use std::{fs, process::Command};

fn execute(source: &str) {
    let directory = tempfile::tempdir().unwrap();
    let source_path = directory.path().join("host.ril");
    fs::write(&source_path, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(source_path)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["runtime"], "returned-unit", "{report}");
    assert_eq!(report["exit"], 0, "{report}");
}

#[test]
fn host_leaf_helpers_aliases_defaults_and_higher_order_callbacks_execute() {
    execute(
        r#"
use ril/io
use ril/time
use ril/random
fn leaf(value:int)->int @Fiber{
    Time::sleep(Time::duration_nanos(1000000i64))
    match Io::stdin_read(0){
        Ok(chunk)->assert(chunk.data==b"" && !chunk.end),
        Err(_)->panic("zero-length standard input failed"),
    }
    assert(Random::entropy(0) is Ok(b""))
    let progress=Io::stdout_write(b"")
    assert(progress.error == None && progress.written == 0)
    value+1
}
fn middle(value:int)->int @Fiber{leaf(value)}
fn map_leaf(value:int)->int @Fiber{Time::sleep(Time::duration_nanos(1000000i64));value+1}
fn invoke(value:int,action:fn(int)->int @Fiber)->int @Fiber{action(value)}
fn default_action(action:fn(int)->int @Fiber=middle)->int @Fiber{action(6)}
pub fn test_native() @Fiber{
    let action=middle
    assert(invoke(1,action)==2)
    assert(default_action()==7)
    assert(Array::map([2,3],map_leaf)==[3,4])
    assert((\number->middle(number))(8)==9)
    let direct=Time::sleep
    direct(Time::duration_nanos(0i64))
}
"#,
    );
}

#[test]
fn a_host_child_and_nested_parallel_keep_their_calling_conventions() {
    execute(
        r#"
use ril/time
use ril/concurrent::{scope}
use ril/parallel
fn host_leaf()->int @Fiber{Time::sleep(Time::duration_nanos(1000000i64));7}
fn pure_leaf()->int{11}
fn invoke(action:fn()->int)->int{action()}
pub fn test_native() @Async{
    let outcome=scope \mut s->{let task=s.fork(host_leaf);let value=task.join();Ok(value)}
    assert(outcome is Ok(Ok(7)))
    assert(invoke(pure_leaf)==11)
    let pairs=Parallel::map([1,2],\value->Parallel::join(\->value+1,\->value*2))
    assert(pairs==[(2,2),(3,4)])
}
"#,
    );
}

#[test]
fn ordinary_filesystem_helpers_use_the_host_continuation_path() {
    let directory = tempfile::tempdir().unwrap();
    let file = serde_json::to_string(&directory.path().join("payload").to_string_lossy()).unwrap();
    execute(&format!(
        r#"
use ril/file
use ril/path
fn write_file(name:str) @Fiber{{assert(File::write_bytes(Path::from_string(name),b"host") is Ok(_))}}
fn read_file(name:str)->bytes @Fiber{{match File::read_bytes(Path::from_string(name)){{Ok(data)->data,Err(_)->panic("read failed")}}}}
pub fn test_native() @Fiber{{write_file({file});assert(read_file({file})==b"host")}}
"#
    ));
}
