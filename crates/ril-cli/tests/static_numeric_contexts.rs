use std::{fs, process::Command};

fn run(source: &str, execute: bool) -> serde_json::Value {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("static_numbers.ril");
    fs::write(&path, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_ril"));
    command
        .arg(if execute { "test" } else { "check" })
        .arg(path)
        .args(["--json", "--static-budget", "100"]);
    if execute {
        command.args(["--entry", "test_native"]);
    }
    let output = command.output().unwrap();
    serde_json::from_slice(&output.stdout).unwrap_or_else(|_| {
        panic!(
            "{:?}\n{}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}
fn executes(source: &str) {
    let report = run(source, true);
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], "returned-unit", "{report}");
}

#[test]
fn exact_integer_selection_reaches_native_scalars_and_graph_leaves() {
    executes(
        r#"
meta let FIRST:f32=18014399583223809
meta let SECOND:f32=170141193601674033557522515689509748737
meta let VALUES:(f32,u64,bigint,f64)=(-0X40000040000001,18446744073709551615,340282366920938463463374607431768211456,340282366920938463463374607431768211456)
pub fn test_native() &{FIRST,SECOND,VALUES}{
    assert(FIRST==18014400656965632.0f32)
    assert(SECOND==170141203742878835383357727663135391744.0f32)
    assert(VALUES.0 == -18014400656965632.0f32)
    assert(VALUES.1==18446744073709551615u64)
    assert(VALUES.2==340282366920938463463374607431768211456bigint)
    assert(VALUES.3==340282366920938463463374607431768211456.0f64)
}
"#,
    );
}

#[test]
fn committed_zero_infinity_and_nan_preserve_their_native_float_semantics() {
    executes(
        r#"
meta let ZERO:f32=-0
meta let TINY:f32=-1.0e-9999
meta let HUGE:f32=1.0e9999
meta let NAN:f64=0.0/0.0
pub fn test_native() &{ZERO,TINY,HUGE,NAN}{
    assert(1.0f32/ZERO<0.0f32 && 1.0f32/TINY<0.0f32)
    assert(HUGE>340282346638528859811704183484516925440.0f32)
    assert(NAN!=NAN)
}
"#,
    );
}

#[test]
fn actual_application_slots_and_return_contexts_select_before_static_execution() {
    executes(
        r#"
meta fn pair(first:u64,second:f32=16777217)->(u64,f32){(first,second)}
meta fn answer()->f32{return 16777217+1}
meta fn identity(value:f32)->f32{value}
meta let NAMED:fn(other:f32)->f32=identity
meta let DEFAULT=pair(18446744073709551615)
meta let REORDERED=pair(second:16777219,first:18446744073709551615)
meta let ANSWER=answer()
meta let VIEW=NAMED(other:16777217)
pub fn test_native() &{DEFAULT,REORDERED,ANSWER,VIEW}{
    assert(DEFAULT==(18446744073709551615u64,16777216.0f32))
    assert(REORDERED==(18446744073709551615u64,16777220.0f32))
    assert(ANSWER==16777216.0f32 && VIEW==16777216.0f32)
}
"#,
    );
}

#[test]
fn selected_aggregate_leaves_keep_reference_identity_through_reification() {
    executes(
        r#"
meta let ROOT={let child:[2]f32=[16777217,-16777217];(child,child)}
pub fn test_native() &{ROOT}{
    let mut copied= ^mut clone(ROOT)
    assert(copied.0[0]==16777216.0f32 && copied.1[1] == -16777216.0f32)
    copied.0[0]=9.0f32
    assert(copied.1[0]==9.0f32 && ROOT.0[0]==16777216.0f32)
}
"#,
    );
}

#[test]
fn committed_values_and_suffixes_do_not_reopen_literal_selection() {
    for source in [
        "meta let VALUE:f32=1int",
        "meta let STORED=1\nmeta let VALUE:f32=STORED",
        "meta let STORED=[1]\nmeta let VALUE:[]f32=STORED",
    ] {
        let report = run(source, false);
        assert_eq!(report["status"], "rejected", "{report}");
        assert!(
            report["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|diagnostic| diagnostic["code"] == "E0301"),
            "{report}"
        );
    }
}
