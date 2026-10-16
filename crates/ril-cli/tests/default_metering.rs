use std::{fs, process::Command};

fn run(source: &str) -> serde_json::Value {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("defaults.ril");
    fs::write(&input, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(input)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap_or_else(|_| {
        panic!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    assert_eq!(report["status"], "executed", "{report}");
    report
}

#[test]
fn default_panics_happen_before_the_callee_body_entry_charge() {
    for source in [
        include_str!("fixtures/generic_defaults/entry_budget_order.ril"),
        include_str!("fixtures/generic_defaults/helper_entry_budget_order.ril"),
        include_str!("fixtures/generic_defaults/lambda_entry_budget_order.ril"),
    ] {
        let report = run(source);
        assert_eq!(report["runtime"], "language-panic", "{report}");
        assert!(
            report["message"].as_str().unwrap().contains("before"),
            "{report}"
        );
    }
}

#[test]
fn defaults_charge_their_helpers_and_supplied_arguments_bypass_them() {
    let report = run(r#"
halt fn helper()->int{7}
fn callee(value:int=helper())->int{value}
fn omitted(limit:int)->?int{with Div::exhausted()->None;Some(Div::budget(limit,\->callee()))}
fn supplied(limit:int)->?int{with Div::exhausted()->None;Some(Div::budget(limit,\->callee(9)))}
pub fn test_native(){
    assert(omitted(2)==None && omitted(3)==Some(7))
    assert(supplied(1)==None && supplied(2)==Some(9))
    assert(callee()==7 && callee(9)==9)
}
"#);
    assert_eq!(report["runtime"], "returned-unit", "{report}");
}
