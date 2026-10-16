use std::{fs, process::Command};

fn executes(source: &str) {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("generic_effects.ril");
    fs::write(&path, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(path)
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
    assert_eq!(report["runtime"], "returned-unit", "{report}");
}

#[test]
fn closed_type_instances_and_transitive_calls_select_their_own_effect_operations() {
    executes(
        r#"
eff Read<T>{get()->T}
fn read<U>(witness:U)->U @Read<U>{Read<U>::get()}
fn forward<T>(value:T)->T @Read<T>{read(value)}
pub fn test_native(){
    with {Read<int>::get()->resume 7,Read<str>::get()->resume "seven"}
    assert(forward(0)==7 && forward("")=="seven")
    assert(forward(1)==7 && forward("again")=="seven")
}
"#,
    );
}

#[test]
fn closed_effect_instances_keep_distinct_normal_and_metered_entries() {
    executes(
        r#"
eff Read<T>{get()->T}
fn read<T>(witness:T)->T @Read<T>{Read<T>::get()}
fn integer(limit:int)->?int {
    with {Read<int>::get()->resume 7,Div::exhausted()->None}
    Div::budget(limit,\->Some(read(0)))
}

fn text(limit:int)->?str {
    with {Read<str>::get()->resume "seven",Div::exhausted()->None}
    Div::budget(limit,\->Some(read("")))
}
pub fn test_native(){
    assert(integer(0)==None && text(0)==None)
    assert(integer(100)==Some(7) && text(100)==Some("seven"))
    with {Read<int>::get()->resume 9,Read<str>::get()->resume "nine"}
    assert(read(0)==9 && read("")=="nine")
}
"#,
    );
}

#[test]
fn generic_local_handlers_keep_their_type_and_dynamic_payload() {
    executes(
        r#"
eff Read<T>{get()->T}
fn local<T>(value:T)->T{with Read<T>::get()->resume value;Read<T>::get()}
pub fn test_native(){assert(local(7)==7 && local("seven")=="seven" && local(9)==9)}
"#,
    );
}

#[test]
fn specialization_preserves_both_previewed_conditional_paths() {
    executes(
        r#"
eff Read<T>{get()->T}
fn read_if<T>(value:T,enabled:bool)->T @Read<T>{if enabled{Read<T>::get()}else{value}}
pub fn test_native(){
    with {Read<int>::get()->resume 7,Read<str>::get()->resume "seven"}
    assert(read_if(0,false)==0 && read_if(0,true)==7)
    assert(read_if("original",false)=="original" && read_if("original",true)=="seven")
}
"#,
    );
}

#[test]
fn generic_closures_at_one_site_keep_distinct_static_instances() {
    executes(include_str!(
        "fixtures/generic_closures/immediate_instances.ril"
    ));
}

#[test]
fn escaping_generic_closures_keep_each_creation_capture_and_recipe() {
    executes(include_str!(
        "fixtures/generic_closures/retained_instances.ril"
    ));
}

#[test]
fn escaped_generic_nested_handlers_keep_their_metered_entries() {
    executes(include_str!(
        "fixtures/generic_closures/nested_and_budget.ril"
    ));
}

#[test]
fn an_unclosed_generic_closure_keeps_its_specialization_boundary() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("unclosed.ril");
    fs::write(
        &path,
        include_str!("fixtures/generic_closures/unclosed.ril"),
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(path)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["status"], "not-implemented", "{report}");
    assert!(
        report["reason"]["detail"]
            .as_str()
            .unwrap()
            .contains("specialization"),
        "{report}"
    );
}
