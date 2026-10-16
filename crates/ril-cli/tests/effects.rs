use std::{fs, process::Command};

fn execute(source_text: &str) {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("effects.ril");
    fs::write(&source, source_text).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&source)
        .args(["--entry", "test_effects", "--json"])
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(result["runtime"], "returned-unit", "{result}");
}

#[test]
fn distinct_generic_effect_instances_execute() {
    execute(
        r#"eff State<T>{get()->T}
pub fn test_effects(){with {State<int>::get()->resume 7,State<str>::get()->resume "seven"};assert(State<int>::get()==7&&State<str>::get()=="seven")}"#,
    );
}

#[test]
fn generic_effect_sets_keep_the_underlying_operation_identity() {
    execute(
        r#"eff State<T>{get()->T}
eff App<T>{State<T>}
eff ReadInt{App<int>}
pub fn test_effects(){with {ReadInt::get()->resume 7,App<str>::get()->resume "seven"};assert(State<int>::get()==7&&State<str>::get()=="seven")}"#,
    );
}

#[test]
fn retained_handlers_use_fresh_boundaries_and_original_lexical_cells() {
    execute(
        r#"eff Read{get()->int}
type Reader=fn()->int &closure
fn ask()->int @Read{Read::get()}
fn make_reader()->Reader &capture{let value=7;with Read::get()->resume value;{let value=99;\->ask()}}
pub fn test_effects(){let reader=make_reader();with Read::get()->resume 99;assert(reader()==7&&reader()==7)}"#,
    );
}

#[test]
fn retained_handlers_preserve_outer_forwarding() {
    execute(
        r#"eff Read{get()->int}
type Reader=fn()->int &closure
fn make_reader()->Reader &capture{with Read::get()->resume 7;{with Read::get()->{let outer=Read::get();resume (outer+1)};\->Read::get()}}
pub fn test_effects(){let reader=make_reader();with Read::get()->resume 99;assert(reader()==8&&reader()==8)}"#,
    );
}

#[test]
fn parameterized_handler_applications_keep_the_preselected_handler() {
    execute(
        r#"eff Read{get()->int}
fn supply(value:int,action:fn()->int)->int{with Read::get()->resume value;action()}
halt fn configured()->int{with supply(7);Read::get()+1}
halt fn existing()->int{with Read::get()->resume 3;with supply(7);Read::get()}
pub fn test_effects(){assert(configured()==8&&existing()==3)}"#,
    );
}

#[test]
fn named_callables_retain_only_the_handlers_at_their_creation_scope() {
    execute(
        r#"eff Read{get()->int}
type Reader=fn()->int &closure
type Deferred=fn()->int @Read
fn nested()->Reader &capture{with Read::get()->resume 7;{helper where fn helper()->int{Read::get()}}}
fn same()->Deferred{with Read::get()->resume 7;helper where fn helper()->int @Read{Read::get()}}
fn ask()->int @Read{Read::get()}
pub fn test_effects(){let kept=nested();let forwarded=same();let existing={with Read::get()->resume 7;ask};with Read::get()->resume 99;assert(kept()==7&&forwarded()==99&&existing()==99)}"#,
    );
}

#[test]
fn handlers_retained_outside_a_budget_keep_metered_arm_entries() {
    execute(
        r#"eff Read{get()->int}
type Reader=fn()->int &closure
fn make_reader()->Reader &capture{with Read::get()->resume 7;\->Read::get()}
fn measured(limit:int)->int{let reader=make_reader();with Div::exhausted()->-1;Div::budget(limit,reader)}
pub fn test_effects(){let reader=make_reader();with Div::exhausted()->();assert(Div::budget(100,reader)==7);assert(reader()==7);assert(measured(0)==-1&&measured(1)==-1&&measured(2)==-1&&measured(3)==7)}"#,
    );
}
