use ril_compiler::{CheckOptions, CompilationOutcome, Session, session::ProjectSource};
use ril_ir::{core, native};

fn lower(session: Session) -> (core::Program, native::Module) {
    let verified = session.verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    let native = ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    (core, native)
}

fn convention(core: &core::Program, native: &native::Module, name: &str, cps: bool) {
    let id = core
        .functions
        .iter()
        .find(|function| function.name == name)
        .unwrap()
        .definition;
    let function = native
        .functions
        .iter()
        .find(|function| function.symbol == format!("__ril_fn_{}", id.0))
        .unwrap();
    assert_eq!(
        matches!(function.body, native::Body::Cps(_)),
        cps,
        "{name}: {:?}",
        function.body
    );
}

#[test]
fn host_operations_select_cps_through_named_and_dynamic_callers() {
    for (imports, operation) in [
        (
            "use ril/io",
            "let result=Io::stdin_read(0);assert(result is Ok(_) | Err(_));1",
        ),
        (
            "use ril/file\nuse ril/path",
            "let result=File::read_bytes(Path::from_string(\"unused\"));assert(result is Ok(_) | Err(_));1",
        ),
        (
            "use ril/process\nuse ril/path",
            "let result=Process::run(Process::command(Path::from_string(\"unused\"),[]));assert(result is Ok(_) | Err(_));1",
        ),
        (
            "use ril/random",
            "let result=Random::entropy(0);assert(result is Ok(_) | Err(_));1",
        ),
        ("use ril/time", "Time::sleep(Time::duration_nanos(0i64));1"),
    ] {
        let (core, native) = lower(Session::new(
            format!(
                r#"
{imports}
fn host_leaf()->int @Fiber{{{operation}}}
fn middle()->int @Fiber{{host_leaf()}}
fn invoke(action:fn()->int @Fiber)->int @Fiber{{action()}}
pub fn test_native() @Fiber{{assert(invoke(middle)==1)}}
"#
            )
            .into_bytes(),
        ));
        for name in ["host_leaf", "middle", "invoke", "test_native"] {
            convention(&core, &native, name, true);
        }
    }
}

#[test]
fn pure_dynamic_interfaces_use_a_continuation_without_upgrading_pure_targets() {
    let (core, native) = lower(Session::new(
        br#"
fn plain()->int{7}
fn invoke(action:fn()->int)->int{action()}
pub fn test_native(){assert(invoke(plain)==7)}
"#
        .to_vec(),
    ));
    convention(&core, &native, "plain", false);
    convention(&core, &native, "invoke", true);
    convention(&core, &native, "test_native", true);
}

#[test]
fn foreign_callback_and_concurrent_child_keep_their_own_host_continuations() {
    let source = br#"
use foreign
use ril/time
fn host_leaf()->int @Fiber{Time::sleep(Time::duration_nanos(0i64));7}
fn middle()->int @Fiber{host_leaf()}
pub fn test_native() @Fiber{assert(Foreign::invoke(middle)==7)}
"#;
    let session = Session::with_project(
        "virtual/main.ril".into(),
        vec![
            ProjectSource {
                path: "virtual/main.ril".into(),
                bytes: source.to_vec(),
            },
            ProjectSource {
                path: "virtual/foreign.d.ril".into(),
                bytes: b"pub fn invoke(action:fn()->int @Fiber)->int @Fiber".to_vec(),
            },
        ],
        CheckOptions::default(),
    )
    .unwrap();
    let (core, native) = lower(session);
    for name in ["host_leaf", "middle", "test_native"] {
        convention(&core, &native, name, true);
    }

    let (core, native) = lower(Session::new(br#"
use ril/time
use ril/concurrent::{scope}
fn host_leaf() @Fiber{Time::sleep(Time::duration_nanos(0i64))}
pub fn test_native() @Async{let result=scope \mut s->{s.fork(host_leaf);Ok()};assert(result is Ok(_) | Err(_))}
"#.to_vec()));
    for name in ["host_leaf", "test_native"] {
        convention(&core, &native, name, true);
    }
}

#[test]
fn routing_does_not_authorize_a_host_effect_in_parallel() {
    let outcome = Session::new(
        br#"
use ril/time
use ril/parallel
fn host_leaf()->int @Fiber{Time::sleep(Time::duration_nanos(0i64));1}
pub fn test_native() @Fiber{let _=Parallel::join(host_leaf,\->2)}
"#
        .to_vec(),
    )
    .check();
    let CompilationOutcome::Rejected { diagnostics } = outcome else {
        panic!("{outcome:?}")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "E0605")
    );
}
