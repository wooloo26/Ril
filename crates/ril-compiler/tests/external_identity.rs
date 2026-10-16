use ril_compiler::{CheckOptions, Session, session::ProjectSource};

fn project(extra_module: bool) -> Session {
    let mut files = vec![
        ProjectSource {
            path: "virtual/main.ril".into(),
            bytes: b"use bridge\nfn entry() {}".to_vec(),
        },
        ProjectSource {
            path: "virtual/bridge.ril".into(),
            bytes: b"pub use external/api::{value, VERSION}".to_vec(),
        },
        ProjectSource {
            path: "virtual/external/api.d.ril".into(),
            bytes: b"pub fn value() -> int\npub let VERSION: i64".to_vec(),
        },
    ];
    if extra_module {
        files.push(ProjectSource {
            path: "virtual/a.ril".into(),
            bytes: b"fn unrelated() {}".to_vec(),
        });
    }
    Session::with_project("virtual/main.ril".into(), files, CheckOptions::default()).unwrap()
}

#[test]
fn binding_identity_survives_reexports_and_file_identity_changes() {
    let before = project(false).verify().unwrap();
    let after = project(true).verify().unwrap();
    let names = |program: &ril_compiler::hir::VerifiedProgram| {
        program
            .external_declarations()
            .iter()
            .map(|external| external.declaration.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(
        names(&before),
        ["external/api::value", "external/api::VERSION"]
    );
    assert_eq!(names(&before), names(&after));
    assert_ne!(
        before.external_declarations()[0].internal_name,
        after.external_declarations()[0].internal_name
    );
    assert_ne!(
        before.external_declarations()[0].span.file,
        after.external_declarations()[0].span.file
    );
}
