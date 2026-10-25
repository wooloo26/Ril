use ril_compiler::{CheckOptions, CompilationOutcome, ProjectSource, Session};

fn session(case: &str, target: &str) -> Session {
    let case = ril_test::case_by_id(&format!(
        "tests/regressions/stdlib-declarations.ril::{case}"
    ));
    Session::with_project(
        case.root.clone().into(),
        case.files
            .iter()
            .map(|file| ProjectSource {
                path: file.name.clone().into(),
                bytes: file.bytes.clone(),
            })
            .collect(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .unwrap()
}

#[test]
fn bundled_fallbacks_are_checked_declarations_and_ordinary_core_functions() {
    for target in ["pointer32", "pointer64"] {
        let snapshot = session("ordinary-fallbacks-pointer64", target).analyze();
        let details = format!("{:?}; {:?}", snapshot.diagnostics(), snapshot.unresolved());
        let program = snapshot
            .into_verified()
            .unwrap_or_else(|outcome| panic!("{target}: {outcome:?}; {details}"));
        let library: Vec<_> = program
            .facts()
            .functions
            .iter()
            .filter(|function| function.syntax.span.file.0 != 0)
            .collect();
        assert_eq!(library.len(), 7);
        for function in &library {
            assert!(function.hir_id.is_some() && function.syntax.body.is_some());
            assert!(
                function
                    .syntax
                    .parameters
                    .iter()
                    .all(|parameter| parameter.ty.as_ref().is_some_and(|ty| ty.hir_id.is_some()))
            );
        }
        let core = ril_compiler::lower::lower_core(&program).unwrap();
        for function in library {
            assert!(
                core.functions
                    .iter()
                    .any(|lowered| lowered.definition == function.definition
                        && lowered.role == ril_ir::core::FunctionRole::Ordinary)
            );
        }
    }
}

#[test]
fn ordinary_library_calls_preserve_imports_generics_and_composite_sources() {
    let mut failures = Vec::new();
    for case in [
        "aliases-and-reexports",
        "first-class-and-named",
        "composite-payloads",
        "user-module-lookalike",
        "generic-control-results-pointer64",
        "eager-fallback-order",
        "eager-fallback-panic",
        "bottom-cleanup",
        "typed-bottom-cleanup",
        "result-inference-pointer64",
        "typed-testing-helpers",
        "explicit-user-error-type",
    ] {
        for target in ["pointer32", "pointer64"] {
            match session(case, target).verify() {
                Ok(program) => {
                    ril_compiler::lower::lower_core(&program).unwrap();
                }
                Err(outcome) => failures.push(format!("{case}, {target}: {outcome:?}")),
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn ordinary_library_returns_cannot_retype_stored_payloads() {
    for target in ["pointer32", "pointer64"] {
        for (case, code) in [
            ("reject-stored-payload-dimension", "E0301"),
            ("reject-restored-write-authority", "E0520"),
            ("reject-uninspected-nested-result", "E0720"),
            ("reject-nonunit-cleanup", "E0541"),
            ("reject-uninspected-nested-result-via-ok", "E0720"),
            ("reject-result-payload-dimension", "E0301"),
            ("reject-result-write-authority", "E0520"),
        ] {
            let outcome = session(case, target).check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
                "{case}, {target}: {outcome:?}"
            );
        }
    }
}

#[test]
fn inactive_constructor_arguments_require_real_inference_constraints() {
    for target in ["pointer32", "pointer64"] {
        for case in [
            "reject-unselected-error-type",
            "reject-unselected-test-error-type",
            "reject-unselected-success-type",
            "reject-unselected-user-success-type",
            "reject-discarded-user-success-type",
        ] {
            let outcome = session(case, target).check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0344")),
                "{case}, {target}: {outcome:?}"
            );
        }
    }
}

#[test]
fn ordinary_library_definitions_keep_their_evaluation_family() {
    for target in ["pointer32", "pointer64"] {
        let outcome = session("reject-meta-call", target).check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0810")),
            "{target}: {outcome:?}"
        );
    }
}
#[test]
fn private_standard_modules_require_an_actual_bundled_source_origin() {
    for target in ["pointer32", "pointer64"] {
        for case in [
            "reject-private-standard-storage",
            "reject-private-qualified-storage",
        ] {
            let outcome = session(case, target).check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0201")),
                "{case} {target}: {outcome:?}"
            );
        }
        let program = session("private-namespace-user-module", target)
            .verify()
            .unwrap();
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}
