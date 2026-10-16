use ril_compiler::{CheckOptions, Session};
use ril_compiler_core::{phase::Stage, target::TargetLayout};

fn program(target: &str) -> ril_compiler::hir::VerifiedProgram {
    Session::with_options(
        b"pub fn test_native(){let value:int=1;assert(value==1)}".to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap()
}

#[test]
fn core_uses_the_verified_layout_and_cannot_change_it_after_checking() {
    for (target, layout, other) in [
        (
            "pointer32",
            TargetLayout::POINTER32,
            TargetLayout::POINTER64,
        ),
        (
            "pointer64",
            TargetLayout::POINTER64,
            TargetLayout::POINTER32,
        ),
    ] {
        let verified = program(target);
        assert_eq!(verified.facts().target_layout, Some(layout));
        let core = ril_compiler::lower::lower_core(&verified).unwrap();
        assert_eq!(core.provenance.target_layout, Some(layout));
        let error = ril_compiler::lower::lower_core_for(&verified, other)
            .expect_err("a different layout cannot reuse this semantic certificate");
        assert_eq!(error.stage, Stage::Lowering);
        assert!(error.detail.contains("layout"));
    }
}

#[test]
fn pointer32_static_checking_does_not_authorize_x64_native_execution() {
    let verified = program("pointer32");
    let core = ril_compiler::lower::lower_core_for(&verified, TargetLayout::POINTER32).unwrap();
    let error = ril_codegen::lower::lower_native_with_entry(&core, "test_native")
        .expect_err("a pointer32 static certificate cannot enter the x64 runtime");
    assert_eq!(error.stage, Stage::Lowering);
    assert!(error.detail.contains("64"));
    let core = ril_compiler::lower::lower_core(&program("pointer64")).unwrap();
    ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
}
