use ril_compiler::{CheckOptions, Session, session::ProjectSource};

#[test]
fn declaration_defaults_certify_handlers_installed_before_the_local_budget() {
    let source = Session::with_project(
        "virtual/main.ril".into(),
        vec![
            ProjectSource { path:"virtual/main.ril".into(),bytes:b"use foreign\nfn entry(){assert(Foreign::compute()==7);assert(Foreign::short()==0)}".to_vec() },
            ProjectSource { path:"virtual/helper.ril".into(),bytes:b"pub eff Read{get()->int}\npub fn value()->int @Read{Read::get()}".to_vec() },
            ProjectSource { path:"virtual/foreign.d.ril".into(),bytes:b"use helper\npub fn compute(value:int={with Helper::Read::get()->resume 7;with Div::exhausted()->0;Div::budget(3,Helper::value)})->int\npub fn short(value:int={with Helper::Read::get()->resume 7;with Div::exhausted()->0;Div::budget(2,Helper::value)})->int".to_vec() },
        ],CheckOptions::default()
    ).unwrap();
    let verified = source.verify().unwrap();
    assert!(!verified.facts().budget_proofs.is_empty());
    assert!(
        verified
            .facts()
            .budget_proofs
            .iter()
            .all(|proof| proof.callee_coverage.len() >= 3)
    );
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert!(ril_codegen::cps::contains_budget(&core));
    let module = ril_codegen::lower::lower_native_with_entry(&core, "entry").unwrap();
    assert!(!module.budget_entries.is_empty());
}
