use ril_compiler::{CheckOptions, Session, session::ProjectSource};
use ril_compiler_core::ids::CallableOwner;

fn project(declaration: &str, body: &str) -> Session {
    Session::with_project(
        "virtual/main.ril".into(),
        vec![
            ProjectSource {
                path: "virtual/main.ril".into(),
                bytes: format!("use foreign\n{body}").into_bytes(),
            },
            ProjectSource {
                path: "virtual/foreign.d.ril".into(),
                bytes: declaration.as_bytes().to_vec(),
            },
            ProjectSource {
                path: "virtual/helper.ril".into(),
                bytes: b"pub eff Read { get() -> int }".to_vec(),
            },
        ],
        CheckOptions::default(),
    )
    .unwrap()
}

#[test]
fn retained_default_recipes_are_owned_by_concrete_callable_instances() {
    let declaration = r#"
use helper
pub type Reader = fn() -> int &closure
pub fn retained<n:int>(callback:Reader={with Helper::Read::get()->resume n;\->Helper::Read::get()})->int
"#;
    let verified = project(
        declaration,
        "pub fn main(){assert(Foreign::retained<7>()==7);assert(Foreign::retained<9>()==9)}",
    )
    .verify()
    .unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    let mut selected = Vec::new();
    for function in &core.external_functions {
        let owner = CallableOwner::Function(function.definition);
        let sites: Vec<_> = core
            .provenance
            .closure_sites
            .iter()
            .filter(|site| site.owner == owner)
            .collect();
        assert_eq!(sites.len(), 1);
        let proof = core
            .provenance
            .retained_handlers
            .iter()
            .find(|proof| proof.callable == Some(CallableOwner::Lambda(sites[0].id)))
            .unwrap();
        let definitions = proof.definitions.as_ref().unwrap();
        assert_eq!(definitions.len(), 1);
        assert!(
            core.provenance
                .handlers
                .iter()
                .any(|handler| handler.callable_owner == Some(owner)
                    && handler.definition == Some(definitions[0]))
        );
        selected.push((sites[0].id, definitions[0]));
    }
    assert_eq!(selected.len(), 2);
    assert_ne!(selected[0].0, selected[1].0);
    assert_ne!(selected[0].1, selected[1].1);
    ril_codegen::lower::lower_native(&core).unwrap();
}

#[test]
fn retained_default_identity_preserves_capability_and_resource_checks() {
    let prefix = "use helper\npub type Reader=fn()->int &closure\n";
    for (declaration, body, expected) in [
        (
            "pub fn retained<n:int>(callback:Reader={with Helper::Read::get()->resume n;\\->Helper::Read::get()})->int",
            "fn entry()->int &{}{Foreign::retained<7>()}",
            "E0534",
        ),
        (
            "pub type Guard={value:int,on_close:fn()->()}\npub fn retained<n:int>(callback:Reader={let scoped guard=Guard.{value:n,on_close:\\->()};with Helper::Read::get()->resume guard.value;\\->Helper::Read::get()})->int",
            "fn entry()->int{Foreign::retained<7>()}",
            "E0614",
        ),
    ] {
        let outcome = project(&format!("{prefix}{declaration}"), body).check();
        assert!(
            matches!(&outcome, ril_compiler::CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == expected)),
            "{outcome:?}"
        );
    }
}

#[test]
fn repeated_named_declarations_keep_one_lexical_definition_per_factory() {
    let verified = project("pub type Reader=fn()->int &closure", r#"
use helper
fn factory()->Foreign::Reader &capture{with Helper::Read::get()->resume 7;{reader where fn reader()->int{Helper::Read::get()}}}
fn other()->Foreign::Reader &capture{with Helper::Read::get()->resume 9;{reader where fn reader()->int{Helper::Read::get()}}}
pub fn main(){let seven=factory();let again=factory();let nine=other();assert(seven()==7 && again()==7 && nine()==9)}
"#).verify().unwrap();
    let facts = verified.facts();
    let mut declarations = std::collections::BTreeMap::new();
    for function in &facts.functions {
        if function.owner.is_some() {
            declarations
                .entry((function.syntax.name.clone(), function.syntax.span.start))
                .or_insert_with(Vec::new)
                .push(function.definition);
        }
    }
    assert_eq!(declarations.len(), 2);
    let mut identities = Vec::new();
    for instances in declarations.values() {
        assert!(instances.len() > 1);
        assert!(
            instances
                .iter()
                .all(|definition| *definition == instances[0])
        );
        identities.push(instances[0]);
    }
    assert_ne!(identities[0], identities[1]);
    let defined: std::collections::BTreeSet<_> = verified
        .definitions()
        .iter()
        .map(|definition| definition.id)
        .collect();
    assert_eq!(defined.len(), verified.definitions().len());
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    for identity in identities {
        assert!(
            core.provenance
                .retained_handlers
                .iter()
                .any(|proof| proof.callable == Some(CallableOwner::Function(identity)))
        );
    }
    ril_codegen::lower::lower_native(&core).unwrap();
}
