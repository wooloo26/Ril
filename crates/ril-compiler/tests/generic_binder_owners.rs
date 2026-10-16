use ril_compiler::{CheckOptions, CompilationOutcome, Session, session::ProjectSource};
use std::collections::BTreeSet;

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
                bytes: b"pub eff Read<T>{get()->T}".to_vec(),
            },
        ],
        CheckOptions::default(),
    )
    .unwrap()
}

#[test]
fn effectful_default_helper_instances_do_not_share_the_same_span_binder() {
    let declaration = "use helper\npub fn number<n:int>(value:int={with Helper::Read<int>::get()->resume n;read(n) where fn read<T>(witness:T)->T @Helper::Read<T>{Helper::Read<T>::get()}})->int";
    let program = project(
        declaration,
        "fn example(){assert(Foreign::number<7>()==7);assert(Foreign::number<9>()==9)}",
    )
    .verify()
    .unwrap();
    let facts = program.facts();
    let binders: Vec<_> = facts
        .generic_binders
        .values()
        .filter(|binder| binder.name == "T")
        .collect();
    let owners: BTreeSet<_> = binders.iter().map(|binder| binder.definition).collect();
    assert!(owners.len() >= 3);
    let spans: BTreeSet<_> = binders
        .iter()
        .map(|binder| (binder.owner.file.0, binder.owner.start, binder.owner.end))
        .collect();
    assert_eq!(spans.len(), 1);
    let symbolic: Vec<_> = facts
        .effect_instances
        .iter()
        .filter(|instance| !instance.key.is_closed())
        .collect();
    assert_eq!(symbolic.len(), owners.len());
    for (index, instance) in symbolic.iter().enumerate() {
        for other in &symbolic[index + 1..] {
            assert_ne!(instance.key, other.key);
        }
    }
}

#[test]
fn same_span_foreign_default_helpers_keep_distinct_declaration_binders_in_core() {
    let program=project("pub fn number<n:int>(value:int={identity(n) where fn identity<T>(value:T)->T{value}})->int", "fn example(){assert(Foreign::number<7>()==7);assert(Foreign::number<9>()==9)}").verify().unwrap();
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    let mut owners = BTreeSet::new();
    let mut types = BTreeSet::new();
    let mut spans = BTreeSet::new();
    for external in &core.external_functions {
        let default = external.parameters[0].default.as_ref().unwrap();
        let ril_ir::core::ExprKind::Block(block) = &default.kind else {
            panic!("{default:?}")
        };
        let helper = block
            .statements
            .iter()
            .find_map(|statement| match statement {
                ril_ir::core::Statement::Function(function) => Some(function),
                _ => None,
            })
            .unwrap();
        let binder = core
            .provenance
            .generic_binders
            .iter()
            .find(|binder| binder.definition == helper.definition && binder.index == 0)
            .unwrap();
        assert_eq!(helper.generic_parameters, [binder.ty]);
        assert!(owners.insert(binder.definition));
        assert!(types.insert(binder.ty.0));
        spans.insert((binder.owner.file.0, binder.owner.start, binder.owner.end));
    }
    assert_eq!(owners.len(), 2);
    assert_eq!(spans.len(), 1);
    ril_codegen::lower::lower_native_with_entry(&core, "example").unwrap();
}

#[test]
fn diagnostic_spans_cannot_merge_owned_ast_declarations() {
    let mut syntax=ril_syntax::parse("fn first<T>(value:T)->T{value}\nfn second<T>(value:T)->T{value}\nfn example(){let one=first(1);let text=second(\"two\")}").program;
    let span = syntax.statements[0].span;
    let ril_syntax::ast::StmtKind::Function(second) = &mut syntax.statements[1].kind else {
        panic!()
    };
    second.span = span;
    let program = Session::new(vec![]).verify_program(&syntax).unwrap();
    let binders: Vec<_> = program.facts().generic_binders.values().collect();
    assert_eq!(binders.len(), 2);
    assert_eq!(binders[0].owner, binders[1].owner);
    assert_ne!(binders[0].definition, binders[1].definition);
    assert_ne!(binders[0].identity, binders[1].identity);
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    assert_ne!(
        core.functions[0].generic_parameters,
        core.functions[1].generic_parameters
    );
}

#[test]
fn outer_binders_and_same_named_local_shadows_keep_their_declared_owners() {
    let source = "fn outer<T>(value:T)->T{{same(value) where fn same(item:T)->T{item};fn shadow<T>(item:T)->T{item}}}\nfn example(){assert(outer(1)==1)}";
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let owners: BTreeSet<_> = program
        .facts()
        .generic_binders
        .values()
        .map(|binder| binder.definition)
        .collect();
    assert_eq!(owners.len(), 2);
    for binder in program.facts().generic_binders.values() {
        assert!(
            program
                .facts()
                .functions
                .iter()
                .any(|function| function.definition == binder.definition
                    && function.syntax.generics[binder.index as usize].name == binder.name)
        );
    }
    let bad = "fn outer<T>(value:T)->T{{wrong(value) where fn wrong<U>(item:U)->T{item}}}";
    let outcome = Session::new(bad.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome,CompilationOutcome::Rejected{ref diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
        "{outcome:?}"
    );
}
