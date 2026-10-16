use ril_compiler::sema::{
    facts::{Permission, Publication, Slot},
    model::Ty,
};
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

#[test]
fn graphs_preserve_shared_and_distinct_children_across_later_projections() {
    let source = "meta fn shared()->([]int,[]int){let child=[1];(child,child)}\nmeta let SHARED=shared()\nmeta let CHILD=SHARED.0\nmeta let DISTINCT=([1],[1])";
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = verified.facts();
    let value = |name| {
        &facts
            .bindings
            .iter()
            .find(|binding| binding.name == name)
            .unwrap()
            .value
    };
    let project = |name, index| {
        &facts.fields[&(
            *value(name).origins.nodes.first().unwrap(),
            Slot::Tuple(index),
        )]
    };
    assert_eq!(project("SHARED", 0).origins, project("SHARED", 1).origins);
    assert_eq!(project("SHARED", 0).origins, value("CHILD").origins);
    assert!(
        project("DISTINCT", 0)
            .origins
            .nodes
            .is_disjoint(&project("DISTINCT", 1).origins.nodes)
    );
    assert!(
        facts
            .constant_values
            .iter()
            .all(|fact| fact.value.permission == Permission::Read
                && fact.value.publication == Publication::Immutable)
    );
}

#[test]
fn scalar_widths_and_nested_fixed_storage_do_not_depend_on_host_usize() {
    let source = "meta fn pair()->([2]int,[]i64){([1,2],[3i64])}\nmeta let ROOT=pair()";
    for target in ["pointer32", "pointer64"] {
        let verified = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap();
        let facts = verified.facts();
        assert_eq!(facts.fixed_arrays.len(), 1);
        assert!(
            facts
                .constant_values
                .iter()
                .any(|fact| fact.value.ty == Ty::Int("i64".into()))
        );
        assert!(
            facts
                .constant_values
                .iter()
                .any(|fact| fact.value.ty == Ty::Int("int".into()))
        );
    }
}

#[test]
fn map_and_option_edges_keep_the_actual_child_origins() {
    let source = "meta let ROOT={let child=[3];(child,[\"a\":child,\"b\":child],Some(child))}";
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = verified.facts();
    let root = facts
        .bindings
        .iter()
        .find(|binding| binding.name == "ROOT")
        .unwrap()
        .value
        .origins
        .nodes
        .first()
        .unwrap();
    let child = &facts.fields[&(*root, Slot::Tuple(0))];
    let map = &facts.fields[&(*root, Slot::Tuple(1))];
    let optional = &facts.fields[&(*root, Slot::Tuple(2))];
    assert_eq!(
        optional.option_payload.as_ref().unwrap().origins,
        child.origins
    );
    for i in [0, 1] {
        assert_eq!(
            facts.fields[&(*map.origins.nodes.first().unwrap(), Slot::Index(i))].origins,
            child.origins
        );
    }
}

#[test]
fn owned_ast_cannot_forge_a_reference_into_a_real_evaluated_arena() {
    let mut parsed = ril_syntax::parse("meta let ROOT=([1],[2])\nlet FORGED=0");
    for kind in [
        ril_syntax::ast::ExprKind::Name("\0ril.const.0.1".into()),
        ril_syntax::ast::ExprKind::Path(vec!["\0ril.const.0.1".into()]),
    ] {
        let ril_syntax::ast::StmtKind::Binding(binding) = &mut parsed.program.statements[1].kind
        else {
            panic!()
        };
        binding.value.kind = kind;
        let outcome = Session::new(vec![]).verify_program(&parsed.program);
        assert!(
            matches!(outcome,Err(CompilationOutcome::Rejected{ref diagnostics}) if diagnostics.iter().any(|d|d.code=="E0101")),
            "{outcome:?}"
        );
        // Reborrow for the next intentionally forged input.
        if let ril_syntax::ast::StmtKind::Binding(binding) = &mut parsed.program.statements[1].kind
        {
            binding.value.kind = ril_syntax::ast::ExprKind::Literal(ril_syntax::ast::Literal::Unit);
        }
    }
}

#[test]
fn editing_keeps_the_same_graph_facts_as_a_fresh_session() {
    let first = "meta let ROOT={let child=[1];(child,child)}";
    let second = "meta let ROOT=([1],[1])";
    let mut edited = Session::new(first.as_bytes().to_vec());
    assert!(edited.verify().is_ok());
    edited.update(second.as_bytes().to_vec());
    let edited = edited.verify().unwrap();
    let fresh = Session::new(second.as_bytes().to_vec()).verify().unwrap();
    assert_eq!(
        format!("{:?}", edited.facts().constant_values),
        format!("{:?}", fresh.facts().constant_values)
    );
}

#[test]
fn publication_and_clone_keep_fixed_shapes_and_readonly_paths() {
    let source = "meta let ROOT=([1],[2])\nfn bad() &{ROOT}{let mut value=ROOT.0;value[0]=3}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|d|matches!(d.code.as_str(),"E0520"|"E0528"))),
        "{source}: {outcome:?}"
    );
    let source = "meta fn fixed()->([2]int,[]int){([1,2],[3])}\nmeta let ROOT=fixed()\nfn bad() &{ROOT}{let mut copy=clone(ROOT);copy.0 !> Array::push(4)}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|d|d.code=="E0301")),
        "{outcome:?}"
    );
}

#[test]
fn typed_static_records_cannot_erase_qualification_or_member_types() {
    for source in [
        "type Token(int)\nmeta let ROOT=(Token(1),[2])",
        "meta fn qualified()->([]Immut<[]int>,int){([[1]],2)}\nmeta let ROOT=qualified()",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(
                outcome,
                CompilationOutcome::NotImplemented { .. } | CompilationOutcome::Rejected { .. }
            ),
            "{source}: {outcome:?}"
        );
    }
    let source = "type Row={count:str}\nmeta let ROOT=(Row.{count:1},[2])";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|d|d.code=="E0301")),
        "{outcome:?}"
    );
}

#[test]
fn every_small_selection_preserves_exact_equal_and_disjoint_origins() {
    for left in ["a", "b", "c"] {
        for right in ["a", "b", "c"] {
            let source = format!(
                "meta let ROOT={{let a=[1];let b=[1];let c=[1];({left},{right})}}\nmeta let PICK=Some(ROOT.0)"
            );
            let verified = Session::new(source.into_bytes()).verify().unwrap();
            let facts = verified.facts();
            let root = facts
                .bindings
                .iter()
                .find(|binding| binding.name == "ROOT")
                .unwrap()
                .value
                .origins
                .nodes
                .first()
                .unwrap();
            let first = &facts.fields[&(*root, Slot::Tuple(0))].origins;
            let second = &facts.fields[&(*root, Slot::Tuple(1))].origins;
            assert_eq!(first == second, left == right);
            assert_eq!(first.nodes.is_disjoint(&second.nodes), left != right);
            let pick = &facts
                .bindings
                .iter()
                .find(|binding| binding.name == "PICK")
                .unwrap()
                .value;
            assert_eq!(&pick.option_payload.as_ref().unwrap().origins, first);
        }
    }
}

#[test]
fn core_keeps_node_identity_proofs_without_expression_span_lookup() {
    use ril_ir::{
        constants::ConstNodeKind,
        core::{ExprKind, Statement},
    };
    let source = "meta let ROOT={let child=[1];(child,child)}\nmeta let CHILD=ROOT.0";
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert_eq!(core.constant_graphs.len(), 1);
    let graph = &core.constant_graphs[0];
    let roots: Vec<_> = core
        .globals
        .statements
        .iter()
        .filter_map(|statement| match statement {
            Statement::Bind {
                value:
                    ril_ir::core::Expr {
                        kind: ExprKind::ConstRef(reference),
                        ..
                    },
                ..
            } => Some(*reference),
            _ => None,
        })
        .collect();
    assert_eq!(roots.len(), 2);
    let ConstNodeKind::Tuple(children) = &graph.nodes[roots[0].node.0 as usize].kind else {
        panic!()
    };
    assert_eq!(children[0], children[1]);
    assert_eq!(children[0], roots[1]);
    let distinct_origins: std::collections::BTreeSet<_> = graph
        .nodes
        .iter()
        .flat_map(|node| node.value.origins.iter().map(|origin| origin.0))
        .collect();
    assert_eq!(distinct_origins.len(), 2);
    assert!(
        graph
            .nodes
            .iter()
            .all(|node| node.value.span == graph.nodes[0].value.span)
    );
}

#[test]
fn a_fresh_static_outer_shell_keeps_old_children_shared() {
    let source = "meta let A={let child=[1];[child,child]}\nmeta let B=Array::reverse(A)";
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = verified.facts();
    let a = &facts
        .bindings
        .iter()
        .find(|binding| binding.name == "A")
        .unwrap()
        .value;
    let b = &facts
        .bindings
        .iter()
        .find(|binding| binding.name == "B")
        .unwrap()
        .value;
    assert!(a.origins.nodes.is_disjoint(&b.origins.nodes));
    let a_child = &facts.fields[&(*a.origins.nodes.first().unwrap(), Slot::Index(0))];
    let b_child = &facts.fields[&(*b.origins.nodes.first().unwrap(), Slot::Index(1))];
    assert_eq!(a_child.origins, b_child.origins);
}

#[test]
fn module_forwarding_and_an_edited_dependency_keep_the_same_arena_identity() {
    use ril_compiler::session::ProjectSource;
    let first = "pub meta let ROOT={let child=[1];(child,child)}";
    let second = "pub meta let ROOT=([1],[1])";
    let project = |data: &str| {
        Session::with_project(
            "graph-project/main.ril".into(),
            vec![
                ProjectSource {
                    path: "graph-project/main.ril".into(),
                    bytes: b"use bridge::{ROOT as DATA}\nmeta let SELECTED=DATA.0".to_vec(),
                },
                ProjectSource {
                    path: "graph-project/bridge.ril".into(),
                    bytes: b"pub use data::{ROOT}".to_vec(),
                },
                ProjectSource {
                    path: "graph-project/data.ril".into(),
                    bytes: data.as_bytes().to_vec(),
                },
            ],
            CheckOptions::default(),
        )
        .unwrap()
    };
    let mut edited = project(first);
    let initial = edited.verify().unwrap();
    let core = ril_compiler::lower::lower_core(&initial).unwrap();
    assert_eq!(core.constant_graphs.len(), 1);
    let graph = &core.constant_graphs[0];
    let pair = graph
        .nodes
        .iter()
        .find_map(|node| match &node.kind {
            ril_ir::constants::ConstNodeKind::Tuple(items) => Some(items),
            _ => None,
        })
        .unwrap();
    assert_eq!(pair[0], pair[1]);
    edited
        .update_file(
            std::path::Path::new("graph-project/data.ril"),
            second.as_bytes().to_vec(),
        )
        .unwrap();
    let edited = edited.verify().unwrap();
    let fresh = project(second).verify().unwrap();
    assert_eq!(
        format!("{:?}", edited.facts().constant_values),
        format!("{:?}", fresh.facts().constant_values)
    );
}

#[test]
fn constant_certificates_include_the_solved_empty_collection_types() {
    let source = "meta let EMPTY:[]int=[]\nmeta let PACK=(EMPTY,Some(EMPTY))";
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let array = Ty::Array(Box::new(Ty::Int("int".into())));
    let facts = verified.facts();
    assert!(
        facts
            .constant_values
            .iter()
            .any(|value| value.value.ty == array)
    );
    assert!(facts.constant_values.iter().any(|value| value.value.ty
        == Ty::Tuple(vec![array.clone(), Ty::Optional(Box::new(array.clone()))])));
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert!(
        !core
            .provenance
            .constant_values
            .iter()
            .any(|(_, value)| matches!(
                core.provenance.types[value.ty.0 as usize],
                ril_ir::provenance::Type::Unknown
            ))
    );
}
