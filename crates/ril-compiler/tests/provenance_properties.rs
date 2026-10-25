//! Independent finite-graph and execution oracles, plus source-pipeline regressions.
//! Domain tests below do not claim that recursive source summaries are implemented.
use proptest::prelude::*;
use ril_compiler::sema::{
    facts::{
        Heap, HeapNode, NodeId, OriginKind, Participant, Permission, Publication, Reference,
        RootId, ScopeId, SiteId, Slot,
    },
    relations::{Atom, Conditions, Pivot, Relation},
    summary::{InvocationSummary, close_invocation_dependencies},
};
use ril_compiler::{CompilationOutcome, Session};
use ril_compiler_core::diagnostic::CauseId;
use std::collections::BTreeSet;

/// Concrete identity graphs use bit matrices and transitive closure, independently
/// of the production graph's worklist, recency nodes, and Boolean relations.
#[derive(Clone)]
struct ConcreteGraph {
    closure: [[bool; 4]; 4],
}
impl ConcreteGraph {
    fn new(edges: [u8; 4]) -> Self {
        let mut closure = [[false; 4]; 4];
        for (i, row) in closure.iter_mut().enumerate() {
            for (j, entry) in row.iter_mut().enumerate() {
                *entry = i == j || edges[i] & (1 << j) != 0;
            }
        }
        for via in 0..4 {
            for from in 0..4 {
                for to in 0..4 {
                    closure[from][to] |= closure[from][via] && closure[via][to];
                }
            }
        }
        Self { closure }
    }
    fn reachable(&self, root: usize) -> BTreeSet<NodeId> {
        (0..4)
            .filter(|index| self.closure[root][*index])
            .map(|index| NodeId(index as u32))
            .collect()
    }
    fn disjoint(&self, left: usize, right: usize) -> bool {
        (0..4).all(|target| !(self.closure[left][target] && self.closure[right][target]))
    }
}

fn reference(
    origin: u32,
    write: bool,
    publication: Publication,
    owner: u32,
    cause: u32,
) -> Reference {
    Reference {
        origins: [NodeId(origin)].into(),
        permission: if write {
            Permission::Write
        } else {
            Permission::Read
        },
        publication,
        participants: [Participant::Root(RootId(origin))].into(),
        owner: ScopeId(owner),
        cause: CauseId(cause),
    }
}
fn normalize(mut reference: Reference) -> Reference {
    reference.cause = CauseId(0);
    reference
}
fn arbitrary_reference() -> impl Strategy<Value = Reference> {
    (0u32..4, any::<bool>(), 0u8..3, 0u32..4, 0u32..32).prop_map(
        |(origin, write, publication, owner, cause)| {
            reference(
                origin,
                write,
                match publication {
                    0 => Publication::Immutable,
                    1 => Publication::Live,
                    _ => Publication::Unpublished,
                },
                owner,
                cause,
            )
        },
    )
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases:128,
        failure_persistence:Some(Box::new(proptest::test_runner::FileFailurePersistence::Direct(concat!(env!("CARGO_MANIFEST_DIR"),"/../../target/provenance-properties-regressions.txt")))),
        ..ProptestConfig::default()
    })]

    #[test]
    fn reference_join_is_a_semilattice_and_cannot_invent_authority(a in arbitrary_reference(),b in arbitrary_reference(),c in arbitrary_reference()){
        prop_assert_eq!(normalize(a.join(&a,CauseId(50))),normalize(a.clone()));
        prop_assert_eq!(normalize(a.join(&b,CauseId(51))),normalize(b.join(&a,CauseId(52))));
        prop_assert_eq!(normalize(a.join(&b,CauseId(53)).join(&c,CauseId(54))),normalize(a.join(&b.join(&c,CauseId(55)),CauseId(56))));
        let joined=a.join(&b,CauseId(57));
        for origin in a.origins.union(&b.origins){prop_assert!(joined.origins.contains(origin));}
        prop_assert_eq!(joined.permission==Permission::Write,a.permission==Permission::Write&&b.permission==Permission::Write);
        let mut restricted=joined.clone();restricted.restrict(Permission::Read);
        prop_assert_eq!(restricted.permission,Permission::Read);
        prop_assert_ne!(restricted.publication,Publication::Unpublished);
    }

    #[test]
    fn heap_reachability_covers_the_independent_cyclic_graph_oracle(edges in any::<[u8;4]>(),root in 0usize..4){
        let graph=ConcreteGraph::new(edges);
        let mut heap=Heap::default();
        for mask in edges{
            let targets=(0..4).filter(|j|mask&(1<<j)!=0).map(|j|NodeId(j as u32)).collect();
            let fields=[(Slot::AnyIndex,targets)].into();
            heap.insert(HeapNode{kind:OriginKind::Opaque,multiplicity:ril_compiler::sema::facts::Multiplicity::One,owner:ScopeId(0),fields,writable_roots:BTreeSet::new(),escaping:false,cause:CauseId(0)});
        }
        prop_assert_eq!(heap.reachable([NodeId(root as u32)]),graph.reachable(root));
    }

    #[test]
    fn branch_relations_authorize_only_facts_true_in_every_concrete_execution(
        edges in any::<[u8;4]>(),identities in prop::array::uniform4(0usize..4),
        branches in prop::collection::vec((0usize..4,0usize..4,any::<bool>()),1..7)
    ){
        let graph=ConcreteGraph::new(edges);let mut conditions=Conditions::default();
        let mut abstract_relation=None;let mut abstract_reference=None;
        for &(left,right,write) in &branches{
            let next=Relation::symbolic(&mut conditions,Pivot(left as u32),Pivot(right as u32));
            abstract_relation=Some(abstract_relation.map_or(next,|old:Relation|old.join(next,&mut conditions)));
            let next=reference(left as u32,write,Publication::Live,0,0);
            abstract_reference=Some(abstract_reference.map_or_else(||next.clone(),|old:Reference|old.join(&next,CauseId(0))));
        }
        let relation=abstract_relation.unwrap();let reference=abstract_reference.unwrap();
        let known=|atom|match atom{
            Atom::Equal(a,b)=>identities[a.0 as usize]==identities[b.0 as usize],
            Atom::Disjoint(a,b)=>graph.disjoint(identities[a.0 as usize],identities[b.0 as usize]),
        };
        let every_equal=branches.iter().all(|(a,b,_)|identities[*a]==identities[*b]);
        let every_disjoint=branches.iter().all(|(a,b,_)|graph.disjoint(identities[*a],identities[*b]));
        prop_assert_eq!(conditions.evaluate(relation.equal,&known),every_equal);
        prop_assert_eq!(conditions.evaluate(relation.disjoint,&known),every_disjoint);
        prop_assert_eq!(reference.permission==Permission::Write,branches.iter().all(|(_,_,write)|*write));
        let concretized:BTreeSet<_>=reference.origins.iter().map(|origin|identities[origin.0 as usize]).collect();
        for (left,_,_) in branches{prop_assert!(concretized.contains(&identities[left]));}
    }

    #[test]
    fn summary_fixed_point_matches_independent_transitive_call_graph(edges in any::<[u8;4]>()){
        let graph=ConcreteGraph::new(edges);
        let local:Vec<_>=(0..4).map(|i|{let mut summary=InvocationSummary::default();summary.effects.insert(format!("Effect{i}"));summary.retained_origins.insert(NodeId(i));summary}).collect();
        let calls:Vec<BTreeSet<usize>>=(0..4).map(|i|(0..4).filter(|j|edges[i]&(1<<j)!=0).collect()).collect();
        let closed=close_invocation_dependencies(&local,&calls);
        for (i,summary) in closed.iter().enumerate(){
            let expected=graph.reachable(i);let effects:BTreeSet<_>=expected.iter().map(|node|format!("Effect{}",node.0)).collect();
            prop_assert_eq!(&summary.effects,&effects);prop_assert_eq!(&summary.retained_origins,&expected);
        }
        prop_assert_eq!(&closed,&close_invocation_dependencies(&closed,&calls));
    }

    #[test]
    fn source_branch_permutations_and_nearby_alias_branches_match_the_oracle(second_left in any::<bool>(),second_right in any::<bool>(),suffix in 0u16..1000){
        let source=permutation_source(second_left,second_right,suffix);
        let outcome=Session::new(source.as_bytes().to_vec()).check();
        if second_left!=second_right {prop_assert!(matches!(outcome,CompilationOutcome::Accepted{..}),"{outcome:?}\n{source}");}
        else {prop_assert!(has_code(&outcome,"E0523"),"{outcome:?}\n{source}");}
    }
}

fn permutation_source(left: bool, right: bool, suffix: u16) -> String {
    let a = format!("left{suffix}");
    let b = format!("right{suffix}");
    let left = if left { "a" } else { "b" };
    let right = if right { "a" } else { "b" };
    format!(
        "type Cell={{mut value:int}}\nfn swap(mut a:Cell,mut b:Cell)&mut{{let n=a.value;a.value=b.value;b.value=n}}\nfn permute(flag:bool,^mut a:Cell,^mut b:Cell)->(Cell,Cell)&^mut{{if flag{{(^mut a,^mut b)}}else{{(^mut {left},^mut {right})}}}}\nfn example(flag:bool){{let mut {a}=Cell.{{value:1}};let mut {b}=Cell.{{value:2}};let mut pair=permute(flag,^mut {a},^mut {b});swap(mut pair.0,mut pair.1)}}"
    )
}
fn has_code(outcome: &CompilationOutcome, code: &str) -> bool {
    matches!(outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code==code))
}

#[test]
fn source_return_may_origins_cover_both_concrete_permutation_executions() {
    let source = permutation_source(false, true, 999);
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = program.facts();
    let binding = |name: &str| {
        &facts
            .bindings
            .iter()
            .find(|binding| binding.name == name)
            .unwrap()
            .value
    };
    let expected: BTreeSet<_> = binding("left999")
        .origins
        .nodes
        .union(&binding("right999").origins.nodes)
        .copied()
        .collect();
    let pair = binding("pair");
    for component in 0..2 {
        let may: BTreeSet<_> = pair
            .origins
            .nodes
            .iter()
            .flat_map(|root| {
                facts
                    .fields
                    .get(&(*root, Slot::Tuple(component)))
                    .into_iter()
                    .flat_map(|value| value.origins.nodes.iter().copied())
            })
            .collect();
        assert!(
            expected.is_subset(&may),
            "component {component} lost a possible source: expected {expected:?}, actual {may:?}"
        );
    }
}

#[test]
fn fresh_recency_preserves_each_live_allocation_and_never_calls_an_older_summary_unique() {
    let mut heap = Heap::default();
    let mut actual = Vec::new();
    for (next_identity, site) in [0, 0, 1, 0, 1, 1, 0, 0].into_iter().enumerate() {
        let (recent, remap) = heap.fresh(SiteId(site), ScopeId(0), CauseId(0));
        if let Some((from, to)) = remap {
            for (_, abstract_node) in &mut actual {
                if *abstract_node == from {
                    *abstract_node = to;
                }
            }
        }
        actual.push((next_identity, recent));
        for (a, (_, abstract_a)) in actual.iter().enumerate() {
            for (b, (_, abstract_b)) in actual.iter().enumerate() {
                let relation = heap.relation(*abstract_a, *abstract_b);
                if relation.equal == ril_compiler::sema::relations::Condition::TRUE {
                    assert_eq!(
                        a, b,
                        "an older summary cannot prove distinct executions equal"
                    );
                }
                if relation.disjoint == ril_compiler::sema::relations::Condition::TRUE {
                    assert_ne!(
                        a, b,
                        "one concrete allocation cannot be disjoint from itself"
                    );
                }
            }
        }
    }
    assert!(
        heap.nodes.len() <= 4,
        "two allocation sites need only recent/older summaries"
    );
}

#[test]
fn source_clone_keeps_internal_aliases_and_separates_source_storage() {
    let source = "type Cell={mut value:int}\nfn example(){let cell=Cell.{value:0};let mut copy=^mut clone((cell,cell));copy.0.value+=1}";
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = program.facts();
    let original = &facts
        .bindings
        .iter()
        .find(|binding| binding.name == "cell")
        .unwrap()
        .value;
    let copied = &facts
        .bindings
        .iter()
        .find(|binding| binding.name == "copy")
        .unwrap()
        .value;
    let original = facts.heap.reachable(original.origins.nodes.iter().copied());
    let copy = facts.heap.reachable(copied.origins.nodes.iter().copied());
    assert!(original.is_disjoint(&copy));
    for root in &copied.origins.nodes {
        let left = &facts.fields[&(*root, Slot::Tuple(0))].origins.nodes;
        let right = &facts.fields[&(*root, Slot::Tuple(1))].origins.nodes;
        assert!(!left.is_empty());
        assert_eq!(
            left, right,
            "clone must preserve aliases inside one copied graph"
        );
    }
}

#[test]
fn source_clone_preserves_a_cycle_without_aliasing_the_source() {
    let source = "type Node={mut value:int,mut following:?Node}\nfn example(){let mut original=Node.{value:1,following:None};original.following=Some(^mut original);let mut copied=^mut clone(original);copied.value+=1}";
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = program.facts();
    let original = &facts
        .bindings
        .iter()
        .find(|binding| binding.name == "original")
        .unwrap()
        .value;
    let copied = &facts
        .bindings
        .iter()
        .find(|binding| binding.name == "copied")
        .unwrap()
        .value;
    assert!(
        facts
            .heap
            .reachable(original.origins.nodes.iter().copied())
            .is_disjoint(&facts.heap.reachable(copied.origins.nodes.iter().copied()))
    );
    for root in &copied.origins.nodes {
        assert!(
            facts.heap.nodes[root.0 as usize].fields[&Slot::Field("following".into())]
                .contains(root)
        );
    }
}

#[test]
fn incremental_sessions_match_fresh_analysis_after_authority_and_alias_edits() {
    let sources=[
        permutation_source(true,false,0),permutation_source(true,true,0),
        "type Cell={mut value:int}\nfn example(){let mut source=Cell.{value:0};let mut alias=^mut source;alias.value+=1;source.value+=1}".into(),
        "type Cell={mut value:int}\nfn example(){let mut source=Cell.{value:0};let mut alias=source;alias.value+=1;source.value+=1}".into(),
        "type Cell={mut value:int}\nfn identity(cell:Cell)->Cell{cell}\nfn example(){let source=Cell.{value:0};let mut invalid=identity(source);invalid.value+=1}".into(),
        "type Step=fn()->int &closure\nfn make()->Step &capture{var count=0;\\->{count+=1;count}}\nfn example(){let mut step=make();let _=step()}".into(),
        "type Step=fn()->int &closure\nfn make()->Step &capture{var count=0;\\->{count+=1;count}}\nfn example(){let mut step=make();let view readonly=step;let _=readonly()}".into(),
        permutation_source(false,true,0),
    ];
    let mut incremental = Session::new(Vec::new());
    for source in sources.iter().chain(sources.iter().rev()) {
        incremental.update(source.as_bytes().to_vec());
        let fresh = Session::new(source.as_bytes().to_vec());
        assert_eq!(
            format!("{:?}", incremental.check()),
            format!("{:?}", fresh.check()),
            "{source}"
        );
        if let (Ok(incremental), Ok(fresh)) = (incremental.verify(), fresh.verify()) {
            let bindings = |program: &ril_compiler::hir::VerifiedProgram| {
                program
                    .facts()
                    .bindings
                    .iter()
                    .map(|binding| (binding.name.clone(), binding.value.clone()))
                    .collect::<Vec<_>>()
            };
            assert_eq!(bindings(&incremental), bindings(&fresh));
            assert_eq!(incremental.facts().heap.nodes, fresh.facts().heap.nodes);
            assert_eq!(incremental.facts().invocations, fresh.facts().invocations);
        }
    }
}

#[test]
fn unresolved_source_recursion_cannot_manufacture_write_authority() {
    let source = "type Cell={mut value:int}\nfn recur(cell:Cell)->Cell{recur(cell)}\nfn example(){let source=Cell.{value:0};let mut forged=recur(source);forged.value+=1}";
    assert!(!matches!(
        Session::new(source.as_bytes().to_vec()).check(),
        CompilationOutcome::Accepted { .. }
    ));
}

#[test]
fn older_allocation_summaries_keep_all_projected_child_origins() {
    let source = r#"
type Cell={mut value:int}
type Box={child:Cell}
fn wrap(^mut cell:Cell)->Box &^mut {Box.{child:^mut cell}}
fn swap(mut a:Cell,mut b:Cell)&mut {let saved=a.value;a.value=b.value;b.value=saved}
fn example(){
    let mut a=Cell.{value:1};let mut b=Cell.{value:2};let mut c=Cell.{value:3}
    let mut first=wrap(^mut a);let mut second=wrap(^mut b);let mut third=wrap(^mut c)
    first.child.value+=1;second.child.value+=1;third.child.value+=1
    swap(mut second.child,mut b)
}
"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        has_code(&outcome, "E0523"),
        "older summary dropped the second instance's b origin: {outcome:?}"
    );
    let source = source.replace("swap(mut second.child,mut b)", "");
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = program.facts();
    let second = &facts
        .bindings
        .iter()
        .find(|binding| binding.name == "second")
        .unwrap()
        .value;
    let original = &facts
        .bindings
        .iter()
        .find(|binding| binding.name == "b" && !binding.parameter)
        .unwrap()
        .value;
    let may: BTreeSet<_> = second
        .origins
        .nodes
        .iter()
        .flat_map(|root| {
            facts
                .fields
                .get(&(*root, Slot::Field("child".into())))
                .into_iter()
                .flat_map(|value| value.origins.nodes.iter().copied())
        })
        .collect();
    assert!(
        original.origins.nodes.is_subset(&may),
        "older child summary dropped concrete second-call origins: expected {:?}, actual {may:?}",
        original.origins.nodes
    );
}

#[test]
fn separate_calls_do_not_share_one_dynamic_branch_decision() {
    let source = r#"
type Cell={mut value:int}
fn choose(flag:bool,^mut a:Cell,^mut b:Cell)->Cell &^mut {if flag{^mut a}else{^mut b}}
fn swap(mut a:Cell,mut b:Cell)&mut {let saved=a.value;a.value=b.value;b.value=saved}
fn example(first_flag:bool,second_flag:bool){
    let mut a=Cell.{value:1};let mut b=Cell.{value:2}
    let mut first=choose(first_flag,^mut a,^mut b)
    let mut second=choose(second_flag,^mut b,^mut a)
    swap(mut first,mut second)
}

"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        has_code(&outcome, "E0523"),
        "first_flag=true and second_flag=false select the same a storage: {outcome:?}"
    );
}

#[test]
fn zero_iteration_loop_keeps_initial_callable_obligations() {
    let source = r#"
var count=0
fn dangerous() &{mut count} {count+=1}
fn pure() {}
fn example(flag:bool){
    var action=dangerous
    while flag { action=pure }
    action()
}
"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        has_code(&outcome, "E0510"),
        "zero loop iterations still invoke dangerous and need its named state: {outcome:?}"
    );
}

#[test]
fn recursive_summary_keeps_readonly_reception_of_a_clone() {
    let source = "type Cell={mut value:int}\nfn frozen(n:int,source:Cell)->Cell{let saved=clone(source);if n==0{saved}else{frozen(n-1,source)}}\nfn example(){let source=Cell.{value:1};let mut forged=frozen(1,source);forged.value+=1}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        has_code(&outcome, "E0528"),
        "readonly reception cannot become writable at recursive return: {outcome:?}"
    );
}

#[test]
fn recursive_source_identity_preserves_readonly_origins() {
    let common = "type Cell={mut value:int}\nfn identity(n:int,value:Cell)->Cell{if n==0{value}else{identity(n-1,value)}}\n";
    let valid = format!(
        "{common}fn example(){{let source=Cell.{{value:1}};let result=identity(3,source);assert(result.value==1)}}"
    );
    let outcome = Session::new(valid.into_bytes()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
    let invalid = format!(
        "{common}fn example(){{let source=Cell.{{value:1}};let mut forged=identity(3,source);forged.value+=1}}"
    );
    let outcome = Session::new(invalid.into_bytes()).check();
    assert!(has_code(&outcome, "E0528"), "{outcome:?}");
}

#[test]
fn recursive_source_fresh_and_clone_factories_instantiate_distinct_results() {
    for factory in [
        "fn factory(n:int,source:Cell)->Cell{if n==0{Cell.{value:1}}else{factory(n-1,source)}}",
        "fn factory(n:int,source:Cell)->Cell{if n==0{clone(source)}else{factory(n-1,source)}}",
    ] {
        let source = format!(
            "type Cell={{mut value:int}}\n{factory}\nfn swap(mut a:Cell,mut b:Cell)&mut{{let n=a.value;a.value=b.value;b.value=n}}\nfn example(){{let source=Cell.{{value:0}};let mut a=factory(2,source);let mut b=factory(3,source);swap(mut a,mut b)}}"
        );
        let outcome = Session::new(source.into_bytes()).check();
        assert!(
            matches!(outcome, CompilationOutcome::Accepted { .. }),
            "{outcome:?}"
        );
    }
}

#[test]
fn mutual_recursive_source_retains_a_base_case_return_relation() {
    let source = "type Cell={mut value:int}\nfn first(n:int,value:Cell)->Cell{if n==0{value}else{second(n-1,value)}}\nfn second(n:int,value:Cell)->Cell{first(n,value)}\nfn example(){let source=Cell.{value:1};let result=second(3,source);assert(result.value==1)}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
}

#[test]
fn recursive_retained_result_keeps_the_original_alias_identity() {
    let source = "type Cell={mut value:int}\nfn retain(n:int,^mut value:Cell)->Cell &^mut{if n==0{^mut value}else{retain(n-1,^mut value)}}\nfn swap(mut a:Cell,mut b:Cell)&mut{let saved=a.value;a.value=b.value;b.value=saved}\nfn example(){let mut source=Cell.{value:1};let mut alias=retain(2,^mut source);swap(mut source,mut alias)}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(has_code(&outcome, "E0523"), "{outcome:?}");
}

#[test]
fn recursive_callback_forwarding_keeps_actual_named_state_obligations() {
    let common = "var count=0\nfn action() &{mut count}{count+=1}\nfn invoke(n:int,callback:fn()->()){if n==0{callback()}else{invoke(n-1,callback)}}\n";
    let source = format!("{common}fn example(){{invoke(2,action)}}");
    let outcome = Session::new(source.into_bytes()).check();
    assert!(has_code(&outcome, "E0510"), "{outcome:?}");
    let source = format!("{common}fn example() &{{mut count}}{{invoke(2,action)}}");
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
}

#[test]
fn recursive_temporary_loans_preserve_forwarding_and_ambient_alias_conflicts() {
    let valid = "type Cell={mut value:int}\nfn advance(n:int,mut cell:Cell)&mut{if n==0{cell.value+=1}else{advance(n-1,mut cell)}}\nfn example(){let mut value=Cell.{value:0};advance(2,mut value)}";
    let outcome = Session::new(valid.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
    let invalid = "type Cell={mut value:int}\nlet mut ambient=Cell.{value:0}\nfn touch(n:int,mut target:Cell)&mut &{ambient}{if n==0{target.value=ambient.value}else{touch(n-1,mut target)}}\nfn example() &{mut ambient}{touch(2,mut ambient)}";
    let outcome = Session::new(invalid.as_bytes().to_vec()).check();
    assert!(
        has_code(&outcome, "E0524"),
        "temporary recursive loan must not absorb an independent ambient root: {outcome:?}"
    );
}

#[test]
fn recursive_clone_preserves_cyclic_shape_and_external_isolation() {
    let source = "type Node={mut value:int,mut following:?Node}\nfn copy(n:int,source:Node)->Node{if n==0{clone(source)}else{copy(n-1,source)}}\nfn example(){let mut original=Node.{value:1,following:None};original.following=Some(^mut original);let mut copied=^mut copy(2,original);copied.value+=1}";
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = program.facts();
    let original = &facts
        .bindings
        .iter()
        .find(|binding| binding.name == "original")
        .unwrap()
        .value;
    let copied = &facts
        .bindings
        .iter()
        .find(|binding| binding.name == "copied")
        .unwrap()
        .value;
    assert!(
        facts
            .heap
            .reachable(original.origins.nodes.iter().copied())
            .is_disjoint(&facts.heap.reachable(copied.origins.nodes.iter().copied()))
    );
    for root in &copied.origins.nodes {
        assert!(
            facts.heap.nodes[root.0 as usize].fields[&Slot::Field("following".into())]
                .contains(root)
        );
    }
}

#[test]
fn recursive_retention_does_not_require_new_return_marker_syntax() {
    let source = "type Cell={mut value:int}\nfn retain(n:int,^mut value:Cell)->Cell &^mut{if n==0{value}else{retain(n-1,^mut value)}}\nfn example(){let mut source=Cell.{value:1};let mut returned=retain(2,^mut source);returned.value+=1}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
}

#[test]
fn match_payload_alias_preserves_a_temporary_loan_without_freezing_it() {
    let source = "type Cell={mut value:int}\nfn advance(mut cell:Cell)&mut{match Some(cell){Some(alias)->{assert(alias.value==cell.value);cell.value+=1},None->{cell.value+=1}}}\nfn example(){let mut cell=Cell.{value:1};advance(mut cell)}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
    let invalid = "type Cell={mut value:int}\nfn example(source:?Cell){match source{Some(mut forged)->{forged.value+=1},None->()}}";
    let outcome = Session::new(invalid.as_bytes().to_vec()).check();
    assert!(
        has_code(&outcome, "E0520"),
        "match cannot upgrade a readonly payload: {outcome:?}"
    );
}

#[test]
fn match_result_inspection_requires_coverage_on_every_reachable_arm() {
    for (source, accepted) in [
        (
            "fn example(){let result:Result<int,str>=Ok(1);match result{Ok(_)->(),Err(_)->()}}",
            true,
        ),
        (
            "fn example(flag:bool){let result:Result<int,str>=Ok(1);match flag{true->{assert(result is Ok(_))},false->()}}",
            false,
        ),
        (
            "fn example(){let result:Result<Result<int,str>,str>=Ok(Err(\"nested\"));match result{Ok(_)->(),Err(_)->()}}",
            false,
        ),
        (
            "fn example(){let result:Result<Result<int,str>,str>=Ok(Err(\"nested\"));match result{Ok(inner)->match inner{Ok(_)->(),Err(_)->()},Err(_)->()}}",
            true,
        ),
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        if accepted {
            assert!(
                matches!(outcome, CompilationOutcome::Accepted { .. }),
                "{source}: {outcome:?}"
            );
        } else {
            assert!(has_code(&outcome, "E0720"), "{source}: {outcome:?}");
        }
    }
}

#[test]
fn match_whole_return_alternatives_preserve_permutation_and_reject_nearby_aliases() {
    for (left, right) in [(false, true), (true, false), (true, true), (false, false)] {
        let source = permutation_source(left, right, 700).replace(
            "if flag{(^mut a,^mut b)}else{",
            "match flag{true->(^mut a,^mut b),false->",
        );
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        if left != right {
            assert!(
                matches!(outcome, CompilationOutcome::Accepted { .. }),
                "{source}: {outcome:?}"
            );
        } else {
            assert!(has_code(&outcome, "E0523"), "{source}: {outcome:?}");
        }
    }
}

#[test]
fn deep_source_accesses_match_an_independent_storage_identity_oracle() {
    // The concrete graph is outer -> inner -> selected cell. Neither syntactic
    // path spelling nor the distinct outer allocation separates that child.
    for selected in 0..4 {
        for target in 0..4 {
            let definitions = (0..4)
                .map(|index| format!("let mut cell{index}=Cell.{{value:{index}}};"))
                .collect::<String>();
            let exercise = (0..4)
                .map(|index| format!("cell{index}.value+=1;"))
                .collect::<String>();
            let source = format!(
                "type Cell={{mut value:int}}\ntype Inner={{child:Cell}}\ntype Outer={{inner:Inner}}\nfn wrap(^mut cell:Cell)->Outer &^mut{{Outer.{{inner:Inner.{{child:^mut cell}}}}}}\nfn transfer(source:Outer,mut target:Cell)&mut{{target.value=source.inner.child.value}}\nfn example(){{{definitions}var outer=wrap(^mut cell{selected});transfer(outer,mut cell{target});{exercise}outer=Outer.{{inner:Inner.{{child:Cell.{{value:0}}}}}}}}"
            );
            let outcome = Session::new(source.as_bytes().to_vec()).check();
            if selected == target {
                assert!(
                    has_code(&outcome, "E0524"),
                    "concrete deep read reaches the active write loan: {source}: {outcome:?}"
                );
            } else {
                assert!(
                    matches!(outcome, CompilationOutcome::Accepted { .. }),
                    "distinct concrete leaves: {source}: {outcome:?}"
                );
            }
        }
    }
}

#[test]
fn nullary_pattern_parentheses_are_not_erased_before_validation() {
    for source in [
        "fn example(value:?int)->bool{value is None()}",
        "fn example(value:?int){match value{Some(_)->(),None()->()}}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(has_code(&outcome, "E0353"), "{source}: {outcome:?}");
    }
}

#[test]
fn scoped_authority_cannot_escape_through_values_closures_or_outer_assignments() {
    let prefix = "type Guard={on_close:fn()->()}\n";
    for body in [
        "fn escape()->Guard{let scoped guard=Guard.{on_close:\\->()};guard}",
        "fn escape()->(Guard,int){let scoped guard=Guard.{on_close:\\->()};(guard,1)}",
        "fn escape()->fn()->() &closure{let scoped guard=Guard.{on_close:\\->()};\\->{let _=guard}}",
        "fn example(){var saved:?Guard=None;{let scoped guard=Guard.{on_close:\\->()};saved=Some(guard)};saved=None}",
    ] {
        let source = format!("{prefix}{body}");
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            has_code(&outcome, "E0604"),
            "scoped authority must stay within its registration scope: {source}: {outcome:?}"
        );
    }
    let source = format!(
        "{prefix}fn detached()->Guard{{let scoped guard=Guard.{{on_close:\\->()}};clone(guard)}}"
    );
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "detached ordinary-data clone: {outcome:?}"
    );
}

#[test]
fn constructor_payload_coverage_keeps_every_tuple_component_and_unit_arity() {
    for (source, code) in [
        (
            "fn example(value:?(int,bool)){match value{Some(_,true)->(),None->()}}",
            "E0303",
        ),
        (
            "fn example(value:Result<int,str>){match value{Ok()->(),Err(_)->()}}",
            "E0314",
        ),
        (
            "fn example(value:Result<int,str>)->bool{value is Ok()}",
            "E0314",
        ),
        (
            "fn example(value:Result<(int,int),str>){match value{Ok(_,_)->(),Ok((_,_))->(),Err(_)->()}}",
            "E0304",
        ),
        (
            "fn example(value:bool){match value{true->(),false->(),_->()}}",
            "E0304",
        ),
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(has_code(&outcome, code), "{source}: {outcome:?}");
    }
}

#[test]
fn match_arm_refinements_cannot_authorize_an_unwrap_on_another_path() {
    for body in [
        "match flag{true->{if value==None{return};assert(value.id==1)},false->()};let _=value.id",
        "match flag{true->{if value==None{return};assert(value.id==1)},false->{let _=value.id}}",
    ] {
        let source = format!("type Cell={{id:int}}\nfn example(flag:bool,value:?Cell){{{body}}}");
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            has_code(&outcome, "E0310"),
            "the false arm admits None and cannot inherit another arm's unwrap proof: {source}: {outcome:?}"
        );
    }
}

#[test]
fn an_unknown_constructor_tag_test_cannot_discard_an_aliasing_branch() {
    let source = r#"
type Cell={mut value:int}
fn choose(flag:Result<int,str>,^mut a:Cell,^mut b:Cell)->Cell &^mut{b.value+=0;if flag is Ok(_){^mut a}else{^mut b}}
fn swap(mut a:Cell,mut b:Cell)&mut{let n=a.value;a.value=b.value;b.value=n}
fn example(flag:Result<int,str>){let mut a=Cell.{value:1};let mut b=Cell.{value:2};let mut selected=choose(flag,^mut a,^mut b);swap(mut selected,mut b)}
"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        has_code(&outcome, "E0523"),
        "Err selects b, so both loan participants can access the same storage: {outcome:?}"
    );
}

#[test]
fn published_optional_payloads_do_not_reuse_construction_or_an_old_share_acknowledgment() {
    let source = "type Cell={mut value:int}\nfn example(){let mut cell=Cell.{value:0};let mut wrapped=Some(^mut cell);match wrapped{Some(mut alias)->{alias.value+=1},None->()};cell.value+=1}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        has_code(&outcome, "E0510"),
        "a published Some must not preserve a fresh-construction exemption or stale ^mut acknowledgment: {outcome:?}"
    );
    let source = "type Cell={mut value:int}\nfn retain(^mut value:Cell)->Cell &^mut{^mut value}\nfn touch(mut item:?Cell)&mut{if item!=None{item.value+=0}}\nfn example(){let mut cell=Cell.{value:0};let mut wrapped=Some(retain(^mut cell));touch(mut wrapped);match wrapped{Some(mut alias)->{alias.value+=1},None->()};cell.value+=1}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        has_code(&outcome, "E0510"),
        "a published wrapper must not keep the one-time retained-return reception of its stored payload: {outcome:?}"
    );
}

#[test]
fn nominal_equality_availability_checks_callable_payloads() {
    let source = "type Callback(fn()->())\nfn example(){let wrapped=Callback(\\->());let expected=wrapped;assert(wrapped is expected)}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        has_code(&outcome, "E0327"),
        "nominal wrapping does not grant equality to a callable constituent: {outcome:?}"
    );
}

#[test]
fn match_rejects_a_callable_expression_as_a_constructor_pattern() {
    let source = "fn expected()->int{42}\nfn example(result:Result<int,str>)->bool{match result{Ok(expected())->true,Err(_)->false,Ok(_)->false}}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(has_code(&outcome, "E0349"), "{outcome:?}");
}

#[test]
fn match_array_cardinality_is_a_common_heap_fact_of_reachable_paths() {
    for source in [
        "fn example(flag:bool){let mut items=match flag{true->[1,2,3],false->[4,5,6]};items[0]=7;let view copied:[3]int=items;assert(len(copied)==3)}",
        "fn example(){let mut items=[1,2];items[0]=7;match Some(1){Some(_)->(),None->items !> Array::push(3)};let view copied:[2]int=items;assert(len(copied)==2)}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome, CompilationOutcome::Accepted { .. }),
            "{source}: {outcome:?}"
        );
    }
    let source = "fn example(flag:bool){let mut items=[1,2];match flag{true->items !> Array::push(3),false->()};let view copied:[2]int=items;assert(len(copied)==2)}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        !matches!(outcome, CompilationOutcome::Accepted { .. }),
        "one path has three elements: {outcome:?}"
    );
}

#[test]
fn iteration_local_result_families_require_every_nested_producer_to_be_inspected() {
    for source in [
        "fn example(){for [1,2,3] as number{let parsed:Result<int,str>=Ok(number);assert(parsed is Ok(_))}}",
        "fn example(){for [1,2,3] as number{let parsed:Result<Result<int,str>,str>=Ok(Ok(number));assert(parsed is Ok(Ok(_)))}}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome, CompilationOutcome::Accepted { .. }),
            "{source}: {outcome:?}"
        );
    }
    for source in [
        "fn example(flag:bool){for [1,2,3] as number{let parsed:Result<int,str>=Ok(number);if flag{next};assert(parsed is Ok(_))}}",
        "fn example(values:[]int){let parsed:Result<int,str>=Ok(1);for values as number{assert(parsed is Ok(_))}}",
        "fn example(){for [1,2,3] as number{let parsed:Result<Result<int,str>,str>=Ok(Ok(number));assert(parsed is Ok(_))}}",
        "fn example(){let mut saved:[]Result<int,str>=[];for [1,2,3] as number{let parsed:Result<int,str>=Ok(number);assert(parsed is Ok(_));saved !> Array::push(parsed)};let copied=clone(saved);assert(copied[0] is Ok(_))}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            !matches!(outcome, CompilationOutcome::Accepted { .. }),
            "an outstanding producer remains on a reachable path: {source}: {outcome:?}"
        );
    }
}

#[test]
fn generic_value_tests_require_equality_for_the_actual_instantiation() {
    let source = ril_test::case_source(
        "tests/regressions/testing-declarations.ril::reject-generic-value-test-callable",
    );
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        has_code(&outcome, "E0327"),
        "the selected callable type cannot acquire equality: {outcome:?}"
    );
}

#[test]
fn skipped_value_pattern_components_do_not_exercise_write_authority() {
    for source in [
        "type Cell={mut value:int}\nfn example(){let mut cell=Cell.{value:0};assert(1 is 1 | {cell.value=1;2})}",
        "type Cell={mut value:int}\nfn example(){let mut cell=Cell.{value:0};assert(!((1,2) is (0,{cell.value=1;2})))}",
        "type Cell={mut value:int}\nfn example(){let mut cell=Cell.{value:0};let subject:?int=None;assert(!(subject is Some({cell.value=1;2})))}",
        "type Cell={mut value:int}\nfn example(){let mut cell=Cell.{value:0};assert((1,2) is (panic(\"stop\"),{cell.value=1;2}))}",
        "type Cell={mut value:int}\nfn example(){let mut cell=Cell.{value:0};assert(!((3,0) is (1..3,{cell.value=1;0})))}",
        "type Cell={mut value:int}\nfn example(){let mut cell=Cell.{value:0};match panic(\"stop\"){_->{cell.value=1}}}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            has_code(&outcome, "E0527"),
            "an unreachable expected expression cannot exercise a writer: {source}: {outcome:?}"
        );
    }
}

#[test]
fn a_delimited_abort_in_a_match_subject_cannot_inspect_an_older_result() {
    let source = "eff Stop{now()->int}\nfn example(){let older:Result<int,str>=Ok(1);{with Stop::now()->();match Stop::now(){_->assert(older is Ok(_))}}}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        has_code(&outcome, "E0720"),
        "the arm never executes, and the producer predates the aborted block: {outcome:?}"
    );
}

#[test]
fn value_tests_do_not_grant_equality_to_resources_inside_wrappers() {
    for shape in [
        "File::Handle",
        "?File::Handle",
        "[]File::Handle",
        "{handle:File::Handle}",
    ] {
        let source = format!(
            "use ril/file\nfn example(value:{shape}){{let view expected=value;assert(value is expected)}}"
        );
        let directory = tempfile::tempdir().unwrap();
        let input = directory.path().join("resource-equality.ril");
        std::fs::write(&input, &source).unwrap();
        let outcome = ril_compiler::driver::check_path(&input, "pointer64").unwrap();
        assert!(
            has_code(&outcome, "E0327"),
            "a wrapper cannot add resource equality: {source}: {outcome:?}"
        );
    }
}

#[test]
fn excluded_generic_variants_are_typed_without_committing_preview_state() {
    for source in [
        "type Box<T>{Item(T),Empty}\nfn read(value:Box<int>)->int{match value{Box::Item(number)->number,Box::Empty->-1}}\nfn example(){assert(read(Box::Empty<int>) == -1)}",
        "type Box<T>{Item(T),Empty}\nfn example(){let mut items=[1,2];match Box::Empty<int>{Box::Item(_)->items !> Array::push(3),Box::Empty->()};items[0]=4;let view fixed:[2]int=items;assert(len(fixed)==2)}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome, CompilationOutcome::Accepted { .. }),
            "unreachable payload typing must be isolated: {source}: {outcome:?}"
        );
    }
    let source = "type Cell={mut value:int}\ntype Box<T>{Item(T),Empty}\nfn example(){let mut cell=Cell.{value:0};match Box::Empty<int>{Box::Item(_)->{cell.value=1},Box::Empty->()}}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        has_code(&outcome, "E0527"),
        "a preview cannot exercise actual authority: {outcome:?}"
    );
}

#[test]
fn a_user_prelude_type_cannot_replace_the_standard_constructor_identity() {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("constructor-identity.ril");
    let source = "type Prelude{Some(int)}\nfn example(value:Prelude){assert(value is Some(_))}";
    std::fs::write(&input, source).unwrap();
    let outcome = ril_compiler::driver::check_path(&input, "pointer64").unwrap();
    assert!(
        has_code(&outcome, "E0301"),
        "unqualified Some retains the outer prelude's identity: {outcome:?}"
    );
    let in_memory = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        has_code(&in_memory, "E0301"),
        "in-memory checking retains the same constructor identity: {in_memory:?}"
    );
}

#[test]
fn executable_entry_cannot_request_an_unprovided_user_effect_handler() {
    for source in [
        "eff Read{get()->int}\npub fn main() @Read{assert(Read::get()==1)}",
        "eff Read{get()->int}\nfn fetch()->int @Read{Read::get()}\npub fn main() @Read{assert(fetch()==1)}",
    ] {
        let options = ril_compiler::CheckOptions {
            unit: ril_compiler::UnitKind::Executable,
            ..Default::default()
        };
        let outcome = Session::with_options(source.as_bytes().to_vec(), options).check();
        assert!(
            has_code(&outcome, "E0612"),
            "the program environment supplies no user handler: {source}: {outcome:?}"
        );
        let library = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(library, CompilationOutcome::Accepted { .. }),
            "an ordinary library callable can retain a declared effect: {library:?}"
        );
    }
    let handled = "eff Read{get()->int}\nfn fetch()->int @Read{Read::get()}\npub fn main(){with Read::get()->resume 1;assert(fetch()==1)}";
    let options = ril_compiler::CheckOptions {
        unit: ril_compiler::UnitKind::Executable,
        ..Default::default()
    };
    let outcome = Session::with_options(handled.as_bytes().to_vec(), options).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "a locally handled operation has no residual effect: {outcome:?}"
    );
}

#[test]
fn concrete_gadt_equations_exclude_only_the_matching_family_without_exercising_authority() {
    let declaration = "type Expr<T>{Int(int)->Expr<int>,Bool(bool)->Expr<bool>}";
    let valid = format!(
        "{declaration}\nfn read(value:Expr<int>)->int{{match value{{Expr::Int(number)->number}}}}\nfn example(){{let value:Expr<int>=Expr::Int(7);assert(read(value)==7)}}"
    );
    let outcome = Session::new(valid.into_bytes()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "a concrete instance covers only feasible constructor equations: {outcome:?}"
    );
    for arms in [
        "Expr::Bool(_)->0,Expr::Int(number)->number",
        "Expr::Int(number)->number,Expr::Bool(_)->0",
    ] {
        let source =
            format!("{declaration}\nfn read(value:Expr<int>)->int{{match value{{{arms}}}}}");
        let outcome = Session::new(source.into_bytes()).check();
        assert!(
            has_code(&outcome, "E0304"),
            "a solved impossible equation is an unreachable arm: {outcome:?}"
        );
    }
    let source = format!(
        "{declaration}\ntype Other{{Bool(bool)}}\nfn read(value:Expr<int>)->int{{match value{{Other::Bool(_)->0,Expr::Int(number)->number}}}}"
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        has_code(&outcome, "E0301"),
        "a different family has no equation-based exclusion proof: {outcome:?}"
    );
    let source = format!(
        "{declaration}\ntype Cell={{mut value:int}}\nfn example(){{let mut cell=Cell.{{value:0}};let value:Expr<int>=Expr::Int(7);match value{{Expr::Bool(_)->{{cell.value=1}},Expr::Int(_)->()}}}}"
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(has_code(&outcome, "E0304"), "{outcome:?}");
    assert!(
        has_code(&outcome, "E0527"),
        "an excluded arm cannot exercise write authority: {outcome:?}"
    );
}

#[test]
fn primitive_gadt_arm_equations_transport_only_the_tested_arm_result() {
    let declaration = "type Expr<T>{Int(int)->Expr<int>,Bool(bool)->Expr<bool>}";
    let source = format!(
        "{declaration}\nfn eval<T>(value:Expr<T>)->T{{match value{{Expr::Int(number)->number,Expr::Bool(flag)->flag}}}}\nfn example(){{assert(eval(Expr::Int(7))==7);assert(eval(Expr::Bool(true)))}}"
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "each tested constructor supplies only its own result equation: {outcome:?}"
    );
    for body in [
        "match value{Expr::Int(number)->number,Expr::Bool(_)->42}",
        "match value{Expr::Int(number)->{let unrelated:T=number;unrelated},Expr::Bool(flag)->flag}",
    ] {
        let source = format!("{declaration}\nfn wrong<T>(value:Expr<T>)->T{{{body}}}");
        let outcome = Session::new(source.into_bytes()).check();
        assert!(
            !matches!(outcome, CompilationOutcome::Accepted { .. }),
            "an arm equation cannot change another arm or an ambient rigid binding: {outcome:?}"
        );
    }
}

#[test]
fn duplicate_pattern_binders_use_the_pattern_diagnostic_before_scope_declarations() {
    for source in [
        "fn example(){let(same,same)=(1,2)}",
        "fn example(){for [(1,2)] as (same,same){}}",
        "fn example(value:(int,int)){match value{(same,same)->()}}",
        "eff Pair{apply((int,int))->()}\nfn example(){with Pair::apply((same,same))->();Pair::apply((1,2))}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(has_code(&outcome, "E0347"), "{source}: {outcome:?}");
        assert!(
            !has_code(&outcome, "E0203"),
            "one pattern branch is not two scope declarations: {source}: {outcome:?}"
        );
        let directory = tempfile::tempdir().unwrap();
        let input = directory.path().join("duplicate-pattern.ril");
        std::fs::write(&input, source).unwrap();
        let outcome = ril_compiler::driver::check_path(&input, "pointer64").unwrap();
        assert!(has_code(&outcome, "E0347"), "{source}: {outcome:?}");
    }
    let valid = "type Choice{Left(int),Right(int)}\nfn read(value:Choice)->int{match value{Choice::Left(number)|Choice::Right(number)->number}}";
    let outcome = Session::new(valid.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
    let outcome = Session::new(b"fn example(){let same=1;let same=2}".to_vec()).check();
    assert!(has_code(&outcome, "E0203"), "{outcome:?}");
    assert!(!has_code(&outcome, "E0347"), "{outcome:?}");
}

#[test]
fn source_budget_termination_retains_actual_coverage_and_never_certifies_latent_work() {
    let source = "fn spin()->int{loop{}}\nhalt fn bounded()->?int{with Div::exhausted()->None;Some(Div::budget(20,spin))}";
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = verified.facts();
    assert!(!facts.budget_proofs.is_empty());
    assert!(!facts.termination["bounded"].unresolved);
    assert!(!facts.termination["bounded"].may_diverge);
    assert!(facts.termination["spin"].may_diverge);
    for proof in &facts.budget_proofs {
        let witness = facts
            .budget_termination
            .iter()
            .find(|witness| witness.span == proof.span && witness.cause == proof.cause)
            .expect("the finite conclusion must reference the finalized coverage certificate");
        assert_eq!(witness.exhaustion_operation, proof.exhaustion_operation);
        assert!(!witness.callee_coverage.is_empty());
        assert!(witness.action_invocation.may_diverge);
        assert!(!witness.explicit_evaluation.unresolved);
        assert!(!witness.explicit_evaluation.may_diverge);
        assert!(!witness.recovery.unresolved && !witness.recovery.may_diverge);
        assert!(
            facts
                .explanations
                .causes
                .iter()
                .any(|cause| cause.id == proof.cause)
        );
    }
    let without_certificates = ril_compiler::termination::analyze(verified.syntax());
    assert!(without_certificates.judgments["bounded"].unresolved);
    for source in [
        "fn spin()->int{loop{}}\nhalt fn bad()->?int{with Div::exhausted()->None;Some(Div::budget(spin(),\\->1))}",
        "fn spin()->int{loop{}}\nhalt fn bad()->?int{with Div::exhausted()->spin();Some(Div::budget(20,spin))}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            !matches!(outcome, CompilationOutcome::Accepted { .. }),
            "{outcome:?}"
        );
    }
}

#[test]
fn generic_multi_payload_sum_aliases_cannot_turn_readonly_payloads_writable() {
    let declarations =
        "type Cell={mut value:int}\ntype Bundle<T>{Empty,Pair(T,T)}\ntype Alias<T>=Bundle<T>";
    let source = format!(
        "{declarations}\nfn read(value:Alias<Cell>)->int{{match value{{Bundle::Empty->0,Bundle::Pair(left,right)->left.value+right.value}}}}"
    );
    let outcome = Session::new(source.into_bytes()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "readonly access through both generic payloads remains usable: {outcome:?}"
    );
    for payload in ["left", "right"] {
        let source = format!(
            "{declarations}\nfn bad(value:Alias<Cell>){{match value{{Bundle::Empty->(),Bundle::Pair(left,right)->{{let mut writable={payload};writable.value+=1}}}}}}"
        );
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            has_code(&outcome, "E0520"),
            "a generic sum alias cannot grant write authority to either readonly payload: {source}: {outcome:?}"
        );
    }
}

#[test]
fn generic_multi_payload_sum_aliases_keep_each_actual_storage_origin() {
    for payload in ["left", "right"] {
        for target in ["first", "second"] {
            let source = format!(
                "type Cell={{mut value:int}}\ntype Bundle<T>{{Empty,Pair(T,T)}}\ntype Alias<T>=Bundle<T>\nfn wrap(flag:bool,^mut first:Cell,^mut second:Cell)->Alias<Cell> &^mut{{if flag{{Bundle::Empty}}else{{Bundle::Pair(^mut first,^mut second)}}}}\nfn transfer(source:Alias<Cell>,mut target:Cell)&mut{{match source{{Bundle::Empty->(),Bundle::Pair(left,right)->{{target.value={payload}.value}}}}}}\nfn example(flag:bool){{let mut first=Cell.{{value:1}};let mut second=Cell.{{value:2}};var wrapped=wrap(flag,^mut first,^mut second);transfer(wrapped,mut {target});first.value+=1;second.value+=1;wrapped=Bundle::Empty<Cell>}}"
            );
            let outcome = Session::new(source.as_bytes().to_vec()).check();
            let aliases = matches!((payload, target), ("left", "first") | ("right", "second"));
            if aliases {
                assert!(
                    has_code(&outcome, "E0524"),
                    "this payload reads storage held by the target's active write loan: {source}: {outcome:?}"
                );
            } else {
                assert!(
                    matches!(outcome, CompilationOutcome::Accepted { .. }),
                    "the two actual payload origins are distinct: {source}: {outcome:?}"
                );
            }
        }
    }
}
