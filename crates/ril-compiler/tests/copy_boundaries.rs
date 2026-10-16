use ril_compiler::{CompilationOutcome, Session};
use ril_compiler_core::source::FileId;
use ril_ir::provenance as p;

fn accepted(source: &str) {
    let result = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(result, CompilationOutcome::Accepted { .. }),
        "{result:?}"
    );
}

fn rejected(source: &str, code: &str) {
    let result = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&result, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|item| item.code == code)),
        "{result:?}"
    );
}

#[test]
fn actual_empty_payloads_have_no_resource_to_copy() {
    for operation in ["clone", "clone_immut"] {
        accepted(&format!(
            "use ril/file\nfn example(){{let absent:?File::Handle=None;let copied={operation}(absent);assert(copied is None)}}"
        ));
        accepted(&format!(
            "use ril/file\nfn example(){{let absent:?File::Handle=None;let view original=.{{item:absent}};assert({operation}(original).item is None)}}"
        ));
    }
}

#[test]
fn actual_resource_and_environment_payloads_remain_forbidden() {
    rejected(
        "use ril/file\nfn bad(resource:File::Handle){let wrapped=Some(resource);let _=clone_immut(wrapped)}",
        "E0530",
    );
    rejected(
        "fn bad(){let mut value=1;let callback=\\->value;let wrapped=Some(callback);let _=clone_immut(wrapped)}",
        "E0530",
    );
    rejected(
        "eff Read{get()->int}\nfn bad(){let callback={with Read::get()->resume 7;\\->Read::get()};let _=clone(callback)}",
        "E0530",
    );
}

#[test]
fn callable_result_shape_alone_never_proves_environment_free_payload() {
    for source in [
        "fn copied(source:Result<fn()->int,str>)->Result<fn()->int,str>{assert(source is Ok(_)|Err(_));clone(source)}",
        "fn copied(source:Result<{call:fn()->int},str>)->Result<{call:fn()->int},str>{assert(source is Ok(_)|Err(_));clone(source)}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome, CompilationOutcome::NotImplemented { reason } if reason.to_string().contains("callable") && reason.to_string().contains("copy")),
            "{outcome:?}"
        );
    }
}

#[test]
fn opaque_collection_shells_do_not_hide_resource_or_environment_members() {
    rejected(
        "use ril/deque\nuse ril/file\nfn bad(file:File::Handle){let mut queue=Deque::new<File::Handle>();Deque::push_back(mut queue,file);let _=clone(queue)}",
        "E0530",
    );
    rejected(
        "use ril/deque\ntype Reader=fn()->int &closure\nfn bad(){var current=1;current+=1;let mut queue=Deque::new<Reader>();Deque::push_back(mut queue,\\->current);let _=clone(queue)}",
        "E0530",
    );
}

#[test]
fn checked_opaque_collections_keep_real_members_through_readonly_helpers_and_copies() {
    accepted(
        r#"
use ril/deque
use ril/heap
use ril/order
fn keep<T>(source:T)->T{source}
fn example(){
    let mut empty=Deque::new<int>()
    let mut empty_copy=clone(empty)
    assert(Deque::pop_front(mut empty)==None)
    assert(Deque::pop_front(mut empty_copy)==None)
    let mut queue=Deque::new<int>()
    Deque::push_back(mut queue,1)
    let view carried=keep(queue)
    let mut copy=clone(carried)
    assert(Deque::pop_front(mut copy)==Some(1))
    let immutable=clone_immut(carried)
    assert(Deque::len(immutable)==1)
    let mut heap=Heap::new<int>(.{compare:Order::compare_int})
    Heap::push(mut heap,1)
    let mut heap_copy=clone(heap)
    assert(Heap::pop(mut heap_copy)==Some(1))
}
"#,
    );
}

#[test]
fn concrete_callable_payloads_and_scoped_ordinary_copies_remain_valid() {
    accepted(
        "fn example(){let original:Result<fn()->int,str>=Ok(\\->7);assert(original is Ok(_)|Err(_));let copied=clone(original);assert(copied is Ok(_)|Err(_))}",
    );
    accepted(
        "type Guard={on_close:fn()->()}\nfn example(){let scoped original=Guard.{on_close:\\->()};let copied=clone(original);copied.on_close()}",
    );
}

#[test]
fn symbolic_generic_and_row_qualification_are_not_granted_by_fresh_templates() {
    for source in [
        "fn copied<T>(source:T)->T{clone(source)}",
        "fn copied<R>(source:{..R})->{..R}{clone(source)}",
        "eff Read{get()->int}\nfn copied<T>(source:T)->int{with Read::get()->{let _=clone(source);resume 1};Read::get()}",
        "fn copied<T>(depth:int,source:T){if depth==0{let _=clone(source)}else{copied(depth-1,source)}}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome, CompilationOutcome::NotImplemented { .. }),
            "{outcome:?}"
        );
    }
}

#[test]
fn core_copy_evidence_freezes_the_source_graph_and_is_forwarded_through_helpers() {
    let source = "type Cell={mut count:int}\nfn copied(source:Cell)->Cell{clone(source)}\nfn forward(source:Cell)->Cell{copied(source)}\nfn example(){let mut original=Cell.{count:1};let copy=forward(original);original.count=2;assert(copy.count==1)}";
    let parsed = ril_syntax::parse(source);
    let analyzed = ril_compiler::sema::analyze(&parsed.program, FileId(0));
    let verified = analyzed
        .program
        .as_ref()
        .unwrap_or_else(|| panic!("{analyzed:?}"));
    let core = ril_compiler::lower::lower_core(verified).expect("copy provenance");
    let graph = &core.provenance;
    assert!(!graph.copy_boundaries.is_empty());
    for boundary in &graph.copy_boundaries {
        assert!(boundary.owner.is_some());
        assert!(boundary.requirements.is_empty());
        assert!(boundary.output.is_some());
        assert!(
            boundary
                .nodes
                .iter()
                .all(|node| node.origin.id.0 < graph.origins.len() as u32)
        );
        assert!(
            graph
                .invocations
                .iter()
                .any(|call| call.copy_boundaries.contains(&boundary.id))
        );
    }
    let concrete = graph.copy_boundaries.iter().find(|boundary| boundary.nodes.iter().any(|node| node.fields.iter().any(|(_, value)| matches!(&value.constant, Some(p::Constant::Integer(number)) if *number == 1)))).expect("source before the later mutation");
    assert!(
        graph
            .invocations
            .iter()
            .filter(|call| call.copy_boundaries.contains(&concrete.id))
            .count()
            >= 2,
        "helper calls forward the same actual boundary"
    );
}

#[test]
fn discarding_a_handler_or_recursive_copy_result_keeps_its_invocation_obligations() {
    for source in [
        "eff Read{get()->int}\nfn example()->int{with Read::get()->{let _=clone([1]);resume 7};Read::get()}",
        "fn copied(depth:int,source:[]int)->[]int{if depth==0{clone(source)}else{copied(depth-1,source)}}\nfn example(){let _=copied(2,[1])}",
    ] {
        let parsed = ril_syntax::parse(source);
        let analyzed = ril_compiler::sema::analyze(&parsed.program, FileId(0));
        let verified = analyzed
            .program
            .as_ref()
            .unwrap_or_else(|| panic!("{analyzed:?}"));
        let facts = verified.facts();
        let example = facts
            .functions
            .iter()
            .position(|function| function.syntax.name == "example")
            .unwrap();
        let summary = &facts
            .definition_checks
            .iter()
            .find(|check| check.function == example)
            .unwrap()
            .invocation;
        assert!(
            facts.copy_boundaries.iter().any(|boundary| {
                summary.copy_boundaries.contains(&boundary.id)
                    && boundary.constituents.iter().any(|item| {
                        item.source.as_ref().is_some_and(|value| {
                            value.constant == Some(ril_compiler::sema::model::Constant::Integer(1))
                        })
                    })
            }),
            "discarded outputs must not discard the executed copy obligation: {source}"
        );
    }
}
