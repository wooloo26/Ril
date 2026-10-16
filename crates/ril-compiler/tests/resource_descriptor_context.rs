use ril_compiler::{CompilationOutcome, Session};

#[test]
fn bounded_helper_calls_keep_each_live_endpoint_and_channel() {
    let source = ril_test::case_source("tests/regressions/copy.ril::private-helpers")
        .replace(
            "fn duplicate<T>(source:T)->T @Fiber",
            "fn duplicate(source:Channel::Sender<int>)->Channel::Sender<int> @Fiber",
        )
        .replace(
            "fn forward<T>(source:T)->T @Fiber",
            "fn forward(source:Channel::Sender<int>)->Channel::Sender<int> @Fiber",
        )
        .replace("    assert(duplicate(7)==7)\n", "");
    let checked = Session::new(source.into_bytes()).verify().unwrap();
    let facts = checked.facts();
    let resources = &facts.resource_clones;
    let concrete: Vec<_> = resources
        .iter()
        .filter(|event| {
            let expression = event
                .source_event
                .and_then(|id| facts.copy_call_events[id.0 as usize].callee_expression);
            let context = facts
                .invocation_expressions
                .iter()
                .find(|observation| Some(observation.expression) == expression);
            !context
                .and_then(|event| event.context.closure_invocation)
                .is_some_and(|id| facts.closure_invocations[id.0 as usize].probe)
        })
        .filter_map(|event| {
            event
                .output_descriptor
                .as_ref()
                .filter(|descriptor| !descriptor.formal)
        })
        .collect();
    // Only runtime-context checks count; latent closure probes retain their
    // own separate certificates without inventing another runtime endpoint.
    assert_eq!(concrete.len(), 3);
    assert_eq!(
        concrete
            .iter()
            .map(|value| value.origin)
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        3
    );
    assert_eq!(
        concrete
            .iter()
            .map(|value| value.channel)
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        1
    );
}

#[test]
fn different_channels_do_not_share_message_result_inspections() {
    let source = r#"
use ril/concurrent::{scope,TaskFault}
use ril/concurrent/channel
fn duplicate(tx:Channel::Sender<Result<int,str>>)->Channel::Sender<Result<int,str>> @Fiber{clone(tx)}
fn example() @Async{
    let result=scope \mut s -> {
        let child=s.fork(\->())
        child.join()?
        let (tx,mut rx)=Channel::bounded<Result<int,str>>(1)
        let (other_tx,mut other_rx)=Channel::bounded<Result<int,str>>(1)
        let mut own=duplicate(tx)
        let mut other=duplicate(other_tx)
        let spare=duplicate(tx)
        Channel::close(spare)
        assert((own !> Channel::send(Ok(1))) is Ok())
        assert((other !> Channel::send(Ok(2))) is Ok())
        Channel::close(own)
        Channel::close(other)
        match (rx !> Channel::recv()) {Ok(value)->assert(value is Ok(1)),Err(_)->()}
        match (other_rx !> Channel::recv()) {Ok(value)->assert(value is Ok(2)),Err(_)->()}
        Channel::close(tx)
        Channel::close(other_tx)
        Channel::close(rx)
        Channel::close(other_rx)
        Ok()
    }
    assert(result is Ok())
}
"#;
    Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let unchecked = source.replace(
        "match (rx !> Channel::recv()) {Ok(value)->assert(value is Ok(1)),Err(_)->()}",
        "",
    );
    let outcome = Session::new(unchecked.into_bytes()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|item|item.code=="E0720")),
        "{outcome:?}"
    );
}

#[test]
fn a_same_actual_alias_never_gets_the_new_descriptor_contract() {
    let source = "use ril/concurrent/channel\nfn same(tx:Channel::Sender<int>)->Channel::Sender<int>{tx}\nfn example(tx:Channel::Sender<int>) @Fiber{let alias=same(tx);Channel::close(alias);Channel::close(tx)}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|item|item.code=="E0603")),
        "{outcome:?}"
    );
}

#[test]
fn loop_and_recursive_resource_families_keep_their_unproved_boundaries() {
    for body in [
        "fn example(tx:Channel::Sender<int>,count:int) @Fiber{var saved=duplicate(tx);for 0..count as _{saved=duplicate(tx)};Channel::close(saved)}",
        "fn example(tx:Channel::Sender<int>,depth:int)->Channel::Sender<int> @Fiber{if depth==0{duplicate(tx)}else{example(tx,depth-1)}}",
    ] {
        let source = format!(
            "use ril/concurrent/channel\nfn duplicate(tx:Channel::Sender<int>)->Channel::Sender<int> @Fiber{{clone(tx)}}\n{body}"
        );
        let outcome = Session::new(source.into_bytes()).check();
        assert!(
            matches!(outcome, CompilationOutcome::NotImplemented { .. }),
            "{outcome:?}"
        );
    }
}

#[test]
fn diagnostic_span_collisions_merge_contexts_instead_of_inventing_independence() {
    use ril_syntax::ast::{ExprKind, StmtKind};
    let source = "use ril/concurrent/channel\nfn duplicate(tx:Channel::Sender<int>)->Channel::Sender<int> @Fiber{clone(tx)}\nfn example(tx:Channel::Sender<int>) @Fiber{let first=duplicate(tx);let second=duplicate(tx);let third=duplicate(tx);Channel::close(first);Channel::close(second);Channel::close(third)}";
    Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let mut program = ril_syntax::parse(source).program;
    let mut shared = None;
    for statement in &mut program.statements {
        if let StmtKind::Function(function) = &mut statement.kind
            && function.name == "example"
        {
            for statement in &mut function.body.as_mut().unwrap().statements {
                if let StmtKind::Binding(binding) = &mut statement.kind
                    && matches!(binding.value.kind, ExprKind::Call { .. })
                {
                    binding.value.span = *shared.get_or_insert(binding.value.span);
                }
            }
        }
    }
    let outcome = Session::new(source.as_bytes().to_vec()).verify_program(&program);
    assert!(
        matches!(outcome, Err(CompilationOutcome::NotImplemented { .. })),
        "{outcome:?}"
    );
}
