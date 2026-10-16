use ril_compiler::sema::effect_identity::ArgumentKey;
use ril_compiler::{CompilationOutcome, Session};

fn verified(source: &str) -> ril_compiler::hir::VerifiedProgram {
    Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|outcome| panic!("{source}: {outcome:?}"))
}

#[test]
fn same_spelled_binders_remain_distinct_and_native_requires_specialization() {
    let program = verified(
        "eff Read<T>{get()->T}\nfn first<T>()->T @Read<T>{Read<T>::get()}\nfn second<T>()->T @Read<T>{Read<T>::get()}",
    );
    let instances = &program.facts().effect_instances;
    assert_eq!(instances.len(), 2);
    assert_ne!(instances[0].key, instances[1].key);
    assert!(instances.iter().all(|instance|matches!(&instance.key.arguments[..],[ArgumentKey::Binder {identity,..}] if program.facts().generic_binders.contains_key(identity))));
    assert!(
        ril_compiler::lower::lower_core(&program)
            .unwrap_err()
            .detail
            .contains("specialization")
    );
}

#[test]
fn actual_calls_keep_closed_instances_and_forwarded_binder_dependencies() {
    let program = verified(
        "eff Read<T>{get()->T}\nfn read<U>(witness:U)->U @Read<U>{Read<U>::get()}\nfn forward<T>(value:T)->T @Read<T>{read(value)}\nfn example(){with {Read<int>::get()->resume 7,Read<str>::get()->resume \"seven\"};assert(forward(0)==7&&forward(\"\")==\"seven\")}",
    );
    let calls = &program.facts().effect_invocations;
    assert!(calls.iter().any(|call| {
        !call.verifying
            && call
                .arguments
                .iter()
                .all(|argument| argument.key.as_ref().is_some_and(ArgumentKey::is_closed))
    }));
    for call in calls {
        assert!(!call.operations.is_empty());
        assert!(call.operations.iter().all(|id| {
            program
                .facts()
                .operations
                .values()
                .any(|operation| operation.identity == *id)
        }));
    }
    assert_eq!(
        program
            .facts()
            .effect_instances
            .iter()
            .filter(|instance| instance.key.is_closed())
            .count(),
        2
    );
}

#[test]
fn full_shapes_keep_lengths_mutability_and_callable_modes() {
    let program = verified(
        "eff Mark<T>{get()->int}\ntype ReadFn<U>=fn(U)->()\ntype WriteFn<U>=fn(mut U)->()\nfn example<T>(){let a=Mark<[2]T>::get;let b=Mark<[3]T>::get;let c=Mark<ReadFn<T>>::get;let d=Mark<WriteFn<T>>::get;let e=Mark<{value:T}>::get;let f=Mark<{mut value:T}>::get}",
    );
    let instances = &program.facts().effect_instances;
    assert_eq!(instances.len(), 6);
    for (index, a) in instances.iter().enumerate() {
        for b in &instances[index + 1..] {
            assert_ne!(a.key, b.key);
        }
    }
}

#[test]
fn a_concrete_resumption_does_not_satisfy_an_arbitrary_type_binder() {
    let outcome = Session::new(
        b"eff Read<T>{get()->T}\nfn wrong<T>()->T{with Read<T>::get()->resume 7;Read<T>::get()}"
            .to_vec(),
    )
    .check();
    assert!(
        matches!(outcome,CompilationOutcome::Rejected {ref diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0624")),
        "{outcome:?}"
    );
}

#[test]
fn owned_ast_cannot_forge_a_real_registered_binder_type() {
    let source =
        "eff Read<T>{get()->T}\nfn read<T>()->T @Read<T>{Read<T>::get()}\nfn forged()->int{0}";
    let good = verified(source);
    let identity = good
        .facts()
        .generic_binders
        .values()
        .find(|binder| binder.name == "T")
        .unwrap()
        .identity
        .clone();
    let mut parsed = ril_syntax::parse(source).program;
    let ril_syntax::ast::StmtKind::Function(function) = &mut parsed.statements[2].kind else {
        panic!()
    };
    let ty = function.return_type.as_mut().unwrap();
    ty.kind = ril_syntax::ast::TypeKind::Name {
        path: vec![format!("\0effect-binder:{identity}")],
        arguments: vec![],
    };
    let outcome = Session::new(vec![]).verify_program(&parsed);
    assert!(
        matches!(outcome,Err(CompilationOutcome::Rejected {ref diagnostics}) if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0101")),
        "{outcome:?}"
    );
}

#[test]
fn aliases_defaults_and_effect_sets_preserve_the_same_lexical_argument() {
    let program = verified(
        "type Boxed<T>=?T\neff Read<T,U=T>{get()->U}\neff App<T>{Read<Boxed<T>>}\nfn read<T>()->?T @App<T>{Read<?T,?T>::get()}",
    );
    let read: Vec<_> = program
        .facts()
        .effect_instances
        .iter()
        .filter(|instance| instance.key.name.ends_with("Read"))
        .collect();
    assert_eq!(read.len(), 1, "{:?}", program.facts().effect_instances);
    assert_eq!(read[0].key.arguments[0], read[0].key.arguments[1]);
    assert!(read[0].sites.len() >= 2);
}

#[test]
fn a_different_rigid_argument_does_not_discharge_an_effect_row() {
    let source = "eff Read<T>{get()->T}\nfn wrong<T,U>()->T @Read<U>{Read<T>::get()}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome,CompilationOutcome::Rejected {ref diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0612")),
        "{outcome:?}"
    );
}

#[test]
fn complete_inferred_arrays_and_unresolved_static_values_keep_distinct_boundaries() {
    let program = verified(
        "eff Read<T>{get()->T}\nfn read<T>(witness:T)->T @Read<T>{Read<T>::get()}\nfn example(){with Read<[]int>::get()->resume [7];let value=read([0])}",
    );
    assert!(
        program
            .facts()
            .effect_invocations
            .iter()
            .filter(|call| !call.verifying)
            .flat_map(|call| &call.arguments)
            .any(|argument| matches!(&argument.key, Some(ArgumentKey::Array { length: None, .. })))
    );
    ril_compiler::lower::lower_core(&program).unwrap();
    let source =
        "eff Counter<n:int>{get()->int}\nfn read<n:int>()->int @Counter<n>{Counter<n>::get()}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::NotImplemented { .. }),
        "{source}: {outcome:?}"
    );
}

#[test]
fn generic_callback_observations_keep_symbolic_and_actual_targets() {
    let program = verified(
        "eff Read<T>{get()->T}\nfn read(witness:int)->int @Read<int>{Read<int>::get()}\nfn run<T>(witness:T,action:fn(T)->T)->T{action(witness)}\nfn example()->int{with Read<int>::get()->resume 7;run(0,read)}",
    );
    let calls = &program.facts().effect_invocations;
    assert!(calls.iter().any(|call| call.verifying
        && !call.unresolved.is_empty()
        && call.callbacks.iter().any(|callback| {
            callback
                .targets
                .iter()
                .any(|target| matches!(target, ril_compiler::sema::model::Callable::Symbolic(..)))
        })));
    assert!(calls.iter().any(|call| !call.verifying
        && !call.operations.is_empty()
        && call.callbacks.iter().any(|callback| {
            !callback.parameter_bindings.is_empty()
                && callback
                    .targets
                    .iter()
                    .any(|target| matches!(target, ril_compiler::sema::model::Callable::Named(_)))
        })));
}
