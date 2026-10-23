use ril_compiler::{CompilationOutcome, Session};
use ril_compiler_core::source::Span;
use ril_syntax::ast::{Expr, ExprKind, Program, StmtKind};

fn collide_copy_uses(program: &mut Program) {
    fn expression(expr: &mut Expr, shared: Span) {
        let copy_name = |expr: &Expr| {
            matches!(&expr.kind,
            ExprKind::Name(name) if name == "duplicate" || name == "alias")
        };
        if copy_name(expr) {
            expr.span = shared;
        }
        match &mut expr.kind {
            ExprKind::Call { callee, arguments } => {
                if copy_name(callee) {
                    expr.span = shared;
                }
                expression(callee, shared);
                for argument in arguments {
                    expression(&mut argument.value, shared);
                }
            }
            ExprKind::Binary { left, right, .. } => {
                expression(left, shared);
                expression(right, shared);
            }
            ExprKind::Generic { base, .. } => expression(base, shared),
            ExprKind::Name(_) | ExprKind::Literal(_) => {}
            other => panic!("extend the adversarial fixture visitor: {other:?}"),
        }
    }
    let shared = program.statements[0].span;
    for statement in &mut program.statements {
        let StmtKind::Function(function) = &mut statement.kind else {
            panic!()
        };
        for statement in &mut function.body.as_mut().unwrap().statements {
            match &mut statement.kind {
                StmtKind::Binding(binding) => expression(&mut binding.value, shared),
                StmtKind::Expr {
                    expression: value, ..
                } => expression(value, shared),
                other => panic!("extend the adversarial fixture visitor: {other:?}"),
            }
        }
    }
}

#[test]
fn same_span_direct_and_indirect_evaluations_have_separate_consumed_events() {
    let source = "fn duplicate(source:int)->int{source}\nfn example(){assert(duplicate(1)==1);let alias=duplicate;assert(alias(2)==2)}";
    let mut syntax = ril_syntax::parse(source).program;
    collide_copy_uses(&mut syntax);
    let verified = Session::new(vec![]).verify_program(&syntax).unwrap();
    let facts = verified.facts();
    let target = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "duplicate")
        .unwrap()
        .definition;
    let calls: Vec<_> = facts
        .copy_invocations
        .iter()
        .filter(|call| call.target == target && !call.declaration_probe)
        .collect();
    assert_eq!(calls.len(), 2);
    assert_eq!(calls[0].span, calls[1].span);
    assert!(calls[0].direct);
    assert!(!calls[1].direct);
    assert_ne!(calls[0].source_event, calls[1].source_event);
    let references: Vec<_> = facts
        .copy_references
        .iter()
        .filter(|reference| reference.target == target)
        .collect();
    assert_eq!(references.len(), 3);
    assert!(
        references
            .iter()
            .all(|reference| reference.span == references[0].span)
    );
    assert_eq!(
        references
            .iter()
            .filter(|reference| reference.direct_call.is_some())
            .count(),
        1
    );
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert_eq!(
        core.provenance.copy_references.len(),
        facts.copy_references.len()
    );
    assert_eq!(
        core.provenance.copy_call_events.len(),
        facts.copy_call_events.len()
    );
}

#[test]
fn extracted_template_cannot_borrow_a_direct_use_at_the_same_diagnostic_span() {
    for tail in [
        "let alias=duplicate",
        "let alias=duplicate;let other=alias(one);assert(other()==1)",
    ] {
        let source = format!(
            "fn duplicate(source:fn()->int)->fn()->int{{clone(source)}}\nfn one()->int{{1}}\nfn example(){{let copied=duplicate(one);assert(copied()==1);{tail}}}"
        );
        let mut syntax = ril_syntax::parse(&source).program;
        collide_copy_uses(&mut syntax);
        let outcome = Session::new(vec![]).verify_program(&syntax);
        assert!(
            matches!(&outcome, Err(CompilationOutcome::NotImplemented { .. })),
            "{outcome:?}"
        );
    }
}

#[test]
fn repeated_source_defaults_keep_their_own_call_event_and_actual_instance() {
    let source = "fn duplicate<T>(source:T)->T{clone(source)}\nfn read(value:int=duplicate(7))->int{value}\nfn example(){assert(read()==7);assert(read()==7)}";
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = verified.facts();
    let target = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "duplicate")
        .unwrap()
        .definition;
    let calls: Vec<_> = facts
        .copy_invocations
        .iter()
        .filter(|call| call.target == target && !call.declaration_probe)
        .collect();
    assert!(calls.len() >= 2);
    assert!(
        calls
            .iter()
            .all(|call| call.span == calls[0].span && call.direct)
    );
    let events: std::collections::BTreeSet<_> = calls
        .iter()
        .map(|call| call.source_event.unwrap())
        .collect();
    assert_eq!(events.len(), calls.len());
    ril_compiler::sema::copy_template_closure::validate(facts).unwrap();
}

#[test]
fn final_validation_rejects_missing_or_reused_call_event_evidence() {
    use ril_compiler::sema::copy_template_closure::validate;
    let source = "fn duplicate<T>(source:T)->T{clone(source)}\nfn read(value:int=duplicate(7))->int{value}\nfn example(){assert(read()==7);assert(read()==7)}";
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = verified.facts();
    let target = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "duplicate")
        .unwrap()
        .definition;
    let calls: Vec<_> = facts
        .copy_invocations
        .iter()
        .filter(|call| call.target == target && !call.declaration_probe)
        .map(|call| call.id)
        .collect();
    let mut reused = facts.clone();
    reused.copy_invocations[calls[1].0 as usize].source_event =
        reused.copy_invocations[calls[0].0 as usize].source_event;
    assert!(validate(&reused).is_err());
    let mut missing = facts.clone();
    missing.copy_references.pop();
    assert!(validate(&missing).is_err());
    let mut extracted = facts.clone();
    let reference = extracted
        .copy_references
        .iter_mut()
        .find(|reference| reference.target == target)
        .unwrap();
    reference.direct_call = None;
    assert!(validate(&extracted).is_err());
}

#[test]
fn equal_span_tokens_cannot_be_swapped_between_dynamic_parent_instances() {
    use ril_compiler::sema::{copy_template_closure::validate, model::Ty};
    let source = "fn duplicate<T>(source:T)->T{clone(source)}\nfn forward<T>(source:T)->T{duplicate(source)}\nfn example(){assert(forward(1)==1);assert(forward(\"two\")==\"two\")}";
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = verified.facts();
    let target = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "duplicate")
        .unwrap()
        .definition;
    let calls: Vec<_> = facts
        .copy_invocations
        .iter()
        .filter(|call| {
            call.target == target
                && !call.declaration_probe
                && matches!(call.entry.arguments[0].value().ty, Ty::Int(_) | Ty::Str)
        })
        .collect();
    assert_eq!(calls.len(), 2);
    assert_eq!(calls[0].span, calls[1].span);
    assert_eq!(calls[0].caller_owner, calls[1].caller_owner);
    assert_ne!(calls[0].parent, calls[1].parent);
    let mut exchanged = facts.clone();
    exchanged.copy_invocations[calls[0].id.0 as usize].source_event = calls[1].source_event;
    exchanged.copy_invocations[calls[1].id.0 as usize].source_event = calls[0].source_event;
    assert!(
        validate(&exchanged)
            .unwrap_err()
            .contains("borrowed another syntax event")
    );
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    for call in calls {
        let event = &core.provenance.copy_call_events[call.source_event.unwrap().0 as usize];
        assert_eq!(event.parent.unwrap().0, call.parent.unwrap().0);
    }
}

#[test]
fn handler_lexical_owner_and_dynamic_named_parent_remain_independent() {
    use ril_compiler_core::ids::CallableOwner;
    let source = "eff Read{get()->int}\nfn duplicate<T>(source:T)->T{clone(source)}\nfn request()->int @Read{Read::get()}\nfn example(){with Read::get()->resume duplicate(7);assert(request()==7)}";
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = verified.facts();
    let target = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "duplicate")
        .unwrap()
        .definition;
    let request = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "request")
        .unwrap()
        .definition;
    let lexical = facts
        .functions
        .iter()
        .find(|function| function.syntax.name == "example")
        .unwrap()
        .definition;
    let call = facts
        .copy_invocations
        .iter()
        .find(|call| {
            call.target == target
                && !call.declaration_probe
                && call.parent.is_some_and(|parent| {
                    facts.copy_invocations[parent.0 as usize].target == request
                })
        })
        .unwrap();
    let event = &facts.copy_call_events[call.source_event.unwrap().0 as usize];
    assert_eq!(event.owner, Some(CallableOwner::Function(lexical)));
    assert_eq!(event.parent, call.parent);
    ril_compiler::sema::copy_template_closure::validate(facts).unwrap();
}
