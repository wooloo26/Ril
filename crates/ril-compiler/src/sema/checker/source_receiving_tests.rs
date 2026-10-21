//! Focused checks for original-source receiving. These do not replace the
//! complete Session/Source gate at the real binding/return/member hooks.
use super::*;
use crate::sema::source_reception::Construction;

#[test]
fn a_registered_generic_requires_its_actual_source_observation() {
    let parsed = ril_syntax::parse(
        "fn owner<U>(value:U)->U{value}\nfn other<V>(other:V){}\nfn keys<T,K:keyof T>(record:T,key:K){}",
    );
    assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
    let mut checker = Checker::new(FileId(0));
    checker.run(&parsed.program);
    let owner = checker
        .functions
        .iter()
        .position(|function| function.syntax.name == "owner")
        .unwrap();
    let function = checker.functions[owner].clone();
    let StmtKind::Expr { expression, .. } =
        &function.syntax.body.as_ref().unwrap().statements[0].kind
    else {
        panic!("the owner returns its actual formal")
    };
    assert!(expression.hir_id.is_some());
    let (observation, original) = checker
        .application_effect
        .expressions
        .iter()
        .enumerate()
        .find(|(_, fact)| {
            fact.source_id == expression.hir_id && matches!(fact.value.ty, Ty::Generic(_))
        })
        .unwrap();
    let actual = original.value.clone();
    let context = checker.application_effect.evaluations[observation].context;
    assert_eq!(actual.sources.len(), 1);
    let binding = *actual.sources.first().unwrap();
    let (declaration, environment) = checker
        .parameter_source_schema(binding, None)
        .expect("a written generic formal retains its complete Binder graph at birth");
    assert_eq!(
        environment.id(),
        checker.bindings[binding].typing_environment.id()
    );
    assert!(matches!(declaration.key().unwrap(),
        crate::sema::effect_identity::ArgumentKey::Binder { identity, .. }
            if matches!(&actual.ty, Ty::Generic(actual) if actual == &identity)));
    checker.generic_scope(owner);
    let mut frame = checker.frame(Env::from([("value".into(), binding)]), false);
    frame.owner = checker.bindings[binding].owner;
    frame.definition = Some(function.definition);
    frame.callable_owner = Some(CallableOwner::Function(function.definition));
    assert_eq!(context.owner, frame.callable_owner);
    let invocation = context.invocation.expect("the original named reception");
    checker.copy_invocation_stack.push(invocation);
    assert!(
        checker
            .original_source_receiving_key(&actual, expression, &frame)
            .is_some(),
        "the original formal and its real HIR observation must supply Source"
    );
    for (name, index) in [("owner", 0), ("other", 0), ("keys", 1)] {
        let definition = checker
            .functions
            .iter()
            .find(|function| function.syntax.name == name)
            .unwrap()
            .definition;
        let identity = checker
            .generic_binders
            .values()
            .find(|binder| binder.definition == definition && binder.index == index)
            .unwrap()
            .identity
            .clone();
        // Retain the real HIR expression and cause. Only the Source receipt is
        // absent, so a missing HIR ID cannot make this negative test vacuous.
        let counterfeit = Value::scalar(Ty::Generic(identity), None, actual.cause);
        assert!(
            checker
                .original_source_receiving_key(&counterfeit, expression, &frame)
                .is_none(),
            "registered {name}:{index} without Source minted a Type identity"
        );
    }
    assert_eq!(checker.copy_invocation_stack.pop(), Some(invocation));
}

fn expression(source: &str) -> Expr {
    let parsed = ril_syntax::parse_expression(source, FileId(0));
    assert!(parsed.diagnostics.is_empty() && !parsed.incomplete);
    parsed.expression
}

fn annotation(source: &str) -> TypeExpr {
    let parsed = ril_syntax::parse(&format!("let SOURCE:{source}=[]"));
    assert!(parsed.is_ok(), "{source}: {:?}", parsed.diagnostics);
    let StmtKind::Binding(binding) = &parsed.program.statements[0].kind else {
        panic!("binding fixture");
    };
    binding.ty.clone().unwrap()
}

fn declaration(source: &str) -> TypeDeclaration {
    let parsed = ril_syntax::parse(source);
    assert!(parsed.is_ok(), "{source}: {:?}", parsed.diagnostics);
    let StmtKind::Type(declaration) = &parsed.program.statements[0].kind else {
        panic!("type fixture");
    };
    declaration.clone()
}

fn stored_array(checker: &mut Checker, frame: &mut Frame, schema: &str) -> (Expr, Value, usize) {
    let syntax = annotation(schema);
    let ty = checker.ty(&syntax);
    let literal = expression("[]");
    let mut value = checker
        .expression_expected_observed(&literal, frame, Some(&ty))
        .0;
    value.ty = ty;
    checker.ascribe_source_type(&mut value, &syntax);
    checker.bind_name(
        "stored",
        BindingMode::Let,
        value,
        literal.span,
        frame,
        false,
    );
    let actual = expression("stored");
    let (value, index) = checker.expression_observed(&actual, frame);
    (actual, value, index.unwrap())
}

#[test]
fn a_stored_empty_outer_array_keeps_its_inner_source_dimension() {
    let mut checker = Checker::new(FileId(0));
    let mut frame = checker.frame(Env::new(), false);
    let (actual, value, index) = stored_array(&mut checker, &mut frame, "[0][3]int");
    let target = checker.freeze_source_receiving_target(&annotation("[0][2]int"));
    assert!(!checker.require_source_reception(&target, &actual, &value, Some(index), &frame));
    assert!(
        checker
            .diagnostics
            .iter()
            .any(|error| error.code == "E0301")
    );
    assert!(checker.unsupported.is_empty());
}

#[test]
fn name_cannot_reopen_a_literal_via_cause_construction_or_backing_length() {
    let mut checker = Checker::new(FileId(0));
    let mut frame = checker.frame(Env::new(), false);
    let (actual, mut value, index) = stored_array(&mut checker, &mut frame, "[0][3]int");
    // These do not change the actual Name AST or its frozen schema. No cause
    // traversal or construction flag may discharge the inner [3] versus [2].
    value.construction = true;
    for node in &value.origins.nodes {
        checker.array_lengths.insert(*node, Some(0));
    }
    let target = checker.freeze_source_receiving_target(&annotation("[0][2]int"));
    assert!(!checker.require_source_reception(&target, &actual, &value, Some(index), &frame));
    assert!(
        checker
            .diagnostics
            .iter()
            .any(|error| error.code == "E0301")
    );
}

#[test]
fn missing_or_wrong_context_observation_cannot_supply_receiving_context() {
    let mut checker = Checker::new(FileId(0));
    let mut frame = checker.frame(Env::new(), false);
    let (actual, value, index) = stored_array(&mut checker, &mut frame, "[0][2]int");
    let target = checker.freeze_source_receiving_target(&annotation("[0][2]int"));
    assert!(!checker.require_source_reception(&target, &actual, &value, None, &frame));
    checker.application_effect.contexts[index]
        .context
        .budget_validation = true;
    assert!(!checker.require_source_reception(&target, &actual, &value, Some(index), &frame));
    assert!(checker.diagnostics.is_empty());
    assert_eq!(checker.unsupported.len(), 1);
}

#[test]
fn overwriting_the_current_descriptor_does_not_rewrite_the_original_observation() {
    let mut checker = Checker::new(FileId(0));
    let mut frame = checker.frame(Env::new(), false);
    let (actual, mut value, index) = stored_array(&mut checker, &mut frame, "[0][3]int");
    let destination = annotation("[0][2]int");
    let target = checker.freeze_source_receiving_target(&destination);
    checker.ascribe_source_type(&mut value, &destination);
    assert!(!checker.require_source_reception(&target, &actual, &value, Some(index), &frame));
    assert!(checker.diagnostics.is_empty());
    assert_eq!(checker.unsupported.len(), 1);
}

#[test]
fn actual_empty_literal_can_receive_a_complete_zero_outer_array_schema() {
    let mut checker = Checker::new(FileId(0));
    let mut frame = checker.frame(Env::new(), false);
    let target = checker.freeze_source_receiving_target(&annotation("[0][2]int"));
    let actual = expression("[]");
    let (value, index) = checker.expression_observed(&actual, &mut frame);
    assert!(checker.require_source_reception(&target, &actual, &value, index, &frame));
    assert!(checker.unsupported.is_empty());
    assert!(checker.diagnostics.is_empty());
}

#[test]
fn annotation_alias_is_frozen_before_later_shadowing() {
    let mut checker = Checker::new(FileId(0));
    checker
        .types
        .insert("Items".into(), declaration("type Items=[2]int"));
    let annotation = annotation("Items");
    let before = checker.freeze_source_receiving_target(&annotation);
    checker
        .types
        .insert("Items".into(), declaration("type Items=[3]int"));
    let after = checker.freeze_source_receiving_target(&annotation);
    assert!(
        matches!(&before.key(), Some(ArgumentKey::Array { length: Some(n), .. }) if n=="const(int:2)")
    );
    assert!(
        matches!(&after.key(), Some(ArgumentKey::Array { length: Some(n), .. }) if n=="const(int:3)")
    );
    assert_ne!(before.key(), after.key());
    assert!(before.syntax.is_some() && after.syntax.is_some());
}

#[test]
fn symbolic_structure_keeps_genuine_uid_but_not_an_unexpanded_alias() {
    let token = "\0effect-binder:caller:T";
    let binders = BTreeMap::from([(token.into(), "function:7:generic:0".into())]);
    let mut syntax = annotation("[2]int");
    let TypeKind::Array { element, .. } = &mut syntax.kind else {
        unreachable!()
    };
    element.kind = TypeKind::Name {
        path: vec![token.into()],
        arguments: vec![],
    };
    assert!(resolved_symbolic_names(&syntax, &binders, &BTreeMap::new(), &mut 4096, 0).is_some());
    let key = crate::static_eval::effects::bounded_argument_key(&syntax, &binders).unwrap();
    assert!(
        matches!(key, ArgumentKey::Array { element, .. } if matches!(*element, ArgumentKey::Binder { ref identity, .. } if identity=="function:7:generic:0"))
    );
    let declaration = declaration("type Hidden<T:Type>=[2]T");
    let mut alias = annotation("Hidden<int>");
    let TypeKind::Name { arguments, .. } = &mut alias.kind else {
        unreachable!()
    };
    arguments[0].kind = TypeKind::Name {
        path: vec![token.into()],
        arguments: vec![],
    };
    assert!(
        resolved_symbolic_names(
            &alias,
            &binders,
            &BTreeMap::from([("Hidden".into(), declaration)]),
            &mut 4096,
            0
        )
        .is_none()
    );
}

#[test]
fn frozen_member_source_and_typed_record_opacity_are_independent() {
    let mut checker = Checker::new(FileId(0));
    let record = checker.freeze_source_receiving_target(&annotation("{item:[0][2]int}"));
    let member = member_target(&record, "item", record.span);
    assert!(
        matches!(&member.key(), Some(ArgumentKey::Array { length:Some(n), .. }) if n=="const(int:0)")
    );
    assert!(matches!(
        &member.syntax.as_ref().unwrap().kind,
        TypeKind::Array { .. }
    ));
    let actual = expression("Holder.{item:[]}");
    assert!(matches!(
        source_reception::construction(&actual, &mut 4096),
        Some(Construction::Opaque)
    ));
    let absent = member_target(&record, "absent", record.span);
    assert!(absent.key().is_none() && absent.syntax.is_none());
}

#[test]
fn fresh_empty_recursive_scalar_array_has_only_a_proved_construction_context() {
    let mut checker = Checker::new(FileId(0));
    checker.types.insert(
        "Node".into(),
        declaration("type Node={mut value:int,mut following:?Node}"),
    );
    let target = checker.freeze_source_receiving_target(&annotation("[]Node"));
    assert!(
        target.key().is_none(),
        "a finite absence proof is not a complete Source schema"
    );
    assert!(target.empty_array_context.is_some());
    let mut frame = checker.frame(Env::new(), false);
    let actual = expression("[]");
    let (value, observed) = checker.expression_observed(&actual, &mut frame);
    assert!(checker.require_source_reception(&target, &actual, &value, observed, &frame));
    checker.bind_name(
        "stored",
        BindingMode::Let,
        value,
        actual.span,
        &mut frame,
        false,
    );
    let stored = expression("stored");
    let (value, observed) = checker.expression_observed(&stored, &mut frame);
    assert!(!checker.require_source_reception(&target, &stored, &value, observed, &frame));
    checker.types.insert(
        "Node".into(),
        declaration("type Node={following:?Node,callback:fn()->int}"),
    );
    let target = checker.freeze_source_receiving_target(&annotation("[]Node"));
    assert!(target.empty_array_context.is_none());
}

#[test]
fn qualified_callable_targets_share_canonical_data_schemas_without_losing_rows() {
    let mut checker = Checker::new(FileId(0));
    let header = "fn(mut File::Handle,int)->Result<Io::ReadChunk,Io::IoError>@Fiber&mut";
    checker.types.insert(
        "Reader".into(),
        declaration(&format!("type Reader={header}")),
    );
    let written = checker.freeze_source_receiving_target(&annotation(header));
    let alias = checker.freeze_source_receiving_target(&annotation("Reader"));
    let original = builtin_source_types::contract("File::read_chunk", written.span).unwrap();
    let normalized = super::super::source_types::expand_builtin_source_syntax(
        &BTreeMap::new(),
        original.source.syntax().unwrap(),
        0,
    )
    .unwrap();
    let original_key =
        crate::static_eval::effects::bounded_argument_key(&normalized, &BTreeMap::new()).unwrap();
    for target in [&written, &alias] {
        let target_key = target.key();
        let expected = target_key
            .as_ref()
            .expect("complete qualified source target");
        assert_eq!(
            source_reception::compatible(expected, &original_key, None, &mut 4096),
            Some(true),
            "{expected:?}\n{original_key:?}"
        );
        let TypeKind::Callable {
            annotations,
            result,
            ..
        } = &target.syntax.as_ref().unwrap().kind
        else {
            panic!("the original alias must expose its actual full Fn declaration");
        };
        assert_eq!(
            annotations
                .iter()
                .map(|annotation| annotation.text.as_str())
                .collect::<Vec<_>>(),
            ["@Fiber", "&mut"]
        );
        let TypeKind::Name { arguments, .. } = &result.as_ref().unwrap().kind else {
            panic!("genuine Result header");
        };
        assert!(matches!(arguments[0].kind, TypeKind::Record { .. }));
    }
    assert_eq!(written.key(), alias.key());
}

#[test]
fn a_qualified_alias_does_not_reinterpret_a_captured_or_recursive_source() {
    let mut checker = Checker::new(FileId(0));
    checker.types.insert(
        "Captured".into(),
        declaration("type Captured=fn()->T@Fiber"),
    );
    checker
        .type_source
        .environment
        .generic_context
        .insert("T".into(), "unproved-original-T".into());
    assert!(
        checker
            .freeze_source_receiving_target(&annotation("Captured"))
            .key()
            .is_none()
    );
    checker.type_source.environment.generic_context.clear();
    checker
        .types
        .insert("Cycle".into(), declaration("type Cycle={following:?Cycle}"));
    let target = checker.freeze_source_receiving_target(&annotation("fn()->Cycle@Fiber"));
    assert!(target.key().is_none());
    assert_eq!(target.sensitivity, SchemaSensitivity::Required);
}
