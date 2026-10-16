//! Independent Source-only theorem and conservative control-path tests.
use super::*;

fn program(source: &str) -> Program {
    let parsed = ril_syntax::parse(source);
    assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
    parsed.program
}

fn header(program: &Program, name: &str) -> Function {
    program
        .statements
        .iter()
        .find_map(|statement| match &statement.kind {
            StmtKind::Function(function) if function.name == name => Some(function.clone()),
            _ => None,
        })
        .unwrap()
}

fn span_of(source: &str, text: &str) -> Span {
    let start = source.find(text).unwrap();
    Span {
        file: ril_compiler_core::source::FileId(0),
        start: start as u32,
        end: (start + text.len()) as u32,
    }
}

fn proof(source: &str, predicate: &str) -> Option<ResultSource> {
    let program = program(source);
    result_source(
        &program,
        &header(&program, "example"),
        &[],
        span_of(source, predicate),
        &mut 65_536,
    )
    .unwrap()
}

#[test]
fn real_formal_and_some_pattern_supply_a_source_path() {
    let source = "fn example(other:Option<Result<int,str>>){match other{Some(inner)->assert(inner is Ok(_)|Err(_)),None->()}}";
    let proof = proof(source, "inner is Ok(_)|Err(_)").unwrap();
    assert_eq!(proof.root.parameter, 0);
    assert_eq!(proof.steps.len(), 1);
    assert!(matches!(proof.steps[0], SourceStep::OptionPayload { .. }));
}

#[test]
fn unchanged_e508_formal_capture_is_grounded_but_receive_call_is_not_inferred() {
    let source = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-optional-callback-scope-budget",
    );
    let program = program(source);
    let header = header(&program, "consume");
    let StmtKind::Expr { expression, .. } = &header.body.as_ref().unwrap().statements[0].kind
    else {
        panic!()
    };
    let ExprKind::Call { arguments, .. } = &expression.kind else {
        panic!()
    };
    let lambda = arguments[0].value.span;
    assert!(matches!(arguments[0].value.kind, ExprKind::Lambda { .. }));
    let first = span_of(source, "inner is Ok(_)|Err(_)");
    let proof = result_source(&program, &header, &[lambda], first, &mut 65_536)
        .unwrap()
        .unwrap();
    assert_eq!(proof.root.parameter, 1);
    assert!(
        matches!(&proof.steps[0], SourceStep::Capture { lambda: actual, name } if *actual == lambda && name == "other")
    );
    assert!(matches!(proof.steps[1], SourceStep::OptionPayload { .. }));
    assert!(
        result_source(&program, &header, &[], first, &mut 65_536)
            .unwrap()
            .is_none()
    );
    let second_start = source[first.end as usize..]
        .find("inner is Ok(_)|Err(_)")
        .unwrap()
        + first.end as usize;
    let second = Span {
        start: second_start as u32,
        end: (second_start + "inner is Ok(_)|Err(_)".len()) as u32,
        ..first
    };
    assert!(
        result_source(&program, &header, &[lambda], second, &mut 65_536)
            .unwrap()
            .is_none()
    );
}

#[test]
fn constructor_spelling_and_recorded_unknown_type_cannot_supply_theorem() {
    for source in [
        "type Result{Ok(int),Err(str)}\nfn example(value:Result){assert(value is Ok(_)|Err(_))}",
        "type Option{Some(int),None}\nfn example(value:Option){match value{Some(inner)->assert(inner is Ok(_)|Err(_)),None->()}}",
        "fn example(value:int){assert(value is Ok(_)|Err(_))}",
        "type Impostor{Ok(int),Err(str)}\nfn example(value:Prelude::Result<int,str>){assert(value is Ok(_)|Err(_))}",
    ] {
        let predicate = if source.contains("inner is") {
            "inner is Ok(_)|Err(_)"
        } else {
            "value is Ok(_)|Err(_)"
        };
        assert!(proof(source, predicate).is_none(), "{source}");
    }
}

#[test]
fn qualified_canonical_constructors_respect_expected_source_type() {
    let source = "type Impostor{Ok(int),Err(str)}\nfn example(value:Prelude::Result<int,str>){assert(value is Prelude::Ok(_)|Prelude::Err(_))}";
    assert!(proof(source, "value is Prelude::Ok(_)|Prelude::Err(_)").is_some());
    let source = "type Result{Ok(int),Err(str)}\nfn example(value:Result){assert(value is Prelude::Ok(_)|Prelude::Err(_))}";
    assert!(proof(source, "value is Prelude::Ok(_)|Prelude::Err(_)").is_none());
}

#[test]
fn non_exhaustive_duplicate_and_payload_tests_remain_unknown() {
    for predicate in [
        "value is Ok(_)",
        "value is Ok(_)|Ok(_)",
        "value is Ok(1)|Err(_)",
        "value is Ok()|Err(_)",
    ] {
        let source = format!("fn example(value:Result<int,str>){{assert({predicate})}}");
        assert!(proof(&source, predicate).is_none(), "{source}");
    }
}

#[test]
fn immutable_alias_preserves_root_but_annotations_and_reassignment_do_not_invent_it() {
    let source = "fn example(value:Result<int,str>){let alias=value;assert(alias is Ok(_)|Err(_))}";
    let result = proof(source, "alias is Ok(_)|Err(_)").unwrap();
    assert_eq!(result.root.parameter, 0);
    assert!(matches!(result.steps[0], SourceStep::Alias { .. }));
    for source in [
        "fn example(value:int){let alias:Result<int,str>=value;assert(alias is Ok(_)|Err(_))}",
        "fn example(value:Result<int,str>){var alias=value;alias=Ok(1);assert(alias is Ok(_)|Err(_))}",
    ] {
        assert!(proof(source, "alias is Ok(_)|Err(_)").is_none());
    }
}

#[test]
fn where_and_generic_type_shadows_are_not_prelude_types() {
    let source = "fn example<Result>(value:Result<int,str>){assert(value is Ok(_)|Err(_))}";
    assert!(proof(source, "value is Ok(_)|Err(_)").is_none());
    let source = "fn example(value:Result<int,str>){assert(value is Ok(_)|Err(_)) where type Result{Ok(int),Err(str)}}";
    assert!(proof(source, "value is Ok(_)|Err(_)").is_none());
}

#[test]
fn a_real_lexical_value_name_shadows_an_unqualified_constructor() {
    // Uppercase bare parameters parse as constructor patterns. Exercise the
    // actual Name AST branch explicitly, instead of pretending such a pattern
    // declared a value binder. This is an AST adversarial control, not a valid
    // source-language acceptance claim.
    let source = "fn example(value:Result<int,str>,shadow:int){assert(value is Ok(_)|Err(_))}";
    let mut program = program(source);
    let StmtKind::Function(header) = &mut program.statements[0].kind else {
        panic!()
    };
    header.parameters[1].pattern.kind = PatternKind::Name("Ok".into());
    let header = header.clone();
    assert!(
        result_source(
            &program,
            &header,
            &[],
            span_of(source, "value is Ok(_)|Err(_)"),
            &mut 65_536
        )
        .unwrap()
        .is_none()
    );
}

#[test]
fn duplicate_and_mismatching_headers_and_exhausted_work_fail_closed() {
    let source = "fn example(value:Result<int,str>){assert(value is Ok(_)|Err(_))}";
    let original = program(source);
    let header = header(&original, "example");
    let condition = span_of(source, "value is Ok(_)|Err(_)");
    let mut duplicate = original.clone();
    duplicate.statements.push(duplicate.statements[0].clone());
    assert!(result_source(&duplicate, &header, &[], condition, &mut 65_536).is_err());
    let mut changed = header.clone();
    changed.name = "borrowed_header".into();
    assert!(result_source(&original, &changed, &[], condition, &mut 65_536).is_err());
    assert!(result_source(&original, &header, &[], condition, &mut 0).is_err());
}

#[test]
fn all_reconstruction_and_clone_work_uses_one_exact_remaining_budget() {
    let source = "fn example(other:Option<Result<int,str>>){let copy=other;match copy{Some(inner)->assert(inner is Ok(_)|Err(_)),None->()}}";
    let program = program(source);
    let header = header(&program, "example");
    let condition = span_of(source, "inner is Ok(_)|Err(_)");
    let mut remaining = 65_536;
    assert!(
        result_source(&program, &header, &[], condition, &mut remaining)
            .unwrap()
            .is_some()
    );
    let consumed = 65_536 - remaining;
    let mut exact = consumed;
    assert!(
        result_source(&program, &header, &[], condition, &mut exact)
            .unwrap()
            .is_some()
    );
    assert_eq!(exact, 0);
    assert!(result_source(&program, &header, &[], condition, &mut (consumed - 1)).is_err());
}

#[test]
fn complete_global_source_view_detects_a_value_shadow_without_type_registry() {
    // Adversarial Source AST control: the global binder itself is the shadow.
    // There is deliberately no producer-owned nominal type registry.
    let source = "let SHADOW=1\nfn example(value:Result<int,str>){assert(value is Ok(_)|Err(_))}";
    let mut program = program(source);
    let header = header(&program, "example");
    let StmtKind::Binding(binding) = &mut program.statements[0].kind else {
        panic!()
    };
    binding.pattern.kind = PatternKind::Name("Result".into());
    assert!(
        result_source(
            &program,
            &header,
            &[],
            span_of(source, "value is Ok(_)|Err(_)"),
            &mut 65_536
        )
        .unwrap()
        .is_none()
    );
}

#[test]
fn nested_some_and_literal_siblings_do_not_supply_an_execution_path() {
    for source in [
        "fn example(other:Option<Option<Result<int,str>>>){match other{Some(Some(inner))->assert(inner is Ok(_)|Err(_)),_->()}}",
        "fn example(other:Option<(int,Result<int,str>)>){match other{Some((1,inner))->assert(inner is Ok(_)|Err(_)),_->()}}",
    ] {
        assert!(proof(source, "inner is Ok(_)|Err(_)").is_none());
    }
}

#[test]
fn nontrivial_prefixes_remain_explicitly_unproved() {
    for prefix in [
        "maybe_abort(flag);",
        "let ignored=maybe_abort(flag);",
        "var ignored=0;ignored=maybe_abort(flag);",
    ] {
        let source = format!(
            "fn example(flag:bool,value:Result<int,str>){{{prefix}assert(value is Ok(_)|Err(_))}}"
        );
        let result = proof(&source, "value is Ok(_)|Err(_)").unwrap();
        assert!(
            result
                .controls
                .iter()
                .any(|control| matches!(control, SourceControl::UnprovedPrefix)),
            "{source}"
        );
    }
}

#[test]
fn canonical_scope_resolution_does_not_borrow_a_computed_callee() {
    let source = "fn example(value:Result<int,str>){Concurrent::scope \\mut s->{assert(value is Ok(_)|Err(_));Ok()}}";
    let program = program(source);
    let header = header(&program, "example");
    let StmtKind::Expr { expression, .. } = &header.body.as_ref().unwrap().statements[0].kind
    else {
        panic!()
    };
    let ExprKind::Call { callee, .. } = &expression.kind else {
        panic!()
    };
    assert!(canonical_scope_callee(&program, &header, callee, &mut 65_536).unwrap());
    for computed in ["choose_scope(flag)", "scope_alias"] {
        let expression = ril_syntax::parse_expression(computed, callee.span.file).expression;
        assert!(!canonical_scope_callee(&program, &header, &expression, &mut 65_536).unwrap());
    }
}

#[test]
fn earlier_callee_and_sibling_abort_paths_remain_unproved() {
    for body in [
        "(may_abort(flag),value is Ok(_)|Err(_))",
        "consume(may_abort(flag),value is Ok(_)|Err(_))",
        "choose_consumer(flag)(value is Ok(_)|Err(_))",
        "[may_abort(flag),value is Ok(_)|Err(_)]",
    ] {
        let source = format!("fn example(flag:bool,value:Result<int,str>){{{body}}}");
        let result = proof(&source, "value is Ok(_)|Err(_)").unwrap();
        assert!(
            result
                .controls
                .iter()
                .any(|control| matches!(control, SourceControl::UnprovedPrefix)),
            "{source}"
        );
    }
}

#[test]
fn later_some_arms_cannot_borrow_the_first_arms_execution() {
    for first in ["Some(_)->()", "Some(1)->()", "_->()"] {
        let source = format!(
            "fn example(value:Option<Result<int,str>>){{match value{{{first},Some(inner)->assert(inner is Ok(_)|Err(_)),None->()}}}}"
        );
        assert!(proof(&source, "inner is Ok(_)|Err(_)").is_none());
    }
    for source in [
        "fn example(flag:bool,other:Option<Result<int,str>>){match other{Some(_) if flag->(),Some(inner)->assert(inner is Ok(_)|Err(_)),None->()}}",
        "fn example(other:Option<Result<int,str>>){match other{Some(Err(_))->(),Some(inner)->assert(inner is Ok(_)|Err(_)),None->()}}",
    ] {
        assert!(proof(source, "inner is Ok(_)|Err(_)").is_none());
    }
}
