use ril_compiler::{CompilationOutcome, Session};

fn accepts(source: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{source}: {outcome:?}"
    );
}

fn rejects(source: &str, code: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Rejected { ref diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
        "{source}: {outcome:?}"
    );
}

#[test]
fn assignments_and_mutable_arguments_keep_distinct_target_diagnostics() {
    rejects("fn example(){(1+2)=3}", "E0503");
    rejects(
        "fn take(mut value:int)&mut{}\nfn example(){take(mut (1+2))}",
        "E0410",
    );
    rejects("fn example(){let value=1;value=2}", "E0501");
}

#[test]
fn conditional_result_mismatches_keep_the_branch_diagnostic() {
    rejects(
        "fn example(choose:bool){let value=if choose{1}else{\"a\"}}",
        "E0351",
    );
    rejects("fn example(){let value=if true{1}else{\"a\"}}", "E0351");
    rejects(
        "fn example(choose:bool){let value=if choose{.{id:1}}else{.{name:\"a\"}}}",
        "E0351",
    );
    accepts("fn example(choose:bool){let value:u8=if choose{1}else{2u8}} ");
}

#[test]
fn shift_counts_are_independent_integer_operands() {
    accepts("fn example(){let _=1u8 << -1;let _=1u8 >> 2i16;let _=1bigint << 100}");
    accepts("fn example(){let value:u8=1 << -1;let other:u16=1 >> 2i8}");
    accepts("fn example(){var value=1u8;value<<=-1;value>>=2i16}");
    rejects("fn example(){var value=1u8;value<<=2.0}", "E0327");
    rejects("fn example(){let _=1u8 << 1.0}", "E0327");
    rejects("fn example(){let _=1.0 << 1}", "E0327");
    rejects("fn example(){let _=1u8 + 1u16}", "E0301");
}

#[test]
fn checked_integer_arithmetic_returns_optional_values() {
    accepts(
        "fn example(){assert(10/?0==None&&10%?0==None);assert(-128i8/?-1i8==None);assert(10/?2==Some(5))}",
    );
    rejects("fn example(){let value:int=10/?2}", "E0301");
    accepts("fn example(){let value:?u8=10/?2;assert(value==Some(5u8))}");
    rejects("fn example(){let value:?u8=300/?2}", "E0326");
    rejects(
        "fn example(){let original=10/?2;let value:?u8=original}",
        "E0301",
    );
    rejects("fn example(){let value:?u16=10u8/?2u8}", "E0301");
}

#[test]
fn generic_record_spreads_preserve_the_universal_row_family() {
    let source = "fn with_stamp<R>(item:{..R})->{stamp:int,..R}{.{stamp:7,..item}}\nfn example(){let item=with_stamp(.{id:1,name:\"Ada\"});assert(item.id==1&&item.name==\"Ada\"&&item.stamp==7);let .{id,..rest}=item;assert(id==1&&rest.stamp==7)}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
}

#[test]
fn closed_record_rests_keep_exact_fields_and_child_permissions() {
    accepts("fn example(){let .{..empty}=.{};assert(empty==.{})}");
    accepts(
        "type Item={id:int,name:str,stamp:int}\nfn example(){let item:Item=.{id:1,name:\"Ada\",stamp:7};let .{id,..rest}=item;assert(id==1&&rest.name==\"Ada\"&&rest.stamp==7)}",
    );
    rejects(
        "fn example(){let .{id,..rest}=.{id:1,name:\"Ada\"};let _=rest.id}",
        "E0336",
    );
    rejects(
        "type Cell={mut value:int}\nfn example(){let mut cell=Cell.{value:0};let view observed=cell;let mut source=.{id:1,child:observed};let mut .{id:_,..rest}=^mut source;rest.child.value=2}",
        "E0520",
    );
    rejects(
        "type Cell={mut value:int}\nfn example(){let mut cell=Cell.{value:0};let mut source=.{id:1,child:^mut cell};let .{id:_,..rest}=source}",
        "E0535",
    );
}

#[test]
fn closed_record_rest_lowering_evaluates_the_source_once() {
    let source = "fn source()->{id:int,name:str,stamp:int}{.{id:1,name:\"Ada\",stamp:7}}\nfn example(){let .{id,..rest}=source();assert(id==1&&rest.name==\"Ada\"&&rest.stamp==7)}";
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    let example = core
        .functions
        .iter()
        .find(|function| function.name == "example")
        .unwrap();
    let [
        ril_ir::core::Statement::Bind { value, .. },
        ril_ir::core::Statement::Bind {
            value: projected, ..
        },
        ril_ir::core::Statement::Bind {
            pattern: ril_ir::core::Pattern::Name(rest),
            value: record,
            ..
        },
        ..,
    ] = example.body.statements.as_slice()
    else {
        panic!("{:?}", example.body);
    };
    assert!(matches!(value.kind, ril_ir::core::ExprKind::Call { .. }));
    assert!(matches!(projected.kind, ril_ir::core::ExprKind::Name(_)));
    assert_eq!(rest, "rest");
    let ril_ir::core::ExprKind::Record { fields, .. } = &record.kind else {
        panic!("{record:?}");
    };
    assert_eq!(
        fields
            .iter()
            .map(|(name, _)| name.as_str())
            .collect::<Vec<_>>(),
        ["name", "stamp"]
    );
    assert!(fields.iter().all(|(_, value)| matches!(&value.kind, ril_ir::core::ExprKind::Field { base, .. } if matches!(base.kind, ril_ir::core::ExprKind::Name(_)))));
}

#[test]
fn uppercase_existing_values_are_equality_tests() {
    accepts(
        "fn example(){meta let EXPECTED=2;assert(2 is EXPECTED);assert(Some(2) is Some(EXPECTED))}",
    );
    accepts("meta let EXPECTED=2\nmeta let _=assert(2 is EXPECTED)");
}

#[test]
fn materialized_static_constants_keep_module_binding_capabilities() {
    accepts("meta let ANSWER=42\nfn example()->int &{ANSWER}{ANSWER}");
    rejects("meta let ANSWER=42\nfn example()->int{ANSWER}", "E0510");
}
