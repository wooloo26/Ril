//! Independent source audit of the static invocation trampoline.
use ril_compiler::{CompilationOutcome, Session};

fn accepts(source: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Accepted { .. }),
        "{source}\n{outcome:?}"
    );
}
fn rejects(source: &str, code: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics}if diagnostics.iter().any(|diagnostic|diagnostic.code==code)),
        "{source}\n{outcome:?}"
    );
}

#[test]
fn long_tail_chains_and_nested_callable_returns_keep_their_actual_values() {
    accepts(
        "meta fn count(n:int,total:int)->int{if n==0{total}else{count(n-1,total+1)}}\nmeta let _=assert(count(200,0)==200)",
    );
    accepts(
        "meta fn outer()->int{let inner=(\\->{return 7})();inner+1}\nmeta let _=assert(outer()==8)",
    );
    accepts(
        "meta fn pair(a:int,b:int)->int{a+b}\nmeta fn outer()->int{pair({return 7},1);99}\nmeta let _=assert(outer()==7)",
    );
}

#[test]
fn tail_callee_return_shapes_do_not_erase_the_callers_contract() {
    accepts(
        "meta fn fixed()->[2]int{[1,2]}\nmeta fn request()->[2]int{fixed()}\nmeta let VALUE=request()\nmeta let _=assert(len(VALUE)==2)",
    );
    rejects(
        "meta fn fixed()->[2]int{[1,2]}\nmeta fn request()->[3]int{fixed()}\nmeta let VALUE=request()",
        "E0301",
    );
}

#[test]
fn return_shape_uses_its_declared_type_before_a_body_type_shadow() {
    accepts(
        "type Shape=[3]int\nmeta fn build()->Shape{[1,2,3] where type Shape=[2]int}\nmeta let VALUE=build()\nmeta let _=assert(len(VALUE)==3)",
    );
    rejects(
        "type Shape=[3]int\nmeta fn build()->Shape{[1,2] where type Shape=[2]int}\nmeta let VALUE=build()",
        "E0301",
    );
}

#[test]
fn guard_return_cannot_replace_the_callable_return_shape_environment() {
    accepts(
        "meta fn build()->[3]int{match Some(2){Some(n) if {return [1,2,3]}->[0,0,0],None->[0,0,0]}}\nmeta let VALUE=build()\nmeta let _=assert(VALUE[0]==1)",
    );
    rejects(
        "meta fn build()->[3]int{match Some(2){Some(n) if {return [1,2]}->[0,0,0],None->[0,0,0]}}\nmeta let VALUE=build()",
        "E0301",
    );
}

#[test]
fn an_escaped_local_callable_keeps_the_sibling_environment_of_its_factory_call() {
    accepts(
        "meta fn make(value:int)->fn()->int{first where meta fn first()->int{second()};meta fn second()->int{value}}\nmeta fn observe()->int{let first=make(7);let second=make(9);first()}\nmeta let _=assert(observe()==7)",
    );
}

#[test]
fn a_later_factory_cannot_make_the_old_callable_accept_a_wrong_value() {
    rejects(
        "meta fn make(value:int)->fn()->int{first where meta fn first()->int{second()};meta fn second()->int{value}}\nmeta fn observe()->int{let first=make(7);let second=make(9);first()}\nmeta let _=assert(observe()==9)",
        "E0830",
    );
}

#[test]
fn an_escaped_lambda_uses_its_own_sibling_declarations() {
    accepts(
        "meta fn make(value:int)->fn()->int{\\->read() where meta fn read()->int{value}}\nmeta fn observe()->int{let first=make(7);let second=make(9);assert(first()==7);assert(first()==7);second()}\nmeta let _=assert(observe()==9)",
    );
}

#[test]
fn recursive_and_mutual_sibling_calls_stay_in_the_selected_factory_group() {
    accepts(
        "meta fn make(value:int)->fn(int)->int{read where meta fn read(n:int)->int{if n==0{value}else{read(n-1)}}}\nmeta fn observe()->int{let first=make(7);let second=make(9);assert(first(80)==7);second(80)}\nmeta let _=assert(observe()==9)",
    );
    accepts(
        "meta fn make(value:int)->fn(int)->int{even where meta fn even(n:int)->int{if n==0{value}else{odd(n-1)}};meta fn odd(n:int)->int{if n==0{value}else{even(n-1)}}}\nmeta fn observe()->int{let first=make(7);let second=make(9);assert(first(81)==7);assert(second(80)==9);first(82)}\nmeta let _=assert(observe()==7)",
    );
}

#[test]
fn old_predicates_and_lambdas_inside_siblings_keep_lexical_identity() {
    accepts(
        "meta fn make(value:int)->fn()->bool{test where meta fn test()->bool{(\\->same())()};meta fn same()->bool{value==7}}\nmeta fn observe()->bool{let first=make(7);let old=first();let second=make(9);assert(old);assert(first());!second()}\nmeta let _=assert(observe())",
    );
}

#[test]
fn nested_factory_invocation_restores_the_parent_sibling_mapping() {
    accepts(
        "meta fn make(value:int)->fn()->int{read where meta fn read()->int{let unused=make(99);sibling()};meta fn sibling()->int{value}}\nmeta fn observe()->int{let first=make(7);let second=make(9);assert(first()==7);assert(second()==9);first()}\nmeta let _=assert(observe()==7)",
    );
}

#[test]
fn type_function_defaults_use_their_factory_environment_and_explicit_args_use_the_caller() {
    accepts(
        "meta fn make(enabled:bool)->fn(bool)->bool{check where type Pick=\\T,selected:bool=enabled->if selected{type<T>}else{type<str>};meta fn check(enabled:bool)->bool{let explicit=type<Pick<int,enabled>>==type<int>;let defaulted=type<Pick<int>>==type<int>;explicit==enabled && defaulted}}\nmeta fn observe()->bool{let first=make(true);let second=make(false);assert(first(false));assert(!second(true));first(true)}\nmeta let _=assert(observe())",
    );
}

#[test]
fn type_function_return_restores_the_meta_tail_return_boundary() {
    accepts(
        "type Pick=\\T,selected:bool=true->{if selected{return type<T>};type<str>}\nmeta fn step(n:int)->int{let chosen=type<Pick<int>>;if n==0{1}else{return step(n-1)}}\nmeta let _=assert(step(80)==1)",
    );
}

#[test]
fn early_callee_or_argument_return_skips_all_later_evaluation() {
    let prefix = "meta fn fail()->int{assert(false);0}\nmeta fn pair(a:int,b:int)->int{a+b}\n";
    accepts(&format!(
        "{prefix}meta fn outer()->int{{pair({{return 7}},fail())}}\nmeta let _=assert(outer()==7)"
    ));
    accepts(&format!(
        "{prefix}meta fn outer()->int{{({{return 7;\\value:int->value}})(fail())}}\nmeta let _=assert(outer()==7)"
    ));
}

#[test]
fn already_resolved_shape_metadata_does_not_reenter_its_meta_computation() {
    let source = "meta fn shape()->[2]int{[0,0]}\ntype Pair=[len(shape())]int\nmeta fn relay(value:Pair)->Pair{value}\nmeta let VALUE=relay([1,2])";
    let outcome = Session::with_options(
        source.as_bytes().to_vec(),
        ril_compiler::CheckOptions {
            static_budget: std::num::NonZeroU64::new(1).unwrap(),
            ..Default::default()
        },
    )
    .check();
    assert!(
        matches!(&outcome, CompilationOutcome::Accepted { .. }),
        "{source}\n{outcome:?}"
    );
}

#[test]
fn concrete_alias_witnesses_are_specific_to_the_declaration_group_environment() {
    accepts(
        "meta fn make(enabled:bool)->fn()->bool{check where type Choose=\\T->if enabled{type<T>}else{type<str>};type Selected=Choose<int>;meta fn check()->bool{type<Selected>==type<int>}}\nmeta fn observe()->bool{let first=make(true);let second=make(false);assert(first());assert(!second());first()}\nmeta let _=assert(observe())",
    );
}

#[test]
fn a_local_computed_length_alias_keeps_each_factorys_array_shape() {
    accepts(
        "meta fn make(values:[]int)->fn()->bool{check where type Shape=[len(read())]int;meta fn read()->[]int{values};meta fn check()->bool{type<Shape>==type<[2]int>}}\nmeta fn observe()->bool{let first=make([1,2]);let second=make([1,2,3]);assert(first());assert(!second());first()}\nmeta let _=assert(observe())",
    );
}

#[test]
fn generic_alias_cache_keys_keep_normalized_arguments_and_captured_group_values() {
    use ril_syntax::ast::{ExprKind, Literal, PatternKind, StmtKind};
    let global = "type Fixed<n:int>=[n]int\nmeta let TWO=type<Fixed<2>>==type<[2]int>\nmeta let THREE=type<Fixed<3>>==type<[3]int>\nmeta let DISTINCT=type<Fixed<2>>!=type<Fixed<3>>\nmeta let EQUIVALENT=type<Fixed<1+1>>==type<Fixed<2>>";
    let parsed = ril_syntax::parse(global);
    assert!(parsed.is_ok());
    let evaluation = ril_compiler::static_eval::evaluate(
        &parsed.program,
        ril_compiler_core::target::TargetLayout::POINTER64,
    );
    assert!(
        evaluation.diagnostics.is_empty(),
        "{:?}",
        evaluation.diagnostics
    );
    assert!(
        evaluation.unsupported.is_empty(),
        "{:?}",
        evaluation.unsupported
    );
    for name in ["TWO", "THREE", "DISTINCT", "EQUIVALENT"] {
        let value=evaluation.program.statements.iter().find_map(|statement|match &statement.kind {
            StmtKind::Binding(binding) if matches!(&binding.pattern.kind,PatternKind::Name(found)if found==name)=>Some(&binding.value),_=>None
        }).unwrap();
        assert!(
            matches!(value.kind, ExprKind::Literal(Literal::Bool(true))),
            "{name}: {value:?}"
        );
    }
    // This global declaration still reaches the separate ordinary provenance
    // gate after static evaluation. The assertion is not a full Session pass.
    let full = Session::new(global.as_bytes().to_vec()).check();
    assert!(
        matches!(&full,CompilationOutcome::NotImplemented{reason}if reason.detail.contains("generic, opaque, or sum type declaration")),
        "{full:?}"
    );
    accepts(
        "meta fn check()->bool{assert(type<Fixed<2>>==type<[2]int>);assert(type<Fixed<3>>==type<[3]int>);assert(type<Fixed<2>>!=type<Fixed<3>>);type<Fixed<1+1>>==type<Fixed<2>> where type Fixed<n:int>=[n]int}\nmeta let _=assert(check())",
    );
    accepts(
        "meta fn make(offset:int)->fn()->bool{check where type Fixed<n:int>=[n+offset]int;meta fn check()->bool{type<Fixed<1>>==type<[3]int>}}\nmeta fn observe()->bool{let first=make(2);let second=make(3);assert(first());assert(!second());first()}\nmeta let _=assert(observe())",
    );
}

#[test]
fn inline_signature_shape_witnesses_do_not_run_as_parameter_or_return_metadata() {
    let source = "meta fn shape()->[2]int{[0,0]}\nmeta fn relay(value:[len(shape())]int)->[len(shape())]int{value}\nmeta let VALUE=relay([1,2])";
    let outcome = Session::with_options(
        source.as_bytes().to_vec(),
        ril_compiler::CheckOptions {
            static_budget: std::num::NonZeroU64::new(1).unwrap(),
            ..Default::default()
        },
    )
    .check();
    assert!(
        matches!(&outcome, CompilationOutcome::Accepted { .. }),
        "{source}\n{outcome:?}"
    );
}

#[test]
fn identical_type_function_arguments_in_new_lexical_groups_are_not_false_cycles() {
    accepts(
        "meta fn prior(n:int)->int{n-1}\ntype Recur=\\n:int->{type<Inner<int>> where type Inner=\\T->if n==0{type<T>}else{type<Recur<prior(n)>>}}\ntype Selected=Recur<4>\nmeta let _=assert(type<Selected>==type<int>)",
    );
}

#[test]
fn a_return_inside_a_computed_callee_exits_the_enclosing_meta_function() {
    accepts(
        "meta fn outer()->int{({return 7;\\value:int->value})(1)}\nmeta let _=assert(outer()==7)",
    );
}
