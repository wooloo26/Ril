use ril_compiler::{CheckOptions, Session, session::ProjectSource};
use ril_ir::foreign::{StaticArgumentValue, StaticValue, TypeNode};

fn project(declaration: &str, body: &str) -> Session {
    Session::with_project(
        "virtual/main.ril".into(),
        vec![
            ProjectSource {
                path: "virtual/main.ril".into(),
                bytes: format!("use external/api\n{body}").into_bytes(),
            },
            ProjectSource {
                path: "virtual/external/api.d.ril".into(),
                bytes: declaration.as_bytes().to_vec(),
            },
        ],
        CheckOptions::default(),
    )
    .unwrap()
}
fn core(declaration: &str, body: &str) -> ril_ir::core::Program {
    let verified = project(declaration, body).verify().unwrap();
    ril_compiler::lower::lower_core(&verified).unwrap()
}

#[test]
fn phantom_types_and_values_are_distinct_explicit_instance_arguments() {
    let core = core(
        "pub fn zero<T>()->T\npub fn number<n:int>()->int",
        "fn entry(){let integer=Api::zero<int>();let text=Api::zero<str>();assert(Api::number<7>()==7);assert(Api::number<9>()==9)}",
    );
    assert_eq!(core.external_functions.len(), 4);
    let zero: Vec<_> = core
        .external_functions
        .iter()
        .filter(|function| function.declaration.ends_with("::zero"))
        .collect();
    assert_ne!(zero[0].internal_name, zero[1].internal_name);
    assert_ne!(zero[0].static_arguments, zero[1].static_arguments);
    let values: Vec<_> = core
        .external_functions
        .iter()
        .filter(|function| function.declaration.ends_with("::number"))
        .map(|function| &function.static_arguments[0].value)
        .collect();
    assert!(
        matches!(values[0],StaticArgumentValue::Value{value:StaticValue::Integer{decimal,bits:64,signed:true},..}if decimal=="7")
    );
    assert!(
        matches!(values[1],StaticArgumentValue::Value{value:StaticValue::Integer{decimal,bits:64,signed:true},..}if decimal=="9")
    );
}

#[test]
fn concrete_aliases_fixed_shapes_and_bound_callable_modes_survive_instantiation() {
    let core = core(
        "pub fn identity<T>(value:T)->T\npub fn mark<T>()->int",
        "type BytePair=[2]u8\ntype Callback=fn()->int\nfn entry(){let action=Api::identity<BytePair>;let output=action([1u8,2u8]);assert(len(output)==2);assert(Api::mark<Callback>()==0)}",
    );
    let identity = &core.external_functions[0];
    assert!(matches!(
        identity.signature.arena[identity.signature.parameters[0] as usize],
        TypeNode::Array {
            length: Some(2),
            ..
        }
    ));
    assert!(matches!(
        identity.static_arguments[0].value,
        StaticArgumentValue::Type {
            schema: Some(_),
            ..
        }
    ));
    let marker = &core.external_functions[1];
    assert!(matches!(
        marker.static_arguments[0].value,
        StaticArgumentValue::Type { schema: None, .. }
    ));
}

#[test]
fn specialization_retains_argument_authority_and_result_duties() {
    for (declaration, body) in [
        (
            "pub fn identity<T>(value:T)->T",
            "fn entry(){let mut values=[1];values[0]=2;let output=Api::identity<[]int>(values)}",
        ),
        (
            "pub fn outcome<T>()->Result<T,str>",
            "fn entry(){let ignored=Api::outcome<int>()}",
        ),
        (
            "pub fn number<n:int>()->int",
            "fn entry(){let ignored=Api::number<true>()}",
        ),
    ] {
        assert!(project(declaration, body).verify().is_err(), "{body}");
    }
    let verified = project(
        "pub fn identity<T>(value:T)->T",
        "fn entry(){let value=Api::identity(1)}",
    )
    .verify()
    .unwrap();
    assert!(
        ril_compiler::lower::lower_core(&verified).is_err(),
        "unspecialized inferred callable needs its own complete static instance"
    );
}

#[test]
fn static_instances_and_later_local_functions_have_distinct_definition_ids() {
    let core = core(
        "pub fn zero<T>()->T",
        "fn first()->int{Api::zero<int>()}\nfn second()->str{assert(local()==2);Api::zero<str>() where fn local()->int{2}}\nfn entry(){let a=first();let b=second()}",
    );
    let module = ril_codegen::lower::lower_native_with_entry(&core, "entry").unwrap();
    let symbols: std::collections::BTreeSet<_> = module
        .functions
        .iter()
        .map(|function| &function.symbol)
        .collect();
    assert_eq!(
        symbols.len(),
        module.functions.len(),
        "concrete foreign instances cannot reuse local function symbols"
    );
    let definitions: std::collections::BTreeSet<_> = core
        .functions
        .iter()
        .map(|function| function.definition.0)
        .chain(
            core.external_functions
                .iter()
                .map(|function| function.definition.0),
        )
        .collect();
    assert_eq!(
        definitions.len(),
        core.functions.len() + core.external_functions.len()
    );
}

#[test]
fn ordinary_defaults_preserve_static_values_earlier_arguments_and_lexical_shadowing() {
    core(
        "pub fn number<n:int>(base:int=n,value:int=base+n)->int\npub fn shadow<n:int>(value:int={let n=n+1;n})->int\npub fn apply<n:int>(callback:fn(int)->int=\\n->n+1)->int\npub fn fixed<n:int>(callback:fn()->int=\\->n)->int\npub fn empty<T>(items:[]T=[])->int\npub fn copied<T>(source:T,value:T=source)->T",
        "fn entry(){assert(Api::number<7>()==14);assert(Api::number<7>(10)==17);assert(Api::number<9>()==18);assert(Api::shadow<7>()==8);assert(Api::apply<99>()==1);assert(Api::fixed<7>()==7);assert(Api::empty<int>()==0);assert(Api::empty<str>()==0);assert(Api::copied<int>(7)==7);assert(Api::copied<str>(\"ok\")==\"ok\")}",
    );
}

#[test]
fn default_specialization_cannot_hide_effects_forward_references_or_live_exchange() {
    for declaration in [
        "pub fn bad<n:int>(value:int=later,later:int=n)->int",
        "pub fn bad<n:int>(mut value:int=n)->int",
        "pub eff Read{get()->int}\npub fn bad<n:int>(value:int=Read::get())->int",
    ] {
        assert!(
            project(declaration, "fn entry(){Api::bad<7>()}")
                .verify()
                .is_err()
        );
    }
    assert!(
        project(
            "pub fn copied<T>(source:[]T,value:[]T=source)->int",
            "fn entry(){let mut source=[1];source[0]=2;Api::copied<int>(source)}",
        )
        .verify()
        .is_err()
    );
    assert!(
        project("pub fn bad<T>(value:T=0)->T", "fn entry(){Api::bad<int>()}")
            .verify()
            .is_err(),
        "a default must satisfy every permitted type instantiation"
    );
}

#[test]
fn default_local_type_annotations_and_scalar_kinds_are_concrete_per_instance() {
    let core = core(
        "pub fn typed<T>(items:[]T={let items:[]T=[];items})->int\npub fn text<message:str>(value:str=message)->str\npub fn small<n:u8>(value:u8=n)->u8",
        "fn entry(){assert(Api::typed<int>()==0);assert(Api::typed<str>()==0);assert(Api::text<\"hello\">()==\"hello\");assert(Api::small<7u8>()==7u8)}",
    );
    assert_eq!(core.external_functions.len(), 4);
}

#[test]
fn differing_default_callable_instances_require_distinct_native_identities() {
    for declaration in [
        "pub fn fixed<n:int>(callback:fn()->int=\\->n)->int",
        "pub fn fixed<n:int>(value:int=(\\->n)())->int",
        "pub fn fixed<n:int>(value:int={read() where fn read()->int{n}})->int",
    ] {
        let verified = project(
            declaration,
            "fn entry(){assert(Api::fixed<7>()==7);assert(Api::fixed<9>()==9)}",
        )
        .verify()
        .unwrap();
        let core = ril_compiler::lower::lower_core(&verified).unwrap();
        ril_codegen::lower::lower_native_with_entry(&core, "entry").unwrap();
    }
}

#[test]
fn generic_defaults_keep_match_binders_and_value_test_references_distinct() {
    core(
        "pub fn selected<n:int>(value:int=match Some(n){Some(n)->n+1,None->n})->int\npub fn tested<n:int>(value:int=if n is n {n+1}else{0})->int\npub fn restored<n:int>(value:int={let selected=match Some(5){Some(n) if n is 5->n,None->0,_->0};selected+n})->int",
        "fn entry(){assert(Api::selected<7>()==8);assert(Api::selected<9>()==10);assert(Api::tested<7>()==8);assert(Api::restored<7>()==12)}",
    );
}

#[test]
fn generic_defaults_specialize_local_handlers_and_hoisted_declarations() {
    for (declaration, expected) in [
        (
            "pub fn selected<n:int>(value:int={helper() where fn helper()->int{n}})->int",
            7,
        ),
        (
            "pub fn selected<n:int>(value:int={let n=n+1;helper() where fn helper()->int &{closure,n}{n}})->int",
            8,
        ),
        (
            "pub fn selected<n:int>(value:int={with Read::get()->resume n;Read::get() where eff Read{get()->int}})->int",
            7,
        ),
        (
            "pub fn selected<n:int>(value:int={with Read::get(n)->resume n+1;Read::get(n) where eff Read{get(int)->int}})->int",
            8,
        ),
        (
            "pub fn selected<n:int>(value:int={outer() where fn outer()->int{inner() where fn inner()->int{n}}})->int",
            7,
        ),
        (
            "pub fn selected<T>(value:int={let items:Items=[];len(items) where type Items=[]T})->int",
            0,
        ),
        (
            "pub fn selected<T>(value:int={let items:Items<T>=[];len(items) where type Items<U>=[]U})->int",
            0,
        ),
        (
            "pub fn selected<T>(value:int={let items:Items=[];len(items) where type Items<U=T>=[]U})->int",
            0,
        ),
        (
            "pub fn selected<n:int>(value:int={with supply(n);Read::get() where eff Read{get()->int};fn supply(value:int,action:fn()->int)->int{with Read::get()->resume value;action()}})->int",
            7,
        ),
    ] {
        let argument = if declaration.contains("<T>") {
            "int"
        } else {
            "7"
        };
        let verified = project(
            declaration,
            &format!("fn entry(){{assert(Api::selected<{argument}>()=={expected})}}"),
        )
        .verify()
        .unwrap();
        ril_compiler::lower::lower_core(&verified).unwrap();
    }
}

#[test]
fn nested_default_specialization_preserves_initialization_result_and_effect_duties() {
    for declaration in [
        "pub fn selected<n:int>(value:int={read();let n=1;n where fn read()->int &{closure,n}{n}})->int",
        "pub fn selected<n:int>(value:int={let n=1;read() where fn read()->int{n}})->int",
        "pub fn selected<n:int>(value:int={let answer:Result<int,str>=Ok(n);n})->int",
        "pub fn selected<n:int>(value:int={Read::get() where eff Read{get()->int}})->int",
        "pub fn selected<n:int>(value:int={with Read::get()->Read::get();Read::get() where eff Read{get()->int}})->int",
    ] {
        assert!(
            project(declaration, "fn entry(){Api::selected<7>()}")
                .verify()
                .is_err(),
            "{declaration}"
        );
    }
}

#[test]
fn generic_defaults_keep_outer_types_in_local_function_signatures() {
    for declaration in [
        "pub fn selected<T>(base:T,value:T={copy(base) where fn copy(item:T)->T{item}})->T",
        "pub fn selected<T>(base:T,value:T={copy(base) where fn copy<T>(item:T)->T{item}})->T",
        "pub fn selected<T>(base:T,value:T={copy(base,0) where fn copy<U>(item:T,unused:U)->T{item}})->T",
    ] {
        core(declaration, "fn entry(){assert(Api::selected<int>(7)==7)}");
    }
    core(
        "pub fn selected<T>(value:int={let text:T=\"a\";len(text) where type T=str})->int",
        "fn entry(){assert(Api::selected<int>()==1)}",
    );
    for declaration in [
        "pub fn selected<T>(base:T,value:T={copy(base) where fn copy<T>(item:T)->T &{closure,base}{base}})->T",
        "pub fn selected<T>(base:T,value:T={copy(base) where fn copy<T>(item:T)->int{item}})->T",
        "pub fn selected<T>(base:T,value:T={let text:T=\"a\";base where type T=int})->T",
    ] {
        let outcome = project(declaration, "fn entry(){Api::selected<int>(7)}").check();
        assert!(
            matches!(&outcome, ril_compiler::CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
            "{outcome:?}"
        );
    }
}
