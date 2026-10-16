use super::model::Ty;
use super::*;
fn check(source: &str) -> AnalyzeOutcome {
    let syntax = ril_syntax::parse(source);
    assert!(syntax.is_ok(), "parse: {:?}", syntax.diagnostics);
    analyze(&syntax.program, FileId(0))
}
fn accepts(source: &str) {
    let result = check(source);
    assert!(
        result.program.is_some(),
        "diagnostics={:?}, unsupported={:?}",
        result.diagnostics,
        result.unsupported
    );
}
fn rejects(source: &str, code: &str) {
    let result = check(source);
    assert!(result.program.is_none());
    assert!(
        result.diagnostics.iter().any(|d| d.code == code),
        "expected {code}, got {:?}; unsupported={:?}",
        result.diagnostics,
        result.unsupported
    );
}
#[test]
fn simple_function_and_scalar_local_mutation() {
    accepts("pub fn main() { var n = 0; n += 1; assert(n == 1) }");
}
#[test]
fn immutable_publication_requires_lexical_writer_end() {
    rejects(
        "type Cell = { mut value: int }\nfn example() { let mut value = Cell.{ value: 0 }; value.value += 1; let frozen = value }",
        "E0535",
    );
    accepts(
        "type Cell = { mut value: int }\nfn example() { let frozen = { let mut value = Cell.{ value: 0 }; value.value += 1; value } }",
    );
}
#[test]
fn readonly_return_does_not_grant_write_authority() {
    rejects(
        "type Cell = { mut count: int }\nfn identity(cell: Cell) -> Cell { cell }\nfn example() { let item = Cell.{count:0}; let mut value = identity(item); value.count += 1 }",
        "E0528",
    );
}
#[test]
fn local_writable_alias_requires_marker() {
    rejects(
        "type Cell = { mut count: int }\nfn example() { let mut value = Cell.{count:0}; let mut alias = value; alias.count += 1; value.count += 1 }",
        "E0510",
    );
    accepts(
        "type Cell = { mut count: int }\nfn example() { let mut value = Cell.{count:0}; let mut alias = ^mut value; alias.count += 1; value.count += 1 }",
    );
}
#[test]
fn actual_write_and_read_origins_control_loans() {
    rejects(
        "type Cell = { mut count: int }\nfn copy_count(source:Cell, mut target:Cell) &mut {target.count=source.count}\nfn example(){let mut value=Cell.{count:0};copy_count(value,mut value)}",
        "E0524",
    );
    accepts(
        "type Cell = { mut count: int }\nfn copy_count(source:Cell, mut target:Cell) &mut {target.count=source.count}\nfn example(){let source=Cell.{count:1};let mut value=Cell.{count:0};copy_count(source,mut value)}",
    );
}
#[test]
fn branch_permutation_preserves_pair_disjointness() {
    accepts(
        "type Cell={mut value:int}\nfn swap(mut a:Cell,mut b:Cell)&mut{let n=a.value;a.value=b.value;b.value=n}\nfn permute(flag:bool,^mut a:Cell,^mut b:Cell)->(Cell,Cell)&^mut{if flag{(^mut a,^mut b)}else{(^mut b,^mut a)}}\nfn example(flag:bool){let mut a=Cell.{value:1};let mut b=Cell.{value:2};let mut pair=permute(flag,^mut a,^mut b);swap(mut pair.0,mut pair.1)}",
    );
}
#[test]
fn same_origin_different_names_is_not_disjoint() {
    rejects(
        "type Cell={mut value:int}\nfn swap(mut a:Cell,mut b:Cell)&mut{let n=a.value;a.value=b.value;b.value=n}\nfn example(){let mut a=Cell.{value:1};let mut b=^mut a;swap(mut a,mut b)}",
        "E0523",
    );
}
#[test]
fn opaque_runtime_indices_may_overlap() {
    rejects(
        "type Cell={mut value:int}\nfn swap(mut a:Cell,mut b:Cell)&mut{let n=a.value;a.value=b.value;b.value=n}\nfn example(i:int,j:int){let mut cells=[Cell.{value:1},Cell.{value:2}];swap(mut cells[i],mut cells[j])}",
        "E0523",
    );
}
#[test]
fn dead_write_does_not_exercise_var() {
    rejects("fn example(){var n=0;if false {n+=1}}", "E0527");
}
#[test]
fn named_state_survives_callback_and_alias() {
    rejects(
        "var count=0\nfn advance()&{mut count}{count+=1}\nfn invoke(action:fn()->()){action()}\nfn example(){invoke(advance)}",
        "E0510",
    );
    accepts(
        "var count=0\nfn advance()&{mut count}{count+=1}\nfn invoke(action:fn()->()){action()}\nfn example()&{mut count}{invoke(advance)}",
    );
}
#[test]
fn cloned_internal_aliases_require_marker() {
    rejects(
        "type Cell={mut count:int}\ntype Holder={mut child:Cell}\nfn example(){let mut holder=Holder.{child:Cell.{count:0}};holder.child=Cell.{count:1};let mut alias=holder.child;alias.count+=1}",
        "E0510",
    );
    rejects(
        "type Cell={mut count:int}\ntype Holder={child:Cell}\nfn example(){let mut cell=Cell.{count:0};let mut holder=Holder.{child:^mut cell};holder.child.count+=1;let mut alias=holder.child;alias.count+=1}",
        "E0510",
    );
    rejects(
        "type Cell={mut count:int}\nfn example(){let cell=Cell.{count:0};let mut pair=clone((cell,cell));pair.0.count+=1}",
        "E0510",
    );
}
#[test]
fn clones_preserve_formal_alias_relations_and_remap_boxed_payloads() {
    rejects(
        "type Cell={mut count:int}\nfn swap(mut a:Cell,mut b:Cell)&mut{a.count+=1;b.count+=1}\nfn unsafe_copy(pair:(Cell,Cell)){let mut copy=^mut clone(pair);swap(mut copy.0,mut copy.1)}",
        "E0523",
    );
    let result = check(
        "type Cell={mut count:int}\nfn example(){let source=Some(Cell.{count:0});let copied=clone(source);assert(source is Some(_));assert(copied is Some(_))}",
    );
    assert!(
        result.program.is_some(),
        "{:?} {:?}",
        result.diagnostics,
        result.unsupported
    );
    let program = result.program.unwrap();
    let source = program
        .facts()
        .bindings
        .iter()
        .find(|binding| binding.name == "source")
        .unwrap();
    let copied = program
        .facts()
        .bindings
        .iter()
        .find(|binding| binding.name == "copied")
        .unwrap();
    assert_eq!(
        copied.value.option_payload.as_ref().unwrap().origins.nodes,
        copied.value.origins.nodes
    );
    for a in &source.value.origins.nodes {
        for b in &copied.value.origins.nodes {
            assert_eq!(
                program.facts().heap.relation(*a, *b).disjoint,
                super::relations::Condition::TRUE
            );
        }
    }
}
#[test]
fn unknown_names_inside_interpolation_are_checked() {
    rejects("fn example(){let text=\"{missing}\"}", "E0204");
}
#[test]
fn mutable_closure_environment_remains_live() {
    accepts(
        "type Step=fn()->int &closure\nfn make_step()->Step &capture{var count=0;\\->{count+=1;count}}\nfn example(){let mut step=make_step();let value=step();let _=clone(value)}",
    );
    rejects(
        "type Step=fn()->int &closure\nfn make_step()->Step &capture{var count=0;\\->{count+=1;count}}\nfn example(){let step=make_step()}",
        "E0535",
    );
}
#[test]
fn derive_draft_can_only_leave_as_detached_copy() {
    accepts(
        "type Cell={mut count:int}\nfn example(){var saved=Cell.{count:0};let base=Cell.{count:1};let result=base |> derive \\mut draft->{draft.count+=1;saved=clone_immut(draft)}}",
    );
    rejects(
        "type Cell={mut count:int}\nfn example(){var saved=Cell.{count:0};let base=Cell.{count:1};let result=base |> derive \\mut draft->{draft.count+=1;saved=draft}}",
        "E0607",
    );
}
#[test]
fn cyclic_clone_preserves_backedge_provenance() {
    accepts(
        "type Node={mut value:int,mut following:?Node}\nfn example(){let mut original=Node.{value:1,following:None};original.following=Some(^mut original);let mut copied=^mut clone(original);let view back=copied.following ?? panic(\"missing\");copied.value=2;assert(back.value==2)}",
    );
}
#[test]
fn callable_modes_are_invariant() {
    rejects(
        "type Cell={mut count:int}\nfn bump(mut cell:Cell)&mut{cell.count+=1}\nfn example(){let action:fn(Cell)->() &mut=bump}",
        "E0407",
    );
}
#[test]
fn named_arguments_defaults_and_ascription() {
    accepts(
        "fn pair(a:int=1,b:int=2)->(int,int){(a,b)}\nfn example(){let values=pair(b:20,10);let alias=pair;let other=alias()}",
    );
    rejects(
        "fn pair(a:int=1,b:int=2)->(int,int){(a,b)}\nfn example(){let values=pair(1,a:2)}",
        "E0325",
    );
    rejects(
        "fn item(value:int=1)->int{value}\nfn example(){let renamed:fn(other:int)->int=item;let value=renamed(value:2)}",
        "E0339",
    );
    rejects(
        "fn item(value:int=1)->int{value}\nfn example(){let renamed:fn(other:int)->int=item;let value=renamed()}",
        "E0314",
    );
}
#[test]
fn mutable_arguments_must_be_addressable() {
    rejects(
        "type Cell={mut count:int}\nfn bump(mut cell:Cell)&mut{cell.count+=1}\nfn example(){bump(mut Cell.{count:0})}",
        "E0410",
    );
}
#[test]
fn defaults_are_checked_without_calls() {
    rejects("fn value(a:int=b,b:int=1)->int{a+b}", "E0408");
    rejects(
        "eff Read{get()->int}\nfn value(a:int=Read::get())->int @Read{a}",
        "E0409",
    );
}
#[test]
fn integer_literal_ranges_and_numeric_types() {
    accepts("fn example(){let a=-128i8;let b=255u8;let c=1u8+2}");
    rejects("fn example(){let value=128i8}", "E0326");
    rejects("fn example(){let value=-1u8}", "E0326");
    rejects("fn example(){let value=1u8+1u16}", "E0301");
}
#[test]
fn array_shape_and_index_type_are_checked() {
    rejects("fn example(){let values:[2]int=[1]}", "E0301");
    rejects("fn example(){let values:[-1]int=[]}", "E0815");
    rejects("fn example(){let value=[1][\"0\"]}", "E0301");
}
#[test]
fn map_keys_and_value_paths_preserve_types_and_origins() {
    accepts(
        "fn example(){let mut mapping=[\"first\":1,\"second\":2];for mapping as (key,value){mapping[\"second\"]=7;assert(value>=0)}}",
    );
    rejects("fn example(){let mapping=[1.0:1]}", "E0328");
    rejects(
        "fn example(){let mapping=[\"key\":1];let value=mapping[0]}",
        "E0301",
    );
    rejects(
        "fn example(){let mut mapping=[\"key\":1];mapping[0]=2}",
        "E0301",
    );
    rejects(
        "type Cell={mut count:int}\nfn bump(mut cell:Cell)&mut{cell.count+=1}\nfn example(key:str){let mut original=Cell.{count:0};let mut other=Cell.{count:0};original.count+=1;other.count+=1;var mapping=[\"a\":original,\"b\":other];bump(mut mapping[key])}",
        "E0520",
    );
}
#[test]
fn scoped_cleanup_checks_contract_and_authority_at_the_lexical_exit() {
    rejects(
        "type Guard={on_close:fn()->()}\nfn example() @Fiber{let scoped item=Guard.{on_close:\\->Fiber::yield()}}",
        "E0616",
    );
    accepts(
        "type Guard={on_close:fn()->()}\nfn example(){let scoped item=Guard.{on_close:\\->()}}",
    );
    rejects("fn example(){let scoped item=42}", "E0541");
    rejects(
        "type Guard={on_close:fn()->()}\nfn example(){let scoped item=Guard.{on_close:\\->{loop{}}}}",
        "E0617",
    );
    rejects(
        "type Guard={on_close:fn()->()}\nfn example()->Guard{let scoped item=Guard.{on_close:\\->()};item}",
        "E0604",
    );
    accepts(
        "type Guard={on_close:fn()->()}\nfn example()->Guard{let scoped item=Guard.{on_close:\\->()};clone(item)}",
    );
    accepts(
        "type Guard={mut on_close:fn()->()}\nfn example(){let mut events:[]int=[];{let scoped mut item=Guard.{on_close:\\->events !> Array::push(1)};item.on_close=\\->events !> Array::push(2)}}",
    );
}
#[test]
fn effect_operation_handlers_check_modes_resumption_and_outward_state() {
    rejects(
        "eff Read{get()->int}\nfn example(){with Read::get()->resume \"bad\";()}",
        "E0624",
    );
    rejects(
        "eff Read{get()->int}\nfn example(){with Read::get()->\"bad\";()}",
        "E0625",
    );
    rejects(
        "eff Read{get()->int}\nfn example(){with Read::get()->{let result:Result<int,str>=Err(\"bad\");resume 1};let _=Read::get()}",
        "E0720",
    );
    accepts("eff Read{get()->int}\nfn example()->int{with Read::get()->resume 7;Read::get()+1}");
    accepts(
        "eff Read{get()->int}\nfn helper()->int @Read{Read::get()}\nfn example()->int{with Read::get()->resume 7;helper()}",
    );
    accepts("eff Read{get()->int}\nfn example(){with Read::get()->();let _=Read::get()}");
    rejects(
        "eff Read{get()->int}\nfn example(){with Read::get()->resume \"bad\";let _=Read::get()}",
        "E0624",
    );
    rejects(
        "eff Read{get()->int}\nfn example(){with{Read::get()->resume 1,Read::get()->resume 2};let _=Read::get()}",
        "E0622",
    );
    rejects("fn example(){resume ()}", "E0623");
    rejects(
        "type Cell={mut count:int}\neff Edit{apply(mut Cell)->() &mut}\nfn example(){with Edit::apply(item)->{item.count+=1;resume ()};let mut cell=Cell.{count:0};Edit::apply(mut cell)}",
        "E0406",
    );
    accepts(
        "type Cell={mut count:int}\neff Edit{apply(mut Cell)->() &mut}\nfn example(){with Edit::apply(mut item)->{item.count+=1;resume ()};let mut cell=Cell.{count:0};Edit::apply(mut cell)}",
    );
    rejects(
        "eff Read{get()->int}\nfn example(){with Read::get()->\"bad\";let _=Read::get()}",
        "E0625",
    );
    rejects(
        "eff Read{get()->int}\nfn example(){with Read::get()->{resume 1;resume 2};let _=Read::get()}",
        "E0610",
    );
    rejects(
        "eff Read{get()->int}\nfn example(){with Read::get()->{let action=\\->{resume 1};action()};let _=Read::get()}",
        "E0611",
    );
    rejects(
        "type Cell={mut count:int}\neff Edit{apply(mut Cell)->() &mut}\nfn example(){with Edit::apply(mut item)->{item.count+=1;resume ();item.count+=1};let mut cell=Cell.{count:0};Edit::apply(mut cell)}",
        "E0540",
    );
    accepts(
        "eff Read{get()->int}\nfn example()->int{with Read::get()->resume 7;{with Read::get()->{let outer=Read::get();resume outer+1};Read::get()}}",
    );
}
#[test]
fn unused_definitions_and_unreachable_branches_still_obey_ordinary_types() {
    accepts("fn read(item:?{id:int})->int{if item==None{return -1};item.id}");
    accepts("fn read(action:?(fn()->int))->int{if action==None{return -1};action()}");
    rejects(
        "fn example(){var item:?int=Some(1);if item!=None{item=None;let value=item+1}}",
        "E0310",
    );
    rejects("fn bad(item:?{id:int})->int{item.id}", "E0310");
    rejects("fn bad(action:?(fn()->int))->int{action()}", "E0310");
    rejects("fn example(){while false{unknown}}", "E0204");
    rejects("fn example(){while false{last 1}}", "E0301");
    rejects("fn example()->str{loop{last 1}}", "E0301");
    accepts("fn example()->int{loop{last 1}}");
    rejects("fn example(){var value=0;loop{next;value=1}}", "E0527");
    rejects(
        "fn example(){()
where
fn invalid()->str{1}
}",
        "E0301",
    );
    rejects("fn example(){if false{unknown}}", "E0204");
    rejects("fn example()->i8{if true{1}else{128}}", "E0326");
    rejects("fn example()->[]i8{if true{[1]}else{[128]}}", "E0326");
    accepts("fn example(){let value=1;{let value=2}}");
    accepts("fn example(){let result:Result<int,str>=Err(\"bad\");let _=panic(\"stop\")}");
}
#[test]
fn optional_refinements_are_invalidated_by_live_writes_and_unknown_callbacks() {
    accepts("fn read(item:?{id:int})->int{if item!=None&&item.id>0{item.id}else{0}}");
    rejects(
        "type Cell={mut value:?int}\nfn example(mut cell:Cell)&mut{if cell.value!=None&&{cell.value=None;true}{let value=cell.value+1}}",
        "E0310",
    );
    rejects(
        "type Cell={mut value:?int}\nfn example(mut cell:Cell)&mut{if cell.value is Some(replace()){let value=cell.value+1}\nwhere\nfn replace()->int &{mut cell}{cell.value=None;1}\n}",
        "E0310",
    );
    accepts(
        "type Cell={mut value:?int}\nfn example(mut cell:Cell)&mut{if cell.value!=None{let value=cell.value+1};cell.value=None}",
    );
    rejects(
        "type Cell={mut value:?int}\nfn clear(mut cell:Cell)&mut{cell.value=None}\nfn example(mut cell:Cell)&mut{if cell.value!=None{clear(mut cell);let value=cell.value+1}}",
        "E0310",
    );
    rejects(
        "type Cell={mut value:?int}\nfn example(mut cell:Cell,action:fn()->())&mut{if cell.value!=None{action();let value=cell.value+1};cell.value=None}",
        "E0533",
    );
    accepts(
        "type Cell={mut value:?int}\nfn example(mut cell:Cell,action:fn()->())&mut{let snapshot=clone_immut(cell);if snapshot.value!=None{action();let value=snapshot.value+1};cell.value=None}",
    );
}
#[test]
fn provenance_corpus_static_verdicts() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests");
    let cases = ril_test::discover_cases(&root).unwrap();
    let cases: Vec<_> = cases
        .into_iter()
        .filter(|case| case.bundle == "tests/conformance/provenance.ril")
        .collect();
    assert_eq!(cases.len(), 6);
    for case in cases {
        let source = case
            .files
            .iter()
            .find(|file| file.name == case.root)
            .unwrap();
        let outcome = check(std::str::from_utf8(&source.bytes).unwrap());
        if case.meta.mode == ril_test::Mode::CheckFail {
            assert!(outcome.program.is_none(), "{} accepted", case.id);
            for error in case.errors {
                assert!(
                    outcome.diagnostics.iter().any(|d| d.code == error),
                    "{}: expected {error}, actual {:?}",
                    case.id,
                    outcome.diagnostics
                );
            }
        } else {
            assert!(
                outcome.program.is_some(),
                "{}: {:?}; {:?}",
                case.id,
                outcome.diagnostics,
                outcome.unsupported
            );
        }
    }
}
#[test]
fn explicit_nested_immutable_qualification_survives_clone() {
    rejects(
        "type Cell={mut count:int}\ntype Holder={mut count:int,child:Immut<Cell>}\nfn example(){let holder=Holder.{count:0,child:clone_immut(Cell.{count:7})};let mut values:[]Holder=[];values !> Array::push(clone(holder));values[0].child.count+=1}",
        "E0522",
    );
}
#[test]
fn retained_global_capture_uses_its_named_source_mode() {
    accepts(
        "var count=0\ntype Step=fn()->int &closure\nfn make()->Step &capture &{^mut count}{\\->{count+=1;count}}",
    );
    rejects(
        "var count=0\ntype Step=fn()->int &closure\nfn make()->Step &capture{\\->{count+=1;count}}",
        "E0510",
    );
}
#[test]
fn referencing_a_named_function_does_not_create_a_lexical_environment() {
    accepts("type Action=fn()->()\nfn helper(){}\nfn make()->Action{\\->helper()}");
}
#[test]
fn generic_binders_are_distinct_and_definitions_are_universal() {
    rejects("fn forge<T,U>(value:T)->U{value}", "E0301");
    rejects("fn forged<T>()->T{1}", "E0301");
    accepts(
        "fn first<T>(value:T)->T{value}\nfn second<T>(value:T)->T{first(value)}\nfn example(){let value=second(1)}",
    );
    let result = check("fn first<T>(value:T)->T{value}\nfn second<T>(value:T)->T{value}");
    let facts = result.program.unwrap();
    let binders: Vec<_> = facts.facts().generic_binders.values().collect();
    assert_eq!(binders.len(), 2);
    assert_ne!(binders[0].identity, binders[1].identity);
}
#[test]
fn builtins_and_value_parameter_roles_are_checked() {
    rejects("fn example(){panic(1)}", "E0301");
    rejects("fn example(){assert(true,0)}", "E0301");
    rejects("fn example(){let n=len(42)}", "E0301");
    rejects("fn example(mut text:str)&mut{let n=len(text)}", "E0401");
    accepts("fn example(){assert(true,\"ok\");let n=len(\"text\")}");
}
#[test]
fn interpolation_format_types_are_checked() {
    rejects("fn example(){let text=\"{true:.2}\"}", "E0329");
    rejects("fn example(){let text=\"{1:.2}\"}", "E0329");
    rejects(
        "fn example(){let word=\"word\";let text=\"{word:x}\"}",
        "E0329",
    );
}
#[test]
fn numeric_contexts_are_recorded_without_promoting_selected_values() {
    let source = "fn inc(value:i8)->i8{value+1}\nfn example(){let n=inc(127);let values:[]u8=[1,2];let f:f32=1.25}";
    let result = check(source);
    assert!(
        result.program.is_some(),
        "{:?} {:?}",
        result.diagnostics,
        result.unsupported
    );
    let program = result.program.unwrap();
    let map = &program.facts().contextual_types;
    for (text, ty, selected_type) in [
        (
            "127",
            Ty::Int("i8".into()),
            crate::numeric_literals::NumberType::I8,
        ),
        (
            "1.25",
            Ty::Float("f32".into()),
            crate::numeric_literals::NumberType::F32,
        ),
    ] {
        let offset = source.find(text).unwrap() as u32;
        let selections: Vec<_> = program
            .facts()
            .numeric_selections
            .iter()
            .filter(|selection| {
                selection.span.start == offset && selection.span.end == offset + text.len() as u32
            })
            .collect();
        if selections.is_empty() {
            assert_eq!(map.get(&(0, offset, offset + text.len() as u32)), Some(&ty));
        } else {
            for selection in selections {
                assert_eq!(selection.ty, selected_type);
            }
        }
    }
    rejects(
        "fn take(value:i8){}\nfn example(){let x=1;take(x)}",
        "E0301",
    );
    rejects("fn example(){let x:i8=1;let y:i16=x}", "E0301");
    rejects(
        "fn take(values:[]i8){}\nfn example(){let values=[1,2];take(values)}",
        "E0301",
    );
    accepts("fn tiny()->i8{127+1}\nfn example(){let x:i8=-128}");
}
#[test]
fn result_producers_require_inspection_and_recovery_preserves_payload() {
    accepts("fn example(){let recovered=Err(\"error\") ?? \\_error -> 7;assert(recovered==7)}");
    rejects(
        "fn example(){let result:Result<int,str>=Err(\"bad\");let alias=result}",
        "E0720",
    );
    accepts(
        "fn example(){let result:Result<int,str>=Err(\"bad\");let alias=result;assert(alias is Err(_))}",
    );
    rejects(
        "let RESULT:Result<int,str>=Err(\"bad\")\nfn inspect()->bool{RESULT is Err(_)}",
        "E0720",
    );
    rejects(
        "fn example(){let result:Result<int,str>=Err(\"bad\");let inspect=\\->result is Err(_)}",
        "E0720",
    );
}
#[test]
fn conditional_result_obligations_follow_each_producer_path() {
    accepts(
        "fn maybe(flag:bool)->?Result<int,str>{if flag{Some(Err(\"error\"))}else{None}}\nfn example(){let result=maybe(true);match result{Some(value)->{assert(value is Err(_))},None->()}}",
    );
    accepts(
        "fn forward(flag:bool,result:Result<int,str>)->?Result<int,str>{if flag{Some(result)}else{assert(result is Err(_));None}}\nfn example(){let result=forward(true,Err(\"error\"));match result{Some(value)->{assert(value is Err(_))},None->()}}",
    );
    rejects(
        "fn example(flag:bool){let result:Result<int,str>=Err(\"error\");if flag{assert(result is Err(_))}}",
        "E0720",
    );
    rejects(
        "fn example(flag:bool){let result:Result<int,str>=Err(\"error\");let checked=flag && (result is Err(_))}",
        "E0720",
    );
    rejects(
        "fn example(value:?int){let result:Result<int,str>=Err(\"error\");let number=value ?? {assert(result is Err(_));0}}",
        "E0720",
    );
    rejects(
        "fn example(){let result:Result<int,str>=Err(\"error\");let number=Some(1) ?? {assert(result is Err(_));0}}",
        "E0720",
    );
    rejects(
        "fn example(){let result:Result<int,str>=Err(\"error\");let number=Ok(1) ?? \\_error->{assert(result is Err(_));0}}",
        "E0720",
    );
}
#[test]
fn deep_reads_include_nested_origins_under_independent_shells() {
    accepts(
        "type Cell={mut count:int}\nfn inspect(mapping:[str:Cell],mut cell:Cell)&mut{let present=\"key\" in mapping;cell.count+=1}\nfn example(){let mut cell=Cell.{count:0};inspect([\"key\":cell],mut cell)}",
    );
    rejects(
        "fn example(){let value=7;let action=\\->value;let copy=clone(action)}",
        "E0530",
    );
    rejects(
        "fn example(){let value=7;let container=.{action:\\->value};let copy=clone(container)}",
        "E0530",
    );
    rejects(
        "fn example(){let container=.{action:\\->1};let same=container==container}",
        "E0327",
    );
    rejects("fn example(){let present=true in [1]}", "E0301");
    rejects("fn example(){let present=1 in \"text\"}", "E0327");
    rejects(
        "type Cell={mut count:int}\ntype Holder={child:Cell}\nfn inspect(holder:Holder,mut cell:Cell)&mut{let copy=clone(holder);cell.count+=1}\nfn example(){let mut cell=Cell.{count:0};var holder=Holder.{child:cell};inspect(holder,mut cell)}",
        "E0524",
    );
    rejects(
        "type Cell={mut count:int}\ntype Holder={child:Cell}\nfn inspect(holder:Holder,mut cell:Cell)&mut{let same=holder==holder;cell.count+=1}\nfn example(){let mut cell=Cell.{count:0};var holder=Holder.{child:cell};inspect(holder,mut cell)}",
        "E0524",
    );
}
#[test]
fn reassignment_and_fallback_preserve_their_separate_boundaries() {
    rejects("fn example(){var mut values=[1];values=[2]}", "E0527");
    accepts("fn example(){var mut values=[1];values=[2];values !> Array::push(3)}");
    rejects("fn example(value:?int){let item=value ?? return}", "E0710");
    rejects(
        "fn example(value:Result<int,str>){let item=value ?? 0}",
        "E0711",
    );
    accepts("fn example(value:?(fn()->int))->int{(value ?? (\\->{return 1}))()}");
}

#[test]
fn constructor_refinements_preserve_their_tag_and_payload_test_boundary() {
    rejects(
        "type Shape {Circle(int),Point}\nfn example(shape:Shape){if shape is Shape::Circle{if shape is Shape::Point{}}}",
        "E0311",
    );
    accepts(
        "type Shape {Circle(int),Point}\nfn example(shape:Shape){if shape is Shape::Circle{}else if shape is Shape::Point{}}",
    );
    accepts("fn example(value:?int){if value is Some(1){}else if value is Some(2){}}");
    rejects(
        "fn example(value:?int){if value is Some(1){}else{let number=value+1}}",
        "E0310",
    );
}

#[test]
fn block_local_named_functions_keep_their_lexical_environment_capabilities() {
    rejects(
        "type Action=fn()->int &closure\nfn make()->Action{let value=7;action\nwhere fn action()->int &{closure,value}{value}}",
        "E0510",
    );
    accepts(
        "type Action=fn()->int &closure\nfn make()->Action &capture{let value=7;action\nwhere fn action()->int &{closure,value}{value}}",
    );
    rejects(
        "fn example(){let value=7;let copy=clone(action)\nwhere fn action()->int &{closure,value}{value}}",
        "E0530",
    );
    accepts(
        "type Action=fn()->int &closure\nfn make()->Action &capture{var count=0;action\nwhere fn action()->int &{closure,mut count}{count+=1;count}}\nfn example(){let mut action=make();assert(action()==1)}",
    );
    rejects(
        "type Resource={on_close:fn()->()}\nfn make()->(fn()->Resource) &capture{let scoped resource=Resource.{on_close:\\->()};action\nwhere fn action()->Resource &{closure,resource}{resource}}",
        "E0604",
    );
}

#[test]
fn local_signature_types_and_mutual_named_recursion_are_checked() {
    accepts("fn example()->Token where type Token=int {1}");
    accepts(
        "fn parity(value:int)->bool{even(value)\nwhere fn even(value:int)->bool{if value==0{true}else{odd(value-1)}}\nfn odd(value:int)->bool{if value==0{false}else{even(value-1)}}}\npub fn test_native(){assert(parity(10)&&!parity(9))}",
    );
}

#[test]
fn propagation_keeps_failure_returns_and_result_obligations_separate() {
    accepts("fn example(value:Result<int,str>)->Result<int,str>{Ok(value?)}");
    accepts("fn example(value:?int)->?int{Some(value?+1)}");
    accepts("fn example()->?int{let value=Some(42)?;Some(value)}");
    rejects(
        "fn example(value:Result<int,str>)->Result<int,int>{Ok(value?)}",
        "E0713",
    );
    rejects("fn example(value:?int)->int{value?}", "E0713");
    rejects("fn example()->?int{let value=42?;Some(value)}", "E0712");
    rejects("let VALUE=Some(1)?", "E0205");
    rejects(
        "fn example(value:?int)->?int{let pending:Result<int,str>=Err(\"unseen\");let number=value?;assert(pending is Err(_));Some(number)}",
        "E0720",
    );
    accepts("fn example()->Result<int,str>{let value:Result<int,str>=Err(\"bad\");Ok(value?)}");
}

#[test]
fn result_payload_witnesses_keep_receipt_and_do_not_make_wrappers_callable() {
    rejects(
        "type Cell={mut value:int}\nfn choose(flag:bool,cell:Cell)->Result<Cell,str>{if flag{Ok(cell)}else{Err(\"bad\")}}\nfn example(flag:bool){let cell=Cell.{value:0};let mut alias=choose(flag,cell) ?? \\_error->panic(\"bad\");alias.value+=1}",
        "E0528",
    );
    rejects(
        "fn example(){let result:Result<fn()->int,str>=Ok(\\->1);let number=result();assert(result is Ok(_))}",
        "E0338",
    );
    accepts(
        "fn example(){let timestamp=Time::timestamp(1i64,0u32) ?? \\_error->panic(\"bad\");assert(timestamp.seconds==1i64)}",
    );
}
#[test]
fn borrowed_named_environment_retains_actual_capture_participants() {
    rejects(
        "type Cell={mut value:int}\nfn apply(mut action:fn()->(),mut cell:Cell)&mut{action();cell.value+=1}\nfn example(){let mut cell=Cell.{value:0};let mut action=helper;apply(mut action,mut cell)\nwhere fn helper() &{closure,mut cell}{cell.value+=1}}",
        "E0523",
    );
    accepts(
        "fn example()->int{var count=1;{let count=9;assert(helper()==1)};count+=1;count\nwhere fn helper()->int &{closure,count}{count}}",
    );
}

#[test]
fn optional_fallback_and_safe_projection_never_restore_published_payload_authority() {
    rejects(
        "type Cell={mut value:int}\nfn example(){let wrapped=Some(Cell.{value:0});let mut item=wrapped ?? panic(\"bad\");item.value+=1}",
        "E0520",
    );
    rejects(
        "type Cell={mut value:int}\nfn example(){let wrapped=Some(.{child:Cell.{value:0}});let mut item=wrapped?.child ?? panic(\"bad\");item.value+=1}",
        "E0520",
    );
    rejects(
        "fn example(){var count=0;let tuple=(panic(\"stop\"),{count=1;()})}",
        "E0527",
    );
    rejects(
        "fn example(){var count=0;let record=.{stop:panic(\"stop\"),later:{count=1;()}}}",
        "E0527",
    );
    rejects(
        "fn example(){with Fiber::yield()->resume();println(\"x\")}",
        "E0612",
    );
}

#[test]
fn declaration_data_is_readonly_contract_storage_without_an_initializer() {
    let parsed = ril_syntax::parse_file("pub let VALUE:int", FileId(9));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let outcome = super::analyze_project(&parsed.program, FileId(9), &[FileId(9)]);
    assert!(
        outcome.program.is_some(),
        "{:?} {:?}",
        outcome.diagnostics,
        outcome.unsupported
    );
    let facts = outcome.program.unwrap();
    let value = &facts.facts().bindings[0].value;
    assert_eq!(value.permission, super::facts::Permission::Read);
    assert!(!value.construction);
}

#[test]
fn fixed_array_cardinality_is_checked_at_every_callable_boundary() {
    rejects("fn wrong()->[2]int{[1]}", "E0301");
    rejects("fn take(value:[2]int){}\nfn example(){take([1])}", "E0301");
    accepts(
        "fn identity(value:[2]int)->[2]int{value}\nfn example(){let values:[2]int=identity([1,2])}",
    );
    let unknown = check("fn claim(value:[]int)->[0]int{value}");
    assert!(unknown.program.is_none());
    rejects("let VALUE=Clock::now()", "E0202");
    rejects("var count=0\nlet VALUE={count+=1;count}", "E0202");
}

#[test]
fn optional_lookup_cannot_return_or_waive_a_result_that_was_not_found() {
    rejects(
        "fn example()->?Result<int,str>{let result:Result<int,str>=Err(\"bad\");let values=[result];values?[99]}",
        "E0720",
    );
    rejects(
        "fn example(){let result:Result<int,str>=Err(\"bad\");let values=[result];let found=values?[99];match found{Some(value)->{assert(value is Err(_))},None->()}}",
        "E0720",
    );
}

#[test]
fn named_environment_creation_cannot_hide_an_uninitialized_capture() {
    rejects(
        "fn example(){let copy=clone(helper);let value=7;assert(copy()==7)\nwhere fn helper()->int &{closure,value}{value}}",
        "E0207",
    );
    accepts("let VALUE=7\nlet COPIED=read()\nfn read()->int &{VALUE}{VALUE}");
    accepts("let ACTION=read\nlet VALUE=7\nfn read()->int &{VALUE}{VALUE}");
    rejects(
        "let COPIED=read()\nlet VALUE=7\nfn read()->int &{VALUE}{VALUE}",
        "E0207",
    );
}

#[test]
fn unresolved_standard_contracts_keep_the_resolved_export_identity() {
    let outcome = check("fn example() @Fiber{let arguments=Env::args()}");
    assert!(
        !outcome
            .diagnostics
            .iter()
            .any(|diagnostic| matches!(diagnostic.code.as_str(), "E0204" | "E0338")),
        "{:?}",
        outcome.diagnostics
    );
    assert!(outcome.program.is_some() || !outcome.unsupported.is_empty());
    rejects("fn example(){Array::made_up()}", "E0204");
    rejects(
        "fn example(){let mut values=[1];let count=len(mut values)}",
        "E0405",
    );
}

#[test]
fn result_tag_refinement_projects_only_its_proved_payload_product() {
    accepts("fn example(result:Result<int,str>)->int{if result is Ok(_){result.0}else{0}}");
    accepts(
        "fn example(result:Result<(int,int),str>)->int{if result is Ok(_,_){result.0+result.1}else{0}}",
    );
    rejects("fn example(result:Result<int,str>)->int{result.0}", "E0337");
    rejects(
        "fn example(result:Result<int,str>)->int{if result is Ok(_){result+1}else{0}}",
        "E0327",
    );
}

#[test]
fn empty_iteration_does_not_count_unreachable_writes_or_result_producers() {
    rejects(
        "fn example(){var count=0;let values:[]int=[];for values as number{count+=number}}",
        "E0527",
    );
    accepts(
        "fn example(){let values:[]int=[];for values as number{let result:Result<int,str>=Ok(number);assert(result is Ok(_))}}",
    );
    rejects(
        "fn example(){let wrapped=Some(1);let selected:i8=wrapped ?? panic(\"empty\")}",
        "E0301",
    );
    rejects(
        "fn example(){let wrapped:Result<int,str>=Ok(1);if wrapped is Ok(_){let selected:i8=wrapped.0}}",
        "E0301",
    );
}

#[test]
fn result_branch_holes_keep_each_payload_type_and_reference_reception() {
    accepts(
        "fn read(flag:bool)->int{let result=if flag{Ok((6,7))}else{Err(\"failure\")};if result is Ok(_){result.0+result.1}else{assert(result.0==\"failure\");0}}\nfn example(){assert(read(true)==13);assert(read(false)==0)}",
    );
}

#[test]
fn universal_clone_needs_copy_eligibility_for_every_generic_constituent() {
    for source in [
        "fn copied<T>(value:T)->T{clone(value)}",
        "fn copied<T>(value:[]T)->[]T{clone(value)}",
        "fn copied<T>(value:{item:T})->{item:T}{clone(value)}",
    ] {
        let outcome = check(source);
        assert!(outcome.program.is_none());
        assert!(!outcome.unsupported.is_empty());
    }
}

#[test]
fn retained_writers_and_result_membership_cannot_escape_through_unchecked_slot_updates() {
    rejects(
        "type Cell={mut value:int}\ntype Holder={mut child:Cell}\nfn store(mut holder:Holder,^mut cell:Cell)&mut{holder.child=^mut cell}",
        "E0510",
    );
    accepts(
        "type Cell={mut value:int}\ntype Holder={mut child:Cell}\nfn store(mut holder:Holder,^mut cell:Cell)&^mut{holder.child=^mut cell}",
    );
    accepts(
        "type Cell={mut value:int}\ntype Holder={mut child:Cell}\nfn store(mut holder:Holder)&mut{holder.child=Cell.{value:2}}",
    );
    let outcome = check(
        "type Holder={mut result:Result<int,str>}\nfn bad()->Holder{let lost:Result<int,str>=Err(\"lost\");let replacement:Result<int,str>=Ok(1);assert(replacement is Ok(_));let mut holder=Holder.{result:lost};holder.result=replacement;holder}",
    );
    assert!(outcome.program.is_none());
    assert!(!outcome.unsupported.is_empty());
    // A complete formal carrier now includes its member's Result duty. The
    // ordinary copy path creates a separate family and remaps copied fields;
    // actual source/copy inspection independence is covered in result_exits.
    accepts("fn copied(source:{result:Result<int,str>})->{result:Result<int,str>}{clone(source)}");
}

#[test]
fn compound_updates_do_not_fabricate_scalar_constants_or_operator_contracts() {
    rejects("fn example(){var flag=true;flag+=false}", "E0327");
    rejects("fn example(){var value=1.0;value<<=2.0}", "E0327");
    let outcome = check(
        "type Cell={mut value:int}\nfn example(){let cell=Cell.{value:0};var current:?Cell=Some(cell);var count=0;let mut step=\\_:int->{count+=1;if count==2{current=Some(Cell.{value:2})}};Array::for_each([1,2],mut step)}",
    );
    assert!(
        outcome.program.is_none(),
        "repeated state changes must not be proved from only the first invocation"
    );
}

#[test]
fn a_callable_return_does_not_cancel_its_callers_remaining_statements() {
    rejects(
        "var count=0\nfn bad(){let action=\\->{return};action();count+=1}",
        "E0510",
    );
    accepts("var count=0\nfn good() &{mut count}{let action=\\->{return};action();count+=1}");
    rejects("fn bad(flag:bool)->int{if flag{return 1}}", "E0301");
    accepts("fn good(flag:bool)->int{if flag{return 1};2}");
    accepts("fn example(){let action=\\->{return 7};assert(action()==7)}");
}

#[test]
fn unknown_callbacks_forget_mutable_scalar_fields_as_well_as_variable_slots() {
    accepts(
        "type Flag={mut value:bool}\nfn example(mut flag:Flag,action:fn()->())&mut{flag.value=false;action();if flag.value{flag.value=true}}",
    );
}

#[test]
fn operators_and_dead_short_circuit_paths_keep_ordinary_type_obligations() {
    rejects("fn example(){let value=1.0 & 2.0}", "E0327");
    rejects("fn example(){let value=~1.0}", "E0327");
    rejects("fn example(){let value=true<false}", "E0327");
    rejects("fn example(){let value=false && missing}", "E0204");
    rejects("fn example(){let value=true || 42}", "E0350");
    rejects("fn example(){if 42{}}", "E0350");
    rejects(
        "fn example(){var count=0;let value=if panic(\"stop\"){count+=1}else{()}}",
        "E0527",
    );
}

#[test]
fn contextual_callable_validation_does_not_execute_the_closure_or_coerce_a_descriptor_to_data() {
    rejects(
        "fn example(){let result:Result<int,str>=Err(\"unseen\");let callback:fn(int)->bool=\\_ -> result is Err(_)}",
        "E0720",
    );
    rejects("fn example(){let number:int=len;let sum=number+1}", "E0301");
    rejects(
        "fn example(){let pair:(int,int)=(len,1);let sum=pair.0+1}",
        "E0301",
    );
}

#[test]
fn cached_numeric_context_cannot_revive_an_early_return() {
    accepts(
        "fn read(item:?{id:int})->int{if item==None{return -1};item.id}\nfn example(){assert(read(Some(.{id:7}))==7);assert(read(None)==-1)}",
    );
    accepts(
        "fn read(item:?int)->int{let Some(value)=item else{return -1};value}\nfn example(){assert(read(Some(7))==7);assert(read(None)==-1)}",
    );
}

#[test]
fn one_invocation_uses_one_substitution_for_every_occurrence_of_a_binder() {
    rejects(
        "fn choose<T>(a:T,b:T)->T{a}\nfn example(){let _=choose(1,\"wrong\")}",
        "E0301",
    );
    rejects(
        "fn choose<T>(a:T,b:T)->T{a}\nfn example(){let _=choose(1i8,2i16)}",
        "E0301",
    );
    rejects(
        "fn choose<T>(a:T,b:T)->T{a}\nfn bad<T,U>(a:T,b:U)->T{choose(a,b)}",
        "E0301",
    );
    accepts(
        "fn identity<T>(value:T)->T{value}\nfn example(){let number=identity(7);let word=identity(\"word\");assert(number==7);assert(word==\"word\")}",
    );
    accepts(
        "fn choose<T>(a:T,b:T)->T{a}\nfn example(){let value:i8=choose(1,2i8);assert(value==1i8)}",
    );
    accepts(
        "type Number=int\nfn first<T>(value:(T,T))->T{value.0}\nfn example(){let number:Number=first((1,2));assert(number==1)}",
    );
}

#[test]
fn anonymous_annotations_and_callable_type_rows_retain_their_constraints() {
    rejects(r"fn example(){let action=\-> &{} ()}", "E0542");
    rejects(
        r"type Action=fn()->()
eff Log{write()->()}
fn logged() @Log{Log::write()}
fn example() @Log{let invoke=\action:Action -> @{} &{} action();invoke(logged)}",
        "E0534",
    );
    accepts(
        r"type Action=fn()->()
fn plain(){}
fn example(){let invoke=\action:Action -> @{} &{} action();invoke(plain)}",
    );
    rejects(
        r"type Action=fn()->()
type PureInvoker=fn(Action)->() @{} &{}
eff Log{write()->()}
fn logged() @Log{Log::write()}
fn invoke(action:Action){action()}
fn example() @Log{let checked:PureInvoker=invoke;checked(logged)}",
        "E0534",
    );
    rejects(
        r"type Bounded=fn()->() @Fiber
eff Log{write()->()}
fn logged() @Log{Log::write()}
fn example(){let unused:Bounded=logged}",
        "E0534",
    );
    accepts(
        r"type Action=fn()->()
type PureInvoker=fn(Action)->() @{} &{}
fn plain(){}
fn invoke(action:Action){action()}
fn example(){let checked:PureInvoker=invoke;checked(plain)}",
    );
    accepts(
        r"eff First{get()->int}
fn apply(action:fn()->int)->int{action()}
fn example()->int @First{apply(First::get)}",
    );
}

#[test]
fn file_resource_authority_stays_nonordinary_at_every_reachable_depth() {
    accepts(
        r#"fn example() @Fiber{let scoped mut file=File::open("unused-path") ?? \_ -> panic("open");let result=File::read_chunk(mut file,4);assert(result is Ok(_))}"#,
    );
    rejects(
        r#"fn example() @Fiber{let file=File::open("unused-path") ?? \_ -> panic("open");let copy=clone((file,))}"#,
        "E0530",
    );
    rejects(
        r#"fn example() @Fiber{let file=File::open("unused-path") ?? \_ -> panic("open");let copy=clone_immut(.{file:file})}"#,
        "E0530",
    );
    rejects(
        r#"fn example() @Fiber{let file=File::open("unused-path") ?? \_ -> panic("open");let copy=file |> derive \mut draft -> ()}"#,
        "E0536",
    );
    rejects(
        r#"fn example() @Fiber{let file=File::open("unused-path") ?? \_ -> panic("open");assert((file,)==(file,))}"#,
        "E0327",
    );
    rejects(
        r#"fn example() @Fiber{let scoped file=File::open("unused-path") ?? \_ -> panic("open")}"#,
        "E0520",
    );
    rejects(
        r#"fn example() @Fiber{let file=File::open("unused-path") ?? \_ -> panic("open");let result=File::close(mut file);assert(result is Ok(_))}"#,
        "E0520",
    );
    accepts(
        r#"fn example(){let scoped resource=.{on_close:\->()};let copy=clone(.{resource:resource})}"#,
    );
}

#[test]
fn nested_callable_bounds_check_fields_payloads_and_returned_values() {
    rejects(
        "eff Log{write()->()}
fn logged() @Log{Log::write()}
fn example(){let holder:{action:fn()->() @Fiber}=.{action:logged}}",
        "E0534",
    );
    rejects(
        "eff Log{write()->()}
fn logged() @Log{Log::write()}
fn example(){let holder:[]fn()->() @Fiber=[logged]}",
        "E0534",
    );
    rejects(
        "eff Log{write()->()}
fn logged() @Log{Log::write()}
fn example(){let holder:?fn()->() @Fiber=Some(logged)}",
        "E0534",
    );
    rejects(
        "eff Log{write()->()}
fn logged() @Log{Log::write()}
fn make()->(fn()->() @Fiber){logged}",
        "E0534",
    );
    accepts(
        "fn plain(){}
fn example(){let holder:{action:fn()->() @Fiber}=.{action:plain};holder.action()}",
    );
}

#[test]
fn conditional_outer_result_returns_export_one_confined_producer_family() {
    accepts(
        r#"fn fallible(value:Result<int,str>)->Result<int,str>{let item=value?;Ok(item+1)}
fn example(){assert(fallible(Ok(6)) is Ok(7));assert(fallible(Err("failed")) is Err("failed"))}"#,
    );
    accepts(
        r#"fn read(flag:bool)->Result<int,str>{let first=if flag{Ok(1)}else{Err("failed")};let number=first?;Ok(number+1)}
fn example(flag:bool){assert(read(flag) is Ok(_))}"#,
    );
    rejects(
        r#"fn read(flag:bool)->Result<int,str>{let first=if flag{Ok(1)}else{Err("failed")};let number=first?;Ok(number+1)}
fn example(flag:bool){let ignored=read(flag)}"#,
        "E0720",
    );
    rejects(
        r#"fn read(flag:bool)->Result<Result<int,str>,str>{let first=if flag{Ok(1)}else{Err("failed")};let number=first?;Ok(Err("nested"))}
fn example(flag:bool){assert(read(flag) is Ok(_))}"#,
        "E0720",
    );
}

#[test]
fn inferred_generic_identity_cannot_erase_selected_dimensions_or_callable_modes() {
    for source in [
        "fn choose<T>(a:T,b:T)->T{a}
fn example(){let a:[2]int=[1,2];let b:[3]int=[1,2,3];let chosen=choose(a,b)}",
        "type Cell={mut value:int}
fn borrow(mut cell:Cell)&mut{cell.value+=1}
fn retained(^mut cell:Cell)&mut{cell.value+=1}
fn choose<T>(a:T,b:T)->T{a}
fn example(){let chosen=choose(borrow,retained)}",
    ] {
        let outcome = check(source);
        assert!(outcome.program.is_none());
        assert!(
            outcome
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0301"),
            "{:?} {:?}",
            outcome.diagnostics,
            outcome.unsupported
        );
    }
    accepts(
        "fn choose<T>(a:T,b:T)->T{a}
fn example(){let chosen=choose([1,2],[1,2,3]);assert(chosen==[1,2])}",
    );
}

#[test]
fn the_nullary_none_descriptor_is_not_an_optional_callable() {
    rejects("fn example(){let invalid=None()}", "E0353");
    rejects("fn example(){let alias:?(fn()->())=None;alias()}", "E0310");
}

#[test]
fn lazy_value_tests_keep_existing_mutable_closure_capture_paths() {
    accepts(
        r#"fn example(){let mut trace:[]int=[];let mut mark=\n->{trace !> Array::push(n);n};let result:Result<int,str>=Ok(1);assert(result is Ok(mark(0)) | Ok(mark(1)) | Ok(mark(2)));assert(trace==[0,1])}"#,
    );
}

#[test]
fn anonymous_parameter_loans_and_retention_survive_return_boundaries() {
    rejects(
        r#"type Cell={mut value:int}
fn example(){let mut cell=Cell.{value:0};cell.value+=1;let identity=\mut value:Cell->value;let mut result=^mut identity(mut cell);result.value+=1}"#,
        "E0528",
    );
    accepts(
        r#"type Cell={mut value:int}
fn example(){let mut cell=Cell.{value:0};let retain=\^mut value:Cell->value;let mut result=retain(^mut cell);result.value+=1;cell.value+=1}"#,
    );
}

#[test]
fn with_file_lends_one_temporary_handle_and_preserves_result_duties() {
    accepts(
        r#"fn read(mut file:File::Handle)->Result<Io::ReadChunk,Io::IoError> @Fiber &mut{File::read_chunk(mut file,3)}
fn example() @Fiber{let path=Path::from_string("unused");assert(File::with_file(path,File::OpenMode::Read,read) is Ok(_));assert(File::with_file(path,File::OpenMode::Read,\mut file->File::read_chunk(mut file,0)) is Ok(_))}"#,
    );
    rejects(
        r#"fn escaped(mut file:File::Handle)->Result<File::Handle,Io::IoError> @Fiber &mut{let checked=File::sync(mut file);assert(checked is Ok());Ok(file)}
fn example() @Fiber{let path=Path::from_string("unused");assert(File::with_file(path,File::OpenMode::Read,escaped) is Ok(_))}"#,
        "E0604",
    );
    rejects(
        r#"fn example() @Fiber{let path=Path::from_string("unused");let result=File::with_file(path,File::OpenMode::Read,\mut file->File::read_chunk(mut file,0))}"#,
        "E0720",
    );
    rejects(
        r#"fn action(mut file:File::Handle)->Result<Result<int,str>,Io::IoError> @Fiber &mut{let checked=File::sync(mut file);assert(checked is Ok());Ok(Err("nested"))}
fn example() @Fiber{let path=Path::from_string("unused");assert(File::with_file(path,File::OpenMode::Read,action) is Ok(_))}"#,
        "E0720",
    );
    rejects(
        r#"fn example() @Fiber{let older:Result<int,str>=Ok(1);let path=Path::from_string("unused");assert(File::with_file(path,File::OpenMode::Read,\mut file->{assert(older is Ok(_));File::read_chunk(mut file,0)}) is Ok(_))}"#,
        "E0720",
    );
}

#[test]
fn nested_factory_calls_cannot_hide_a_new_surviving_environment() {
    rejects(
        r#"fn make()->(fn()->int) &capture{let saved=7;\->saved}
fn hidden()->(fn()->int){let result=make();result}"#,
        "E0510",
    );
    accepts(
        r#"fn make()->(fn()->int) &capture{let saved=7;\->saved}
fn visible()->(fn()->int) &capture{let result=make();result}
fn example(){let action=visible();assert(action()==7)}"#,
    );
}

#[test]
fn a_file_resource_identity_cannot_alias_an_ordinary_scalar_cell() {
    accepts(
        r#"var calls=0
eff Read{count()->int}
fn read(mut file:File::Handle)->Result<Io::ReadChunk,Io::IoError> @Fiber &mut &{mut calls}{with Read::count()->resume 3;calls+=1;File::read_chunk(mut file,Read::count())}"#,
    );
}

#[test]
fn collection_element_constraints_survive_aliases_and_later_writes() {
    rejects(
        r#"fn example(){let mut mapping=[:];Map::set(mut mapping,"key",1);let missing=mapping[42]}"#,
        "E0301",
    );
    rejects(
        r#"fn example(){let mut values=[];Array::push(mut values,1);assert(true in values)}"#,
        "E0301",
    );
    rejects(
        r#"fn example(){let mut values=[];var holder=.{items:values};var typed:{items:[]int}=holder;Array::push(mut values,"wrong");holder=holder;typed=typed;let selected:int=typed.items[0]}"#,
        "E0301",
    );
    rejects(
        r#"fn example(){let mut values=[];Array::push(mut values,1);Array::push(mut values,"wrong");let selected:int=values[0]}"#,
        "E0301",
    );
    rejects(
        r#"fn example(){let mut values=[];let view typed:[]int=values;Array::push(mut values,"wrong");let selected:int=typed[0]}"#,
        "E0301",
    );
}

#[test]
fn derive_initial_writes_are_confined_and_cannot_publish_resource_or_writer_aliases() {
    accepts(
        r#"fn example(){let original=.{count:1};let changed=original |> derive \mut draft->{draft.count=2};assert(original.count==1&&changed.count==2)}"#,
    );
    rejects(
        r#"fn example(){let original=.{count:1};let changed=original |> derive \mut draft->{draft.count=2;7}}"#,
        "E0301",
    );
    rejects(
        r#"fn example() @Fiber{let file=File::open("unused") ?? \_ -> panic("open");let original=[];let changed=original |> derive \mut draft->{Array::push(mut draft,file)}}"#,
        "E0536",
    );
    rejects("fn example(){Array::push(mut [1],2u8)}", "E0410");
    rejects(
        "fn take(value:int){}
fn example(){let action=\\value:i8->take(value);action(1i8)}",
        "E0301",
    );
}

#[test]
fn range_endpoints_keep_one_selected_integer_family_and_do_not_promote_bound_values() {
    accepts(
        "fn example(){for 126i8..=127i8 as number{assert(number>=126i8)};for 0u64..=18446744073709551615u64 as number{assert(number>=0u64);last};for 1000000000000000000000000000000bigint..=1000000000000000000000000000001bigint as number{assert(number>=0bigint);last}}",
    );
    rejects(
        "fn example(){let start=1;let end=2i8;for start..end as number{}}",
        "E0301",
    );
    rejects("fn example(){for 1.0..2.0 as number{}}", "E0327");
    rejects("fn example(){let count=len(0..4)}", "E0301");
    accepts("fn example(){for 1..2i8 as number{assert(number==1i8)}}");
}

#[test]
fn asynchronous_system_aliases_do_not_cover_user_effects_or_unknown_names() {
    rejects(
        "eff Log{write()->()}
fn hidden() @Async{Log::write()}",
        "E0612",
    );
    rejects("fn hidden() @Missing{}", "E0204");
    rejects(
        "eff Read{get()->int}
fn hidden(){let value=Read::made_up()}",
        "E0204",
    );
    accepts(
        "eff Log{write()->()}
eff Logging{Log}
fn visible() @Logging{Log::write()}",
    );
    accepts("fn visible() @Async{Fiber::yield()}");
}

#[test]
fn resumed_arm_cleanup_cannot_change_a_guard_before_the_continuation_runs() {
    rejects(
        r#"type Cell={mut value:int}
type Guard={mut on_close:fn()->()}
eff Tick{go()->()}
fn swap(mut a:Cell,mut b:Cell)&mut{a.value+=1;b.value+=1}
fn example(){let mut a=Cell.{value:0};let mut b=Cell.{value:0};b.value+=0;var same=true;with Tick::go()->{let scoped mut guard=Guard.{on_close:\->{same=false}};resume()};Tick::go();let mut second=if same{^mut a}else{^mut b};swap(mut a,mut second)}"#,
        "E0523",
    );
}

#[test]
fn resumed_cleanup_checks_results_after_the_actual_continuation_and_runs_once() {
    rejects(
        r#"type Guard={mut on_close:fn()->()}
eff Tick{go()->()}
fn example(){let result:Result<int,str>=Ok(1);var inspect=true;with Tick::go()->{let scoped mut guard=Guard.{on_close:\->{if inspect{assert(result is Ok(_))}}};resume()};Tick::go();inspect=false}"#,
        "E0720",
    );
    accepts(
        r#"type Guard={mut on_close:fn()->()}
var flag=true
fn close() &{mut flag}{flag=!flag}
fn early() &{mut flag}{let scoped guard=Guard.{on_close:close};return}
fn example() &{mut flag}{early();assert(!flag)}"#,
    );
}

#[test]
fn repeated_resumed_cleanup_needs_an_activation_multiplicity_proof() {
    let outcome = check(
        r#"type Guard={mut on_close:fn()->()}
eff Tick{go()->()}
var flag=true
fn close() &{mut flag}{flag=!flag}
fn many() &{mut flag}{with Tick::go()->{let scoped guard=Guard.{on_close:close};resume()};for [1,2] as number{Tick::go()}}"#,
    );
    assert!(outcome.program.is_none());
    assert!(!outcome.unsupported.is_empty());
}

#[test]
fn deferred_arm_authority_cannot_escape_its_continuation_boundary() {
    rejects(
        r#"type Guard={on_close:fn()->()}
eff Supply{get()->Guard}
fn example()->Guard{with Supply::get()->{let scoped guard=Guard.{on_close:\->()};resume guard};Supply::get()}"#,
        "E0604",
    );
    accepts(
        r#"type Guard={on_close:fn()->()}
fn example()->{items:[]Guard}{let scoped guard=Guard.{on_close:\->()};clone(.{items:[guard]})}"#,
    );
}

#[test]
fn typed_record_literals_do_not_mint_opaque_authority_or_erase_callback_modes() {
    rejects(
        "fn example(){let scoped mut forged=File::Handle.{}}",
        "E0907",
    );
    rejects("fn example(){let forged=Process::Child.{}}", "E0907");
    rejects(
        "type Wrapped({value:int})
fn example(){let forged=Wrapped.{value:1}}",
        "E0301",
    );
    rejects(
        "type Cell={mut value:int}
type Ops={run:fn(mut Cell)->()}
fn readonly(cell:Cell){}
fn example(){let erased=Ops.{run:readonly}}",
        "E0407",
    );
}

#[test]
fn with_child_lends_temporary_authority_without_granting_source_scoped_cleanup() {
    accepts(
        r#"fn wait(mut child:Process::Child)->Result<Process::ExitStatus,Process::ProcessError> @Fiber &mut{Process::wait(mut child)}
fn example() @Fiber{let command=Process::command(Path::from_string("unused"),[]);assert(Process::with_child(command,wait) is Ok(_))}"#,
    );
    rejects(
        r#"fn escape(mut child:Process::Child)->Result<Process::Child,Process::ProcessError> @Fiber &mut{let status=Process::wait(mut child);assert(status is Ok(_));Ok(child)}
fn example() @Fiber{let command=Process::command(Path::from_string("unused"),[]);assert(Process::with_child(command,escape) is Ok(_))}"#,
        "E0604",
    );
    rejects(
        r#"fn example() @Fiber{let command=Process::command(Path::from_string("unused"),[]);let scoped mut child=Process::spawn(command) ?? \_ -> panic("spawn")}"#,
        "E0541",
    );
    rejects(
        r#"fn example() @Fiber{let command=Process::command(Path::from_string("unused"),[]);let result=Process::with_child(command,\mut child->Process::wait(mut child))}"#,
        "E0720",
    );
}

#[test]
fn standard_stream_callable_descriptors_preserve_modes_effects_and_bounds() {
    accepts(
        "type Reader=fn(mut File::Handle,int)->Result<Io::ReadChunk,Io::IoError> @Fiber &mut
fn example(){let action:Reader=File::read_chunk}",
    );
    rejects(
        "type Missing=fn(mut File::Handle,int)->Result<Io::ReadChunk,Io::IoError> @Fiber &closure
fn example(){let action:Missing=File::read_chunk}",
        "E0534",
    );
    rejects(
        "type ReadOnly=fn(File::Handle,int)->Result<Io::ReadChunk,Io::IoError> @Fiber
fn example(){let action:ReadOnly=File::read_chunk}",
        "E0407",
    );
}

#[test]
fn definition_checks_keep_residual_effects_separate_from_performed_operations() {
    let result = check(
        "eff Read{get()->int}\npub fn pending()->int @Read{Read::get()}\npub fn handled()->int{with Read::get()->resume 1;Read::get()}",
    );
    let program = result.program.expect("checked library definitions");
    let facts = program.facts();
    let pending = facts
        .definition_checks
        .iter()
        .find(|check| facts.functions[check.function].syntax.name == "pending")
        .unwrap();
    let handled = facts
        .definition_checks
        .iter()
        .find(|check| facts.functions[check.function].syntax.name == "handled")
        .unwrap();
    assert_eq!(pending.returned, Ty::Int("int".into()));
    assert!(!pending.invocation.effects.is_empty());
    assert!(handled.invocation.effects.is_empty());
    assert!(!handled.invocation.performed_operations.is_empty());
}

#[test]
fn universal_definitions_cannot_use_a_mutable_global_initializer_as_a_branch_proof() {
    rejects(
        "var enabled=false\neff Read{get()->int}\npub fn enable() &{mut enabled}{enabled=true}\npub fn hidden()->int &{enabled}{if enabled{Read::get()}else{0}}",
        "E0612",
    );
    rejects(
        "eff Read{get()->int}\ntype Action=fn()->int @Fiber &closure\nfn example(){var enabled=false;let view action:Action=\\->if enabled{Read::get()}else{0};enabled=true}",
        "E0534",
    );
}

#[test]
fn non_tail_resumption_uses_the_actual_answer_and_post_continuation_state() {
    accepts(
        "eff Read{get()->int}\nfn read()->int{with Read::get()->{let answer=resume 2;answer+5};Read::get()+1}",
    );
    accepts(
        "eff Read{get()->int}\nfn read()->int{with Read::get()->{let answer=resume 1;answer+10};Read::get()+Read::get()}",
    );
    accepts(
        "eff Tick{go()->()}\nfn read()->int{with Tick::go()->{let result=Ok(1);let answer=resume();assert(result is Ok(_));answer};Tick::go();7}",
    );
    rejects(
        "eff Tick{go()->()}\nfn read()->int{var inspect=true;with Tick::go()->{let result=Ok(1);let answer=resume();if inspect{assert(result is Ok(_))};answer};Tick::go();inspect=false;7}",
        "E0720",
    );
    accepts(
        "eff Tick{go()->()}\nfn read()->int{var stage=0;with Tick::go()->{let before=stage;let answer=resume();assert(stage==2);stage=3;answer+before};stage=1;Tick::go();stage=2;7}",
    );
    accepts(
        r#"type Guard={mut on_close:fn()->()}
eff Tick{go()->()}
fn read()->int{var stage=0;with Tick::go()->{let scoped mut arm=Guard.{on_close:\->{stage=3}};let answer=resume();assert(stage==2);answer+1};let scoped mut body=Guard.{on_close:\->{stage=2}};Tick::go();stage=1;7}"#,
    );
    rejects(
        "type Cell={mut value:int}\neff Edit{apply(mut Cell)->() &mut}\nfn edit(mut cell:Cell)->int &mut{with Edit::apply(mut item)->{item.value+=1;let answer=resume();item.value+=1;answer};Edit::apply(mut cell);cell.value}",
        "E0540",
    );
    rejects(
        "eff Read{get()->int}\nfn read()->int{with Read::get()->{let answer=resume 2;\"wrong\"};Read::get()+1}",
        "E0625",
    );
    rejects(
        "type Cell={mut value:int}\neff Tick{go()->()}\nfn swap(mut a:Cell,mut b:Cell)&mut{a.value+=1;b.value+=1}\nfn example()->int{let mut a=Cell.{value:0};let mut b=Cell.{value:0};b.value+=0;var same=false;with Tick::go()->{let answer=resume();let mut second=if same{^mut a}else{^mut b};swap(mut a,mut second);answer};Tick::go();same=true;0}",
        "E0523",
    );
}

#[test]
fn immutable_formal_qualifications_survive_every_nested_shape() {
    for source in [
        "type Cell={mut value:int}\nfn bad(mut frozen:Immut<Cell>) &mut{frozen.value+=1}",
        "type Cell={mut value:int}\nfn bad(mut holder:{child:Immut<Cell>}) &mut{holder.child.value+=1}",
        "type Cell={mut value:int}\nfn bad(mut items:[]Immut<Cell>) &mut{items[0].value+=1}",
        "type Cell={mut value:int}\nfn bad(mut value:?Immut<Cell>) &mut{if value!=None{value.value+=1}}",
    ] {
        let result = check(source);
        assert!(result.program.is_none());
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| matches!(diagnostic.code.as_str(), "E0520" | "E0522")),
            "{:?}",
            result.diagnostics
        );
    }
    accepts(
        "type Cell={mut value:int}\nfn read(value:Immut<{child:Cell}>)->int{value.child.value}",
    );
}

#[test]
fn resumption_results_keep_the_operation_selected_numeric_family() {
    rejects(
        "eff Small{get()->i8}\nfn example(){with Small::get()->resume 1;let selected=Small::get();let wrong:int=selected}",
        "E0301",
    );
    accepts("eff Small{get()->i8}\nfn read()->i8{with Small::get()->resume 1;Small::get()}");
}

#[test]
fn replacing_a_writer_slot_consumes_the_returned_retention_receipt() {
    rejects(
        "type Cell={mut value:int}\nfn retain(^mut value:Cell)->Cell &^mut{value}\nfn example(){let mut cell=Cell.{value:0};var mut current=Cell.{value:1};current=retain(^mut cell);let mut alias=current;alias.value+=1;current.value+=1;cell.value+=1}",
        "E0510",
    );
    accepts(
        "type Cell={mut value:int}\nfn retain(^mut value:Cell)->Cell &^mut{value}\nfn example(){let mut cell=Cell.{value:0};var mut current=Cell.{value:1};current=retain(^mut cell);let mut alias=^mut current;alias.value+=1;current.value+=1;cell.value+=1}",
    );
}

#[test]
fn stream_helpers_use_actual_operation_rows_loans_results_and_repeated_storage() {
    accepts(
        "type Sink={mut data:[]u8}\nfn write(mut sink:Sink,data:bytes)->Io::WriteProgress &mut{sink.data !> Array::push(1u8);.{written:len(data),error:None}}\nfn example(){let mut sink=Sink.{data:[]};assert(Io::write_all(mut sink,b\"abc\",.{write}) is Ok())}",
    );
    rejects(
        "type Reader={mut count:int}\nfn read(mut reader:Reader,maximum:int)->Result<Io::ReadChunk,Io::IoError> &mut{reader.count+=1;Ok(.{data:b\"\",end:true})}\nfn example(){let mut reader=Reader.{count:0};let result=Io::read_all(mut reader,.{read})}",
        "E0720",
    );
    rejects(
        "type Reader={mut count:int}\nfn read(mut reader:Reader,maximum:int)->Result<Io::ReadChunk,Io::IoError> @Fiber &mut{reader.count+=1;Fiber::yield();Ok(.{data:b\"\",end:true})}\nfn example(){let mut reader=Reader.{count:0};assert(Io::read_all(mut reader,.{read}) is Ok(_))}",
        "E0612",
    );
    rejects(
        "type Reader={mut count:int}\nfn read(reader:Reader,maximum:int)->Result<Io::ReadChunk,Io::IoError>{Ok(.{data:b\"\",end:true})}\nfn example(){let mut reader=Reader.{count:0};reader.count+=0;assert(Io::read_all(mut reader,.{read}) is Ok(_))}",
        "E0407",
    );
}

#[test]
fn confined_result_families_preserve_members_and_clone_independence() {
    let definition =
        "fn produce(flag:bool)->Result<int,str>{if flag{Ok(1)}else{Err(\"failure\")}}\n";
    accepts(&format!(
        "{definition}fn example(flag:bool){{for [1,2] as number{{let result=produce(flag);assert(result is Ok(_))}}}}"
    ));
    rejects(
        &format!(
            "{definition}fn example(flag:bool){{let original=produce(flag);let copied=clone(original);assert(copied is Ok(_))}}"
        ),
        "E0720",
    );
    rejects(
        &format!(
            "{definition}fn example(flag:bool){{let original=produce(flag);assert(original is Ok(_));let copied=clone(original)}}"
        ),
        "E0720",
    );
    accepts(&format!(
        "{definition}fn example(flag:bool){{let original=produce(flag);let copied=clone((original,original));assert(copied.0 is Ok(_));assert(original is Ok(_))}}"
    ));
    rejects(
        "fn produce(flag:bool)->Result<Result<int,str>,str>{if flag{Ok(Err(\"inner\"))}else{Err(\"outer\")}}\nfn example(flag:bool){let result=produce(flag);assert(result is Ok(_))}",
        "E0720",
    );
    accepts(
        "fn produce(flag:bool)->Result<int,str>{if flag{return Ok(1)};Err(\"failure\")}\nfn example(flag:bool){for [1,2] as number{let result=produce(flag);assert(result is Ok(_))}}",
    );
    rejects(
        "fn produce(flag:bool)->Result<int,str>{if flag{let lost=Err(\"lost\");return Ok(1)};Ok(2)}",
        "E0720",
    );
    let old = check(
        "fn produce(flag:bool)->Result<int,str>{let old=Err(\"old\");if flag{return Ok(1)};assert(old is Ok(_));Ok(2)}",
    );
    assert!(
        old.program.is_none(),
        "an early return must not waive an existing producer"
    );
}

#[test]
fn static_key_carriers_and_escaping_lambda_types_use_their_defining_binders() {
    let result = check("fn get_field<T:{..R},K:keyof T>(record:T,key:K)->T.(K){record.(K)}");
    let program = result
        .program
        .expect("symbolic static coordinate projection");
    let facts = program.facts();
    let function = &facts.functions[0].syntax;
    assert!(
        facts
            .static_key_parameters
            .iter()
            .any(|parameter| parameter.owner == function.span
                && parameter.parameter == 1
                && parameter.name == "key"
                && facts.generic_binders.contains_key(&parameter.binder))
    );
    accepts(
        "fn make<T>(value:T)->fn(T)->T{\\argument:T->argument}\nfn consume<T>(value:T){let action=make(1);assert(action(2)==2)}",
    );
    rejects(
        "fn make<T>(value:T)->fn(T)->T{\\argument:T->argument}\nfn example(){let action=make(1);let wrong:str=action(2)}",
        "E0301",
    );
}

#[test]
fn result_context_solves_only_the_producing_invocations_unselected_binders() {
    accepts(
        "fn empty<T>()->[]T{[]}\nfn example(){let values:[]int=empty();assert(len(values)==0)}",
    );
    accepts("fn empty<T>()->[]T{[]}\nfn take(values:[]int){}\nfn example(){take(empty())}");
    accepts(
        "fn empty<T>()->[]T{[]}\nfn example(){let values:([]int,[]str)=(empty(),empty());assert(len(values.0)==0)}",
    );
    rejects(
        "fn empty<T>()->[]T{[]}\nfn example(){let values=empty()}",
        "E0344",
    );
    rejects(
        "fn empty<T>()->[]T{[]}\nfn example(){let values=(empty(),1)}",
        "E0344",
    );
    rejects("fn forged<T,U>(value:T)->U{value}", "E0301");
    rejects(
        "fn choose<T>(a:T,b:T)->T{a}\nfn example(){let value:str=choose(1,2)}",
        "E0301",
    );
    rejects(
        "fn empty<T>()->[]T{[]}\nfn ignore<T>(value:[]T){}\nfn example(){ignore(empty())}",
        "E0344",
    );
    rejects(
        "fn empty<T>()->[]T{[]}\nfn example(){let count=len(empty())}",
        "E0344",
    );
    rejects("fn empty<T>()->[]T{[]}\nfn example(){empty();}", "E0344");
    rejects("fn example(){let count=len([:])}", "E0344");
    rejects(
        "fn ignore<K,V>(values:[K:V]){}\nfn example(){ignore([:])}",
        "E0344",
    );
}

#[test]
fn slice_windows_preserve_readonly_backing_and_last_use_stability() {
    accepts(
        "fn example(){let mut items=[1,2];let view window=items[..];assert(len(window)==2);Array::push(mut items,3)}",
    );
    rejects(
        "fn example(){let mut items=[1,2];let view window=items[..];Array::push(mut items,3);assert(len(window)==2)}",
        "E0537",
    );
    accepts(
        "fn example(){let mut items=[1,2];let view window=items[..];items[0]=9;assert(window[0]==9)}",
    );
    rejects(
        "fn example(){let mut items=[1,2];let view window=items[..];window[0]=9;items[0]=2}",
        "E0522",
    );
    rejects(
        "fn example(){var mut items=[1,2];items=[3,4];let view window=items[..];items[0]=2}",
        "E0531",
    );
    accepts(
        "fn example(){let values=[10,20,30];assert(values[..2]==[10,20]);assert(values[1..][..1][0]==20)}",
    );
    let copied =
        check("fn example(){let values=[1,2];let copied=clone(values[..]);assert(len(copied)==2)}");
    assert!(copied.program.is_none() && !copied.unsupported.is_empty());
    rejects(
        "fn example(){let mut items=[1,2];let view window=items[..];let view alias=window;Array::push(mut items,3);assert(alias[0]==1)}",
        "E0537",
    );
    rejects(
        "fn example(){let mut items=[1,2];let view window=items[..];let view reader=\\->len(window);Array::push(mut items,3);assert(reader()==2)}",
        "E0537",
    );
    accepts(
        "fn example(){let mut items=[1,2];let view window=items[..];let view reader=\\->len(window);assert(reader()==2);Array::push(mut items,3)}",
    );
    rejects(
        "fn read(items:[]int)->[]int{items[..]}\nfn example(){let mut items=[1,2];let view window=read(items);Array::push(mut items,3);assert(len(window)==2)}",
        "E0537",
    );
    rejects(
        "type Guard={mut on_close:fn()->()}\nfn example(){let mut items=[1,2];let view window=items[..];let scoped mut guard=Guard.{on_close:\\->{assert(len(window)==2)}};Array::push(mut items,3)}",
        "E0537",
    );
    rejects(
        "fn example(){let mut items=[1,2];let view window=items[..];for window as item{Array::push(mut items,3)}}",
        "E0526",
    );
    let unknown = check(
        "fn example(items:[]int,action:fn()){let view window=items[..];action();assert(len(window)==2)}",
    );
    assert!(unknown.program.is_none() && !unknown.unsupported.is_empty());
    rejects(
        "type Cell={mut value:int}\nfn edit(mut cell:Cell,items:[]Cell)&mut{cell.value+=1;let view window=items[..];assert(window[0].value==1)}\nfn example(){let mut cell=Cell.{value:0};edit(mut cell,[cell])}",
        "E0524",
    );
    rejects(
        "fn example(){let mut items=[1,2];let view window=items[..];let mut aliases=[];Array::push(mut aliases,window);Array::push(mut items,3);assert(len(aliases[0])==2)}",
        "E0537",
    );
    rejects(
        "type Cell={mut value:int}\nfn example(){let mut cell=Cell.{value:0};let mut items=[^mut cell];let view window=items[..];let reversed=Array::reverse(window);cell.value+=1;items[0].value+=0}",
        "E0535",
    );
    rejects(
        "type Cell={mut value:int}\nfn example(mut cell:Cell)&mut{let values=[1];let _=values[panic(\"stop\")..{cell.value+=1;1}]}",
        "E0527",
    );
}

#[test]
fn finite_budget_tracks_actual_coverage_and_separates_recovery_paths() {
    rejects(
        "fn one(){}\nfn example(){var maybe:?{id:int}=None;{with Div::exhausted()->();Div::budget(10,one);maybe=Some(.{id:1});if maybe==None{return};assert(maybe.id==1)};let _=maybe.id}",
        "E0310",
    );
    rejects(
        "type Guard={mut on_close:fn()->()}\nfn forever(){loop{}}\nfn example(){with Div::exhausted()->();let _=Div::budget(10,\\->{let scoped mut guard=Guard.{on_close:\\->{}};guard.on_close=forever})}",
        "E0617",
    );
    rejects(
        "type Cell={mut value:int}\nfn swap(mut a:Cell,mut b:Cell)&mut{a.value+=1;b.value+=1}\nfn one(){}\nfn example(){let mut a=Cell.{value:0};let mut b=Cell.{value:0};var flag=false;{with Div::exhausted()->();Div::budget(10,one);flag=true;return};let mut selected=if flag{^mut b}else{^mut a};swap(mut a,mut selected);b.value+=0}",
        "E0523",
    );
    let checked = check(
        "fn one()->int{1}\nfn example()->?int{with Div::exhausted()->None;Some(Div::budget(1,one))}",
    );
    assert!(
        checked.program.is_some(),
        "{:?} {:?}",
        checked.diagnostics,
        checked.unsupported
    );
    assert!(!checked.program.unwrap().facts().budget_proofs.is_empty());
    accepts(
        "fn spin()->int{loop{}}\nfn example()->?int{with Div::exhausted()->None;Some(Div::budget(20,spin))}",
    );
    accepts(
        "fn spin()->int{loop{}}\nfn example()->?int{with Div::exhausted()->None;with Div::budget(20);Some(spin())}",
    );
    accepts(
        "fn spin()->int{loop{}}\nhalt fn example()->?int{with Div::exhausted()->None;with Div::budget(20);Some(spin())}",
    );
    rejects(
        "fn example()->?int{with Div::exhausted()->{println(\"recovery\");None};with Div::budget(20);Some(1)}",
        "E0612",
    );
    accepts(
        "fn example()->?int{with Div::exhausted()->None;with Div::budget(20);var total=0;for [1,2,3] as number{total+=number};Some(total)}",
    );
    rejects(
        "fn one()->int{1}\nfn example(){with Div::exhausted()->resume();let _=Div::budget(0,one)}",
        "E0822",
    );
    rejects(
        "fn example(){with Div::exhausted()->();with Fiber::yield()->resume();let _=Div::budget(10,\\->Fiber::yield())}",
        "E0822",
    );
    rejects(
        "var count=0\nfn modify() &{mut count}{count+=1}\nfn example(){with Div::exhausted()->();let _=Div::budget(10,modify)}",
        "E0822",
    );
    // The budget may abort before flag's later write. Its recovery snapshot
    // must therefore keep the potentially aliasing path after the block.
    rejects(
        "type Cell={mut value:int}\nfn swap(mut a:Cell,mut b:Cell)&mut{a.value+=1;b.value+=1}\nfn one(){}\nfn example(){let mut a=Cell.{value:0};let mut b=Cell.{value:0};var flag=false;{with Div::exhausted()->();Div::budget(10,one);flag=true};let mut selected=if flag{^mut b}else{^mut a};swap(mut a,mut selected);b.value+=0}",
        "E0523",
    );
}

#[test]
fn derive_receives_closed_constructions_without_freezing_old_live_children() {
    accepts(
        "type Entry={rank:int,name:str}\nfn example(){let sorted=Order::sorted([Entry.{rank:1,name:\"a\"},Entry.{rank:1,name:\"b\"}],.{compare:\\a,b->Order::compare_int(a.rank,b.rank)});assert(Array::map(sorted,\\.name)==[\"a\",\"b\"])}",
    );
    accepts(
        "type Entry={rank:int,name:str}\nfn example(){let values=[Entry.{rank:1,name:\"a\"},Entry.{rank:1,name:\"b\"}];let sorted=Order::sorted(values,.{compare:\\a,b->Order::compare_int(a.rank,b.rank)});assert(Array::map(sorted,\\.name)==[\"a\",\"b\"])}",
    );
    let retained = check(
        "type Cell={mut value:int}\nfn example(source:Immut<Cell>){let changed=source |> derive \\mut draft->{draft.value=2};assert(changed.value==2)}",
    );
    let retained = retained
        .program
        .expect("derive must retain its input Immut qualification");
    assert!(
        retained.facts().bindings.iter().any(
            |binding| binding.name == "changed" && matches!(binding.value.ty, Ty::Immutable(_))
        )
    );
    rejects(
        "type Cell={mut value:int}\nfn publish(source:Cell){let holder=.{child:source}}",
        "E0535",
    );
    accepts(
        "fn example(){let changed=.{theme:\"dark\"} |> derive \\mut draft->{draft.theme=\"light\"};assert(changed.theme==\"light\")}",
    );
    accepts(
        "type Cell={mut value:int}\nfn example(){let child=Cell.{value:1};let changed=.{child:child} |> derive \\mut draft->{draft.child.value=2};assert(child.value==1&&changed.child.value==2)}",
    );
    rejects(
        "type Cell={mut value:int}\nfn example(source:Cell){let changed=.{child:source} |> derive \\mut draft->{draft.child.value=2}}",
        "E0536",
    );
    rejects(
        "type Cell={mut value:int}\nfn example(source:Immut<Cell>){let changed=.{child:source} |> derive \\mut draft->{draft.child.value=2}}",
        "E0520",
    );
    rejects(
        "type Cell={mut value:int}\nfn example(){let mut child=Cell.{value:1};let changed=.{child:child} |> derive \\mut draft->{draft.child.value=2};child.value+=1}",
        "E0536",
    );
}

#[test]
fn explicit_iterator_sources_retain_readonly_steps_and_cursor_state() {
    accepts(
        "fn example(){let source=Iter::map(Iter::indexed([1,2]),\\n->n*2);let limited=Iter::take(source,1);let mut cursor=Iter::cursor((0,0));assert(Iter::pull(mut cursor,limited)==Some(2));assert(Iter::pull(mut cursor,limited)==None)}",
    );
    accepts(
        "var calls=0\nfn step(state:int)->Iter::Step<int,int> &{mut calls}{calls+=1;Iter::Step::Done}\nfn example(){let source=.{step:step};let limited=Iter::take(source,0);let mut cursor=Iter::cursor((0,0));assert(Iter::pull(mut cursor,limited)==None)}",
    );
    accepts(
        "fn example(){let source=Iter::indexed([10,20]);let mut cursor=Iter::cursor(0);assert(Iter::pull(mut cursor,source)==Some(10));assert(Iter::pull(mut cursor,source)==Some(20));assert(Iter::pull(mut cursor,source)==None);assert(cursor.state==2&&cursor.ended);assert(Iter::pull(mut cursor,source)==None)}",
    );
    rejects(
        "fn example(){let source=Iter::indexed([1]);let copied=clone(source)}",
        "E0530",
    );
    rejects(
        "fn example(){let source=Iter::indexed([1]);let cursor=Iter::cursor(0);let _=Iter::pull(mut cursor,source)}",
        "E0520",
    );
    let results = check(
        "fn example(){let result=Err(\"x\");let source=Iter::indexed([result]);let mut cursor=Iter::cursor(0);let _=Iter::pull(mut cursor,source)}",
    );
    assert!(results.program.is_none() && !results.unsupported.is_empty());
}
