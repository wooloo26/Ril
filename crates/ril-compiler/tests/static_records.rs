use ril_compiler::sema::{
    facts::{Permission, Publication, Slot},
    model::Ty,
};
use ril_compiler::{CompilationOutcome, Session};

fn accepts(source: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{source}: {outcome:?}"
    );
}

#[test]
fn constant_record_slot_modes_survive_the_private_arena_and_core() {
    let source = "type Cell={mut count:int, label:str}\nmeta let ROOT={let cell=Cell.{count:1,label:\"x\"};(cell,cell)}\nmeta let CHILD=ROOT.0";
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let facts = verified.facts();
    let root = &facts
        .bindings
        .iter()
        .find(|b| b.name == "ROOT")
        .unwrap()
        .value;
    let node = *root.origins.nodes.first().unwrap();
    let cell = &facts.fields[&(node, Slot::Tuple(0))];
    assert_eq!(cell.origins, facts.fields[&(node, Slot::Tuple(1))].origins);
    assert_eq!(
        cell.origins,
        facts
            .bindings
            .iter()
            .find(|b| b.name == "CHILD")
            .unwrap()
            .value
            .origins
    );
    let Ty::Record(fields) = &cell.ty else {
        panic!("{:?}", cell.ty)
    };
    assert!(fields["count"].0);
    assert!(!fields["label"].0);
    assert_eq!(cell.permission, Permission::Read);
    assert_eq!(cell.publication, Publication::Immutable);
    assert!(!cell.construction);
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    let constant = core
        .constant_graphs
        .iter()
        .flat_map(|graph| &graph.nodes)
        .find(|node| matches!(node.kind, ril_ir::constants::ConstNodeKind::Record(_)))
        .unwrap();
    let ril_ir::provenance::Type::Record(fields) =
        &core.provenance.types[constant.value.ty.0 as usize]
    else {
        panic!("record constant type was erased")
    };
    assert!(
        fields
            .iter()
            .any(|(name, mutable, _)| name == "count" && *mutable)
    );
    assert!(
        fields
            .iter()
            .any(|(name, mutable, _)| name == "label" && !*mutable)
    );
}

#[test]
fn typed_function_results_parameters_and_generic_identity_preserve_slot_modes() {
    accepts(
        "type Cell={mut count:int}\nmeta fn identity<T>(value:T)->T{value}\nmeta fn make()->Cell{Cell.{count:7}}\nmeta fn get(value:Cell)->int{value.count}\nmeta let CELL=identity(make())\nmeta let _=assert(get(CELL)==7)\nfn example() &{CELL}{let mut copied=clone(CELL);copied.count=8;assert(CELL.count==7)}",
    );
}

#[test]
fn spread_keeps_inherited_modes_and_explicit_fields_choose_new_modes() {
    accepts(
        "type Cell={mut count:int,label:str}\nmeta let CELL=Cell.{count:1,label:\"x\"}\nmeta let SPREAD=.{..CELL}\nmeta let OVERRIDE=.{count:2,..CELL}\nfn example() &{SPREAD}{let mut copied=clone(SPREAD);copied.count=3}",
    );
    let outcome=Session::new(b"type Cell={mut count:int}\nmeta let CELL=Cell.{count:1}\nmeta let OVERRIDE=.{count:2,..CELL}\nfn example() &{OVERRIDE}{let mut copied=clone(OVERRIDE);copied.count=3}".to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|d|d.code=="E0520" && d.message.contains("slot"))),
        "{outcome:?}"
    );
}

#[test]
fn mutable_field_types_and_static_publication_are_still_checked() {
    for (source, code) in [
        (
            "type Cell={mut count:int}\nmeta let CELL=Cell.{count:\"wrong\"}",
            "E0301",
        ),
        (
            "type Cell={mut count:int}\nmeta let CELL=Cell.{count:1}\nfn example() &{CELL}{CELL.count=3}",
            "E0520",
        ),
        (
            "type Cell={mut count:int}\nmeta let ROOT=[Cell.{count:1}]\nfn example() &{ROOT}{let mut borrowed=ROOT[0];borrowed.count=3}",
            "E0520",
        ),
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|d|d.code==code)),
            "{source}: {outcome:?}"
        );
    }
}

#[test]
fn qualifiers_without_a_view_witness_do_not_enter_the_constant_arena() {
    for source in [
        "type Cell={mut count:int}\nmeta let OLD=.{count:1}\nmeta let CELL:Cell=OLD",
        "type Cell={mut count:int}\nmeta let CELL:Immut<Cell>=Cell.{count:1}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome, CompilationOutcome::NotImplemented { .. }),
            "{source}: {outcome:?}"
        );
    }
}

#[test]
fn record_rest_keeps_the_remaining_slot_modes() {
    accepts(
        "type Cell={mut count:int,label:str}\nmeta let ROOT={let value=Cell.{count:4,label:\"x\"};let .{label,..rest}=value;assert(label==\"x\");rest}\nfn example() &{ROOT}{let mut copied=clone(ROOT);copied.count=8;assert(ROOT.count==4)}",
    );
}

#[test]
fn static_mutable_slots_are_invariant_even_in_uninvoked_definitions() {
    let source = "meta fn wrong(value:{mut callback:fn()->never})->{mut callback:fn()->int}{value}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|d|d.code=="E0301")),
        "{outcome:?}"
    );
}

#[test]
fn editing_a_static_record_mode_never_reuses_the_old_write_authority() {
    let template = "type Cell={MODEcount:int}\nmeta let CELL=Cell.{count:1}\nfn example() &{CELL}{let mut copied=clone(CELL);copied.count=2}";
    let writable = template.replace("MODE", "mut ");
    let readonly = template.replace("MODE", "");
    let mut edited = Session::new(writable.as_bytes().to_vec());
    assert!(edited.verify().is_ok());
    for source in [&readonly, &writable, &readonly] {
        edited.update(source.as_bytes().to_vec());
        let observed = edited.check();
        let fresh = Session::new(source.as_bytes().to_vec()).check();
        assert_eq!(format!("{observed:?}"), format!("{fresh:?}"));
        if source == &readonly {
            assert!(
                matches!(&observed,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|d|d.code=="E0520")),
                "{observed:?}"
            );
        } else {
            assert!(
                matches!(observed, CompilationOutcome::Accepted { .. }),
                "{observed:?}"
            );
        }
    }
}

#[test]
fn explicit_binding_context_types_a_new_record_without_requalifying_old_values() {
    accepts(
        "type Cell={mut count:int}\nmeta let CELL:Cell=.{count:1}\nmeta fn make()->Cell{let value:Cell=.{count:2};value}\nmeta let OTHER=make()\nfn example() &{CELL,OTHER}{let mut copied=clone((CELL,OTHER));copied.0.count=3;copied.1.count=4}",
    );
}

#[test]
fn tail_and_branch_constructions_use_the_written_result_context() {
    accepts(
        "type Cell={mut count:int}\nmeta fn make(flag:bool)->Cell{if flag {.{count:1}}else{.{count:2}}}\nmeta let FIRST=make(true)\nmeta let SECOND:Cell=match false {true->.{count:3},false->{.{count:4}}}\nfn example() &{FIRST,SECOND}{let mut copied=clone((FIRST,SECOND));copied.0.count=8;copied.1.count=9}",
    );
    let source = "type Cell={mut count:int}\nmeta let OLD=.{count:1}\nmeta let CELL:Cell=if true {OLD}else{.{count:2}}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::NotImplemented { .. }),
        "{outcome:?}"
    );
}
