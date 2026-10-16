use ril_compiler::{CompilationOutcome, Session};

fn accepts(source: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{source}: {outcome:?}"
    );
}

fn rejects(source: &str, codes: &[&str]) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| codes.contains(&diagnostic.code.as_str()))),
        "{source}: {outcome:?}"
    );
}

#[test]
fn named_tail_extension_preserves_the_callers_members() {
    accepts(
        "fn stamp<R>(item:{..R})->{stamp:int,..R}{.{stamp:7,..item}}\nfn example(){let item=stamp(.{id:1,name:\"Ada\"});assert(item.id==1 && item.name==\"Ada\" && item.stamp==7)}",
    );
}

#[test]
fn unchanged_tail_is_a_complete_source_transport() {
    accepts(
        "fn identity<R>(item:{..R})->{..R}{item}\nfn example(){let item=identity(.{id:1});assert(item.id==1)}",
    );
}

#[test]
fn known_fields_on_open_formals_keep_their_product_type() {
    accepts(
        "fn id<R>(item:{id:int,..R})->int{item.id}\nfn example(){assert(id(.{id:1,name:\"Ada\"})==1)}",
    );
}

#[test]
fn nested_generic_calls_keep_the_callers_rigid_tail() {
    accepts(
        "fn stamp<R>(item:{..R})->{stamp:int,..R}{.{stamp:7,..item}}\nfn forward<T>(item:{..T})->{stamp:int,..T}{stamp(item)}\nfn example(){let item=forward(.{id:1});assert(item.id==1 && item.stamp==7)}",
    );
}

#[test]
fn transparent_row_aliases_supply_the_same_declaration_absences() {
    accepts(
        "type WithId<R>={id:int,..R}\nfn retain<R>(item:WithId<R>)->WithId<R>{.{..item}}\nfn example(){let item=retain(.{id:1,name:\"Ada\"});assert(item.name==\"Ada\")}",
    );
}

#[test]
fn rest_transport_retains_the_unknown_family() {
    accepts(
        "fn rest<R>(item:{id:int,..R})->{..R}{let view .{id:_,..tail}=item;tail}\nfn example(){let item=rest(.{id:1,name:\"Ada\"});assert(item.name==\"Ada\")}",
    );
}

#[test]
fn read_only_tail_spread_never_recovers_child_write_authority() {
    rejects(
        "type Cell={mut value:int}\nfn stamp<R>(item:{..R})->{stamp:int,..R}{.{stamp:7,..item}}\nfn example(){let mut cell=Cell.{value:0};let view observed=cell;let mut item=stamp(.{child:observed});item.child.value+=1}",
        &["E0520", "E0525"],
    );
}

#[test]
fn instantiated_tail_keeps_result_inspection_duties() {
    let prefix = "fn stamp<R>(item:{..R})->{stamp:int,..R}{.{stamp:7,..item}}\n";
    accepts(&format!(
        "{prefix}fn example(){{let item=stamp(.{{answer:Ok(1)}});assert(item.answer is Ok(1))}}"
    ));
    rejects(
        &format!("{prefix}fn example(){{let item=stamp(.{{answer:Ok(1)}});assert(item.stamp==7)}}"),
        &["E0720"],
    );
    rejects(
        "fn forget<R>(item:{..R}){}\nfn example(){forget(.{answer:Ok(1)})}",
        &["E0720"],
    );
    rejects(
        "fn choose<R>(flag:bool,left:{..R},right:{..R})->{..R}{if flag{left}else{right}}\nfn example(flag:bool){let item=choose(flag,.{answer:Ok(1)},.{answer:Ok(2)});assert(item.answer is Ok(_))}",
        &["E0720"],
    );
}

#[test]
fn overlapping_instantiation_cannot_use_the_signature_absence_as_evidence() {
    rejects(
        "fn stamp<R>(item:{..R})->{stamp:int,..R}{.{stamp:7,..item}}\nfn example(){let item=stamp(.{stamp:1});assert(item.stamp==7)}",
        &["E0212", "E0301"],
    );
}

#[test]
fn open_rows_cannot_launder_immutable_or_slot_write_permissions() {
    rejects("fn freeze<R>(item:{..R})->Immut<{..R}>{item}", &["E0535"]);
    rejects(
        "fn write<R>(mut item:{id:int,..R})&mut{item.id=2}",
        &["E0520"],
    );
    accepts("fn immutable<R>(item:Immut<{..R}>)->Immut<{..R}>{item}");
    accepts("fn absent<R>(item:{..R})->{..R}{panic(\"no result\")}");
}

#[test]
fn unknown_tail_copy_and_unknown_tail_union_remain_unimplemented() {
    for source in [
        "fn copy<R>(item:{..R})->{..R}{clone(item)}",
        "fn merge<R,S>(left:{..R},right:{..S}){let _=.{..left,..right}}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome, CompilationOutcome::NotImplemented { .. }),
            "{source}: {outcome:?}"
        );
    }
}

#[test]
fn row_contract_edits_invalidate_absence_and_child_permission_facts() {
    let prefix =
        "type Cell={mut value:int}\nfn stamp<R>(item:{..R})->{stamp:int,..R}{.{stamp:7,..item}}\n";
    let valid = format!("{prefix}fn example(){{let item=stamp(.{{id:1}});assert(item.id==1)}}");
    let invalid = format!(
        "{prefix}fn example(){{let mut cell=Cell.{{value:0}};let view observed=cell;let mut item=stamp(.{{child:observed}});item.child.value+=1}}"
    );
    let mut session = Session::new(valid.as_bytes().to_vec());
    assert!(matches!(
        session.check(),
        CompilationOutcome::Accepted { .. }
    ));
    for source in [&invalid, &valid, &invalid] {
        session.update(source.as_bytes().to_vec());
        let incremental = session.check();
        let fresh = Session::new(source.as_bytes().to_vec()).check();
        assert_eq!(format!("{incremental:?}"), format!("{fresh:?}"));
    }
}

#[test]
fn lowered_row_family_keeps_the_input_origins_permissions_and_result_duties() {
    use ril_ir::provenance::{OriginKind, Permission, Projection};
    let source = "fn stamp<R>(item:{..R})->{stamp:int,..R}{.{stamp:7,..item}}";
    let parsed = ril_syntax::parse(source);
    let checked =
        ril_compiler::sema::analyze(&parsed.program, ril_compiler_core::source::FileId(0));
    let verified = checked.program.as_ref().expect("universal row definition");
    let core = ril_compiler::lower::lower_core(verified).expect("row lowering");
    let graph = &core.provenance;
    let tails: Vec<_> = graph
        .fields
        .iter()
        .filter(|field| matches!(field.projection, Projection::RowTail(_)))
        .collect();
    let output = tails
        .iter()
        .find(|field| {
            matches!(
                graph.origins[field.origin.0 as usize].kind,
                OriginKind::Fresh(_)
            )
        })
        .expect("fresh record with a carried tail");
    let input = tails
        .iter()
        .find(|field| {
            matches!(
                graph.origins[field.origin.0 as usize].kind,
                OriginKind::Formal(_)
            ) && field.value.origins == output.value.origins
        })
        .expect("output tail points to the original parameter family");
    assert!(!output.value.origins.is_empty());
    assert_eq!(input.value.results, output.value.results);
    assert!(!output.value.results.is_empty());
    assert!(output.value.outer_results.is_empty());
    assert!(matches!(output.value.permission, Permission::Read));
    assert!(!output.value.flags.construction);
    assert!(graph.origins[output.origin.0 as usize].edges.iter().any(
        |(projection, origins)| matches!(projection, Projection::RowTail(_))
            && origins == &input.value.origins
    ));
}

#[test]
fn branch_spreads_join_sources_without_treating_alternatives_as_duplicate_fields() {
    accepts(
        "fn select<R>(flag:bool,left:{..R},right:{..R})->{stamp:int,..R}{.{stamp:7,..if flag{left}else{right}}}\nfn example(){let item=select(true,.{id:1},.{id:2});assert(item.id==1)}",
    );
    rejects(
        "type Cell={mut value:int}\nfn stamp<R>(item:{..R})->{stamp:int,..R}{.{stamp:7,..item}}\nfn example(flag:bool){let mut cell=Cell.{value:0};let view observed=cell;let mut item=stamp(if flag{.{child:observed}}else{.{child:Cell.{value:2}}});item.child.value+=1}",
        &["E0520", "E0525"],
    );
}

#[test]
fn concrete_resource_and_scoped_members_survive_row_transport() {
    let prefix = "fn stamp<R>(item:{..R})->{stamp:int,..R}{.{stamp:7,..item}}\n";
    rejects(
        &format!(
            r#"{prefix}fn example() @Fiber{{let file=File::open("unused-path") ?? \_ -> panic("open");let copy=clone(stamp(.{{file:file}}))}}"#
        ),
        &["E0530"],
    );
    rejects(
        &format!(
            r#"{prefix}type Guard={{on_close:fn()->()}}
fn escape()->{{stamp:int,resource:Guard}}{{let scoped guard=Guard.{{on_close:\->()}};stamp(.{{resource:guard}})}}"#
        ),
        &["E0604"],
    );
}
