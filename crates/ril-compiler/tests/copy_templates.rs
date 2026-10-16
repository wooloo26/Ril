use ril_compiler::{CompilationOutcome, Session};

const DUP: &str = "fn duplicate<T>(source:T)->T{clone(source)}\n";
fn accepted(source: &str) -> ril_compiler::hir::VerifiedProgram {
    Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|result| panic!("{source}\n{result:?}"))
}
fn incomplete(source: &str) {
    let result = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(result, CompilationOutcome::NotImplemented { .. }),
        "{source}\n{result:?}"
    );
}
fn rejected(source: &str, code: &str) {
    let result = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&result, CompilationOutcome::Rejected {diagnostics} if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
        "{source}\n{result:?}"
    );
}

#[test]
fn private_direct_instances_prove_scalars_reference_data_and_environment_free_functions() {
    for body in [
        "fn example(){assert(duplicate(7)==7);assert(duplicate(\"hello\")==\"hello\")}",
        "type Cell={mut value:int}\nfn example(){let original=Cell.{value:1};let mut copied=duplicate(original);copied.value=2;assert(original.value==1)}",
        "fn seven()->int{7}\nfn example(){let copied=duplicate(seven);assert(copied()==7)}",
    ] {
        let program = accepted(&format!("{DUP}{body}"));
        let facts = program.facts();
        assert!(facts.copy_template_closure.is_some());
        ril_compiler::sema::copy_template_closure::validate(facts).unwrap();
        let templates: Vec<_> = facts
            .copy_boundaries
            .iter()
            .filter(|boundary| boundary.template)
            .collect();
        assert!(!templates.is_empty());
        assert!(
            templates
                .iter()
                .all(|boundary| boundary.output.is_none() && !boundary.requirements.is_empty())
        );
        let core = ril_compiler::lower::lower_core(&program).unwrap();
        assert!(core.provenance.copy_template_closure.is_some());
    }
}

#[test]
fn helper_chains_nested_carriers_and_copy_of_copy_keep_each_pending_producer() {
    for helper in [
        "fn forward<U>(value:U)->U{duplicate(value)}",
        "fn forward<U>(value:U)->U{clone(clone(value))}",
    ] {
        let prefix = if helper.contains("duplicate(") {
            DUP
        } else {
            ""
        };
        accepted(&format!(
            "{prefix}{helper}\nfn example(){{let source=[1,2];let mut copy=forward(source);copy[0]=9;assert(source[0]==1)}}"
        ));
    }
    accepted(
        "fn wrapped<T>(source:T)->{item:T}{.{item:clone(source)}}\nfn example(){let original=[1,2];let mut copy=wrapped(original);copy.item[0]=9;assert(original[0]==1)}",
    );
    accepted(
        "fn wrapped<T>(source:T)->(T,T){(clone(source),clone(source))}\nfn example(){let original=[1,2];let mut copy=wrapped(original);copy.0[0]=9;assert(copy.1[0]==1&&original[0]==1)}",
    );
}

#[test]
fn conditional_local_forwarding_rechecks_the_actual_reception_permission() {
    let helper = "fn forward<T>(source:T)->T{let copied=clone(source);copied}\n";
    accepted(&format!(
        "{helper}fn example(){{let copied=forward([1,2]);assert(copied[0]==1)}}"
    ));
    rejected(
        &format!("{helper}fn example(){{let mut copied=forward([1,2]);copied[0]=9}}"),
        "E0528",
    );
}

#[test]
fn selecting_a_template_entry_cannot_borrow_another_calls_substitution() {
    let program = accepted(&format!("{DUP}fn example(){{assert(duplicate(1)==1)}}"));
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    ril_codegen::lower::lower_native_with_entry(&core, "example").unwrap();
    let error = ril_codegen::lower::lower_native_with_entry(&core, "duplicate").unwrap_err();
    assert!(error.to_string().contains("copy-template"), "{error:?}");
}

#[test]
fn every_forbidden_actual_instance_remains_rejected_after_an_ordinary_success() {
    rejected(
        &format!(
            "use ril/file\n{DUP}fn example(file:File::Handle){{assert(duplicate(1)==1);let _=duplicate(file)}}"
        ),
        "E0530",
    );
    rejected(
        &format!(
            "{DUP}fn example(){{var current=1;current+=1;assert(duplicate(1)==1);let _=duplicate(\\->current)}}"
        ),
        "E0530",
    );
    rejected(
        &format!(
            "use ril/file\n{DUP}type Mixed{{Number(int),Resource(File::Handle)}}\nfn example(flag:bool,file:File::Handle){{assert(duplicate(1)==1);let value=if flag{{Mixed::Number(1)}}else{{Mixed::Resource(file)}};let _=duplicate(value)}}"
        ),
        "E0530",
    );
}

#[test]
fn export_extraction_missing_instances_and_recursive_templates_remain_incomplete() {
    incomplete(DUP);
    incomplete(&format!("pub {DUP}fn example(){{assert(duplicate(1)==1)}}"));
    incomplete(&format!(
        "{DUP}fn example(){{assert(duplicate(1)==1);let copied=duplicate<int>;assert(copied(2)==2)}}"
    ));
    incomplete(
        "fn duplicate(source:fn()->int)->fn()->int{clone(source)}\nfn package()->{call:fn(fn()->int)->fn()->int}{.{call:duplicate}}\nfn one()->int{1}\nfn example(){let copied=duplicate(one);assert(copied()==1)}",
    );
    incomplete(
        "fn recursive<T>(depth:int,source:T)->T{if depth==0{clone(source)}else{recursive(depth-1,source)}}\nfn example(){assert(recursive(2,1)==1)}",
    );
}

#[test]
fn resource_copy_exceptions_are_not_ordinary_template_discharge() {
    let program = accepted(
        "use ril/concurrent/channel\nfn duplicate<T>(source:T)->T @Fiber{clone(source)}\nfn example(tx:Channel::Sender<int>) @Fiber{let _=duplicate(tx)}",
    );
    use ril_compiler::sema::resource_copy::CopyDischarge;
    let facts = program.facts();
    let closure = facts.copy_template_closure.as_ref().unwrap();
    assert!(!closure.discharges.is_empty());
    assert!(
        closure
            .discharges
            .values()
            .all(|proof| matches!(proof, CopyDischarge::Sender(_)))
    );
    assert!(!facts.resource_clones.is_empty());
    assert!(
        facts
            .copy_boundaries
            .iter()
            .all(|proof| proof.template && proof.output.is_none())
    );
    ril_compiler::sema::copy_template_closure::validate(facts).unwrap();
}

#[test]
fn row_instantiation_keeps_independent_original_and_copy_result_duties() {
    let helper = "fn duplicate<R>(source:{..R})->{..R}{clone(source)}\n";
    accepted(&format!(
        "{helper}fn example(){{let original=.{{value:1}};let copied=duplicate(original);assert(copied.value==1)}}"
    ));
    accepted(&format!(
        "{helper}fn example(){{let original=.{{value:Ok(1)}};assert(original.value is Ok(_)|Err(_));let copied=duplicate(original);assert(copied.value is Ok(_)|Err(_))}}"
    ));
    rejected(
        &format!(
            "{helper}fn example(){{let original=.{{value:Ok(1)}};assert(original.value is Ok(_)|Err(_));let _=duplicate(original)}}"
        ),
        "E0720",
    );
    rejected(
        &format!(
            "{helper}fn example(){{let original=.{{value:Ok(1)}};let copied=duplicate(original);assert(copied.value is Ok(_)|Err(_))}}"
        ),
        "E0720",
    );
}

#[test]
fn closure_certificate_cannot_omit_a_site_or_change_an_instance() {
    use ril_compiler::sema::{
        copy_contract::CopyInvocationStatus, copy_template_closure::validate,
    };
    let program = accepted(&format!(
        "{DUP}fn example(){{assert(duplicate(1)==1);assert(duplicate(2)==2)}}"
    ));
    let facts = program.facts();
    let mut missing = facts.clone();
    missing.copy_template_closure = None;
    assert!(validate(&missing).is_err());
    let mut failed = facts.clone();
    let id = *failed
        .copy_template_closure
        .as_ref()
        .unwrap()
        .certificate
        .instances
        .values()
        .next()
        .unwrap()
        .first()
        .unwrap();
    failed.copy_invocations[id.0 as usize].status = CopyInvocationStatus::Unsupported;
    assert!(validate(&failed).is_err());
    let mut omitted = facts.clone();
    omitted
        .copy_template_closure
        .as_mut()
        .unwrap()
        .templates
        .values_mut()
        .next()
        .unwrap()
        .sites
        .pop_first();
    assert!(validate(&omitted).is_err());
    let mut invented = facts.clone();
    let template = invented
        .copy_boundaries
        .iter_mut()
        .find(|boundary| boundary.template)
        .unwrap();
    template.output = Some(template.source.clone());
    assert!(validate(&invented).is_err());
}
