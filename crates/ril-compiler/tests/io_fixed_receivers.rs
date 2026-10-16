use ril_compiler::{CompilationOutcome, Session};
use ril_ir::specialization::ArgumentKey;

#[test]
fn original_fixed_receiver_and_dynamic_control_keep_actual_callback_schemas() {
    for source in [
        ril_test::case_source("tests/regressions/io.ril::io-fixed-receiver"),
        ril_test::case_source("tests/regressions/io.ril::io-dynamic-receiver-control"),
    ] {
        let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
        let core = ril_compiler::lower::lower_core(&verified).unwrap();
        ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    }
}

#[test]
fn nested_empty_readonly_and_dynamic_views_keep_declared_storage_schemas() {
    for source in [
        ril_test::case_source("tests/regressions/io.ril::io-nested-fixed-receiver"),
        ril_test::case_source("tests/regressions/io.ril::io-fixed-writer"),
        ril_test::case_source("tests/regressions/io.ril::io-dynamic-fixed-backing"),
        ril_test::case_source("tests/regressions/io.ril::io-readonly-capture"),
        ril_test::case_source("tests/regressions/io.ril::io-resource-fixed-receiver"),
    ] {
        let verified = Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        let core = ril_compiler::lower::lower_core(&verified).unwrap();
        ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
    }
}

#[test]
fn exact_scratch_storage_survives_summary_without_changing_dynamic_view_identity() {
    let fixed = ril_test::case_source("tests/regressions/io.ril::io-fixed-receiver").replace(
        "assert(result is Ok(_)|Err(_))",
        "assert(result is Ok(_)|Err(_));Array::push(mut reader.scratch,3u8)",
    );
    rejects(&fixed, "E0301");
    let verified = Session::new(
        ril_test::case_bytes("tests/regressions/io.ril::io-dynamic-fixed-backing").to_vec(),
    )
    .verify()
    .unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert!(core.provenance.bindings.iter().filter(|binding|binding.name=="reader").filter_map(|binding|binding.value.source_type_witness.as_ref()).any(|witness|matches!(&witness.shape,ArgumentKey::Record{fields,..} if fields.iter().any(|(name,_,shape)|name=="scratch" && matches!(shape,ArgumentKey::Array{length:None,..})))));
}

#[test]
fn callback_dimensions_and_modes_are_checked_against_the_actual_receiver() {
    for (receiver, callback, code) in [
        ("[2]u8", "[3]u8", "E0301"),
        ("[0][2]int", "[0][3]int", "E0301"),
        ("Immut<[2]u8>", "Immut<[3]u8>", "E0301"),
        ("?Immut<[2]u8>", "?Immut<[3]u8>", "E0301"),
    ] {
        let source = format!(
            "use ril/io\ntype Reader={{scratch:{receiver},mut calls:int}}\ntype Other={{scratch:{callback},mut calls:int}}\nfn read(mut reader:Other,limit:int)->Result<Io::ReadChunk,Io::IoError>&mut{{reader.calls+=1;Ok(.{{data:b\"\",end:true}})}}\nfn example(mut reader:Reader)&mut{{assert(Io::read_all(mut reader,.{{read:read}}) is Ok(_)|Err(_))}}"
        );
        rejects(&source, code);
    }
    rejects(
        "use ril/io\ntype Reader={scratch:[2]u8,mut calls:int}\nfn read(reader:Reader,limit:int)->Result<Io::ReadChunk,Io::IoError>{Ok(.{data:b\"\",end:true})}\nfn example(mut reader:Reader)&mut{assert(Io::read_all(mut reader,.{read:read}) is Ok(_)|Err(_))}",
        "E0407",
    );
}

#[test]
fn readonly_wrappers_check_cardinality_through_option_result_and_ordinary_calls() {
    for (target, input) in [
        ("Immut<[3]u8>", "array"),
        ("?Immut<[3]u8>", "Some(array)"),
        ("Result<Immut<[3]u8>,str>", "Ok(array)"),
        ("Immut<?[3]u8>", "Some(array)"),
    ] {
        let source = format!(
            "fn consume(value:{target}){{}}\nfn example(){{let array:Immut<[2]u8>=[1u8,2u8];consume({input})}}"
        );
        rejects(&source, "E0301");
    }
}

#[test]
fn actual_stream_callback_permissions_and_ambient_capabilities_remain_obligations() {
    let prelude = "use ril/io\ntype Reader={scratch:[2]u8,mut calls:int}\n";
    for (body, caller, code) in [
        (
            "reader.calls+=1;Array::push(mut reader.scratch,3u8)",
            "let mut reader=Reader.{scratch:[1u8,2u8],calls:0};assert(Io::read_all(mut reader,.{read:read}) is Ok(_)|Err(_))",
            "E0301",
        ),
        (
            "reader.calls+=1",
            "let mut reader=Reader.{scratch:[1u8,2u8],calls:0};reader.calls+=0;let view observed=reader;assert(Io::read_all(mut observed,.{read:read}) is Ok(_)|Err(_))",
            "E0520",
        ),
    ] {
        let source = format!(
            "{prelude}fn read(mut reader:Reader,limit:int)->Result<Io::ReadChunk,Io::IoError>&mut{{{body};Ok(.{{data:b\"\",end:true}})}}\nfn example(){{{caller}}}"
        );
        rejects(&source, code);
    }
    rejects(
        "use ril/io\ntype Reader={scratch:Immut<[2]u8>,mut calls:int}\nfn read(mut reader:Reader,limit:int)->Result<Io::ReadChunk,Io::IoError>&mut{reader.calls+=1;reader.scratch[0]=9u8;Ok(.{data:b\"\",end:true})}\nfn example(mut reader:Reader)&mut{assert(Io::read_all(mut reader,.{read:read}) is Ok(_)|Err(_))}",
        "E0522",
    );
    rejects(
        "use ril/io\ntype Reader={scratch:Immut<[2]u8>,mut calls:int}\nfn example(){let backing:[2]u8=[1u8,2u8];let mut reader=Reader.{scratch:backing,calls:0};let callback=\\mut current:Reader,limit:int->{current.calls+=1;assert(backing[0]==current.scratch[0]);Ok(.{data:b\"\",end:true})};assert(Io::read_all(mut reader,.{read:callback}) is Ok(_))}",
        "E0534",
    );
}

#[test]
fn receiver_resources_are_not_erased_by_schema_reification() {
    let source = "use ril/io\nuse ril/file\ntype Reader={scratch:[2]u8,file:File::Handle,mut calls:int}\nfn read(mut reader:Reader,limit:int)->Result<Io::ReadChunk,Io::IoError>&mut{reader.calls+=1;Ok(.{data:b\"\",end:true})}\nfn example(file:File::Handle){let mut reader=Reader.{scratch:[1u8,2u8],file:file,calls:0};assert(Io::read_all(mut reader,.{read:read}) is Ok(_)|Err(_))}";
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert!(core.provenance.bindings.iter().filter_map(|binding|binding.value.source_type_witness.as_ref()).any(|witness|matches!(&witness.shape,ArgumentKey::Record{fields,..} if fields.iter().any(|(name,_,shape)|name=="file" && matches!(shape,ArgumentKey::Name{name,..} if name=="File::Handle")))));
    rejects(
        &source.replace(
            "assert(Io::read_all",
            "let _=clone(reader);assert(Io::read_all",
        ),
        "E0530",
    );
    for name in ["File::Forged", "File::Handle<int>"] {
        let unknown = source.replace("File::Handle", name);
        let outcome = Session::new(unknown.as_bytes().to_vec()).check();
        assert!(
            !matches!(outcome, CompilationOutcome::Accepted { .. }),
            "{unknown}: {outcome:?}"
        );
    }
}

#[test]
fn builtin_identity_validation_rejects_forged_names_and_builtin_type_arguments() {
    use ril_syntax::ast::{TypeExpr, TypeKind};
    let verified =
        Session::new(ril_test::case_bytes("tests/regressions/io.ril::io-fixed-receiver").to_vec())
            .verify()
            .unwrap();
    for (name, arguments, key) in [
        ("File::Forged", vec![], "File::Forged<>"),
        (
            "File::Handle",
            vec![TypeExpr {
                span: verified.facts().expressions[0].span,
                text: String::new(),
                kind: TypeKind::Name {
                    path: vec!["int".into()],
                    arguments: vec![],
                },
            }],
            "File::Handle<int<>>",
        ),
    ] {
        let mut facts = verified.facts().clone();
        let value = &mut facts.expressions[0].value;
        let witness = ril_compiler::sema::model::SourceTypeWitness {
            syntax: TypeExpr {
                span: verified.facts().expressions[0].span,
                text: String::new(),
                kind: TypeKind::Name {
                    path: name.split("::").map(str::to_owned).collect(),
                    arguments,
                },
            },
            key: key.into(),
        };
        assert!(witness.validate_closed());
        value.source_type_witness = Some(std::sync::Arc::new(witness));
        let issues = ril_compiler::sema::validate::solved_facts(&facts).unwrap_err();
        assert!(
            issues.iter().any(|issue| matches!(
                issue.kind,
                ril_compiler::sema::validate::ValidationIssueKind::SourceTypeWitness
            )),
            "{issues:?}"
        );
    }
}

#[test]
fn receiver_result_debts_require_the_actual_callback_to_inspect_them() {
    let debt = "use ril/io\ntype Reader={scratch:[2]u8,pending:Result<int,str>,mut calls:int}\nfn read(mut reader:Reader,limit:int)->Result<Io::ReadChunk,Io::IoError>&mut{reader.calls+=1;Ok(.{data:b\"\",end:true})}\nfn example(){let pending:Result<int,str>=Ok(1);let mut reader=Reader.{scratch:[1u8,2u8],pending:pending,calls:0};assert(Io::read_all(mut reader,.{read:read}) is Ok(_)|Err(_))}";
    rejects(debt, "E0720");
    let inspected = debt.replace(
        "let mut reader=Reader.",
        "assert(pending is Ok(_)|Err(_));let mut reader=Reader.",
    );
    let verified = Session::new(inspected.as_bytes().to_vec())
        .verify()
        .unwrap();
    ril_compiler::lower::lower_core(&verified).unwrap();
}

fn rejects(source: &str, code: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected {diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code==code)),
        "{source}: expected {code}, got {outcome:?}"
    );
}
