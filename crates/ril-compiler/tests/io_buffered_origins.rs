use ril_compiler::{
    Session,
    sema::{model::Value, validate::solved_facts},
};
use std::collections::BTreeSet;

fn complete_origins(value: &Value) {
    for branches in value.origins.choices.values() {
        assert_eq!(
            branches.iter().flatten().copied().collect::<BTreeSet<_>>(),
            value.origins.nodes
        );
    }
    for child in [
        &value.option_payload,
        &value.result_payload,
        &value.result_success,
        &value.result_error,
        &value.variant_payload,
    ]
    .into_iter()
    .flatten()
    .chain(value.variant_witnesses.values())
    {
        complete_origins(child);
    }
}

#[test]
fn wrapped_file_read_keeps_complete_final_buffered_result_alternatives() {
    let source = r#"
use ril/io
use ril/file
use ril/path
fn wrapped(mut file:File::Handle,maximum:int)->Result<Io::ReadChunk,Io::IoError> @Fiber &mut {
    File::read_chunk(mut file,maximum)
}
fn example() @Fiber {
    let scoped mut file=File::open_path(Path::from_string("unused"),File::OpenMode::Read) ?? \_error->panic("open")
    let mut buffer=Io::read_buffer(2)
    let first=Io::read_buffered(mut buffer,mut file,.{read:wrapped},1) ?? \_error->panic("read")
    assert(first.data==b"a")
    assert(File::read_chunk(mut file,1) is Ok(_))
}
"#;
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    solved_facts(verified.facts()).unwrap();
    for expression in &verified.facts().expressions {
        complete_origins(&expression.value);
    }
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert!(!core.provenance.values.is_empty());
}
