use ril_compiler::{CompilationOutcome, Session};

#[test]
fn buffers_certify_actual_memory_callbacks_and_reject_outward_effects() {
    let source = "use ril/io\ntype Reader={mut calls:int}\nfn reading(mut reader:Reader,maximum:int)->Result<Io::ReadChunk,Io::IoError> &mut {reader.calls+=1;loop{}}\nfn example()->bool{with Div::exhausted()->true;with Div::budget(20);let mut reader=Reader.{calls:0};let mut buffer=Io::read_buffer(2);let result=Io::read_buffered(mut buffer,mut reader,.{read:reading},1);assert(result is Ok(_));false}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
    let source = source.replace(
        "&mut {reader.calls+=1;loop{}}",
        "@Fiber &mut {reader.calls+=1;Fiber::yield();Ok(.{data:b\"x\",end:true})}",
    );
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic| diagnostic.code=="E0822")),
        "{outcome:?}"
    );
}
