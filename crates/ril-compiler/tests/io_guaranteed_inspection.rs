use ril_compiler::{CompilationOutcome, Session};

const ORIGINAL: &str = include_str!("fixtures/io_callback_result_inspection.ril");

#[test]
fn a_normal_read_all_return_retains_its_reached_first_operation_inspection() {
    let verified = Session::new(ORIGINAL.as_bytes().to_vec()).verify().unwrap();
    ril_compiler::lower::lower_core(&verified).unwrap();
}

#[test]
fn an_empty_write_all_still_enters_the_validation_operation() {
    let source = include_str!("fixtures/io_callback_empty_write_inspection.ril");
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    ril_compiler::lower::lower_core(&verified).unwrap();
}

#[test]
fn zero_iteration_and_unreached_inspections_do_not_acquire_the_io_guarantee() {
    for source in [
        r#"use ril/array
fn example(){
    let pending:Result<int,str>=Ok(1)
    let values:[]int=[]
    let mapped=Array::map(values,\value:int->{assert(pending is Ok(_)|Err(_));value})
    ()
}"#,
        r#"use ril/io
type Reader={pending:Result<int,str>}
fn read(mut reader:Reader,limit:int)->Result<Io::ReadChunk,Io::IoError> &mut{
    if false{assert(reader.pending is Ok(_)|Err(_))}
    Ok(.{data:b"",end:true})
}
fn example(){
    let pending:Result<int,str>=Ok(1)
    let mut reader=Reader.{pending:pending}
    assert(Io::read_all(mut reader,.{read:read}) is Ok(_)|Err(_))
}"#,
        r#"use ril/io
type Reader={pending:Result<int,str>}
fn read(mut reader:Reader,limit:int)->Result<Io::ReadChunk,Io::IoError> &mut{
    assert(reader.pending is Ok(_)|Err(_))
    let copied=clone(reader.pending)
    Ok(.{data:b"",end:true})
}
fn example(){
    let pending:Result<int,str>=Ok(1)
    let mut reader=Reader.{pending:pending}
    assert(Io::read_all(mut reader,.{read:read}) is Ok(_)|Err(_))
}"#,
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
            "{source}\n{outcome:?}"
        );
    }
}
