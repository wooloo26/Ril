use ril_compiler::{CompilationOutcome, Session};

const OPERATIONS: &str = "type Reader={mut position:int}\nfn read(mut reader:Reader,maximum:int)->Result<Io::ReadChunk,Io::IoError>&mut{reader.position+=1;Ok(.{data:b\"\",end:true})}\nfn choose<T>(left:T,right:T)->T{left}\n";

#[test]
fn one_generic_type_accepts_alias_explicit_and_literal_operation_records() {
    let source = format!(
        "{OPERATIONS}fn example(){{let alias:Io::ReadOps<Reader>=.{{read:read}};let explicit:{{read:fn(mut Reader,int)->Result<Io::ReadChunk,Io::IoError>&mut}}=.{{read:read}};let one=choose(alias,explicit);let two=choose(explicit,.{{read:read}})}}"
    );
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    assert!(program.facts().effect_invocations.iter().any(|invocation| {
        !invocation.verifying
            && invocation.arguments.iter().any(|argument| {
                argument.syntax.as_ref().is_some_and(|syntax| {
                    matches!(syntax.kind, ril_syntax::ast::TypeKind::Record { .. })
                })
            })
    }));
    ril_compiler::lower::lower_core(&program).unwrap();
}

#[test]
fn generic_operation_records_preserve_distinct_dimensions_and_modes() {
    for source in [
        "fn choose<T>(left:T,right:T)->T{left}\nfn read_two(mut reader:[2]int,maximum:int)->Result<Io::ReadChunk,Io::IoError>&mut{reader[0]+=1;Ok(.{data:b\"\",end:true})}\nfn read_three(mut reader:[3]int,maximum:int)->Result<Io::ReadChunk,Io::IoError>&mut{reader[0]+=1;Ok(.{data:b\"\",end:true})}\nfn example(){let left:Io::ReadOps<[2]int>=.{read:read_two};let right:Io::ReadOps<[3]int>=.{read:read_three};let result=choose(left,right)}",
        "fn choose<T>(left:T,right:T)->T{left}\nfn writable(mut receiver:int)->int&mut{receiver+=1;receiver}\nfn readable(receiver:int)->int{receiver}\nfn example(){let left=.{run:writable};let right=.{run:readable};let result=choose(left,right)}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
            "{source}: {outcome:?}"
        );
    }
}
