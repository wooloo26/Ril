use ril_compiler::{CompilationOutcome, Session};

#[test]
fn closed_product_gadt_equations_transport_only_the_tested_arm_result() {
    for source in [
        "type Expr<T>{Pair((int,bool))->Expr<(int,bool)>,Flag(bool)->Expr<bool>}\nfn evaluate<T>(value:Expr<T>)->T{match value{Expr::Pair((number,flag))->(number,flag),Expr::Flag(flag)->flag}}\nfn example(){let pair=evaluate(Expr::Pair((7,true)));assert(pair.0==7&&pair.1);assert(evaluate(Expr::Flag(true)))}",
        "type Expr<T>{Record({mut count:int})->Expr<{mut count:int}>,Flag(bool)->Expr<bool>}\nfn evaluate<T>(value:Expr<T>)->T{match value{Expr::Record(record)->record,Expr::Flag(flag)->flag}}\nfn example(){let value=evaluate(Expr::Record(.{count:7}));assert(value.count==7)}",
        "type Product=(int,bool)\ntype Expr<T>{Pair(Product)->Expr<Product>,Flag(bool)->Expr<bool>}\nfn evaluate<T>(value:Expr<T>)->T{match value{Expr::Pair((number,flag))->(number,flag),Expr::Flag(flag)->flag}}\nfn example(){let value=evaluate(Expr::Pair((7,true)));assert(value.0==7&&value.1)}",
        "type Expr<T>{Optional(?int)->Expr<?int>,Flag(bool)->Expr<bool>}\nfn evaluate<T>(value:Expr<T>)->T{match value{Expr::Optional(value)->value,Expr::Flag(flag)->flag}}\nfn example(){assert(evaluate(Expr::Optional(Some(7)))==Some(7));assert(evaluate(Expr::Optional(None))==None)}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome, CompilationOutcome::Accepted { .. }),
            "{source}: {outcome:?}"
        );
    }
    let source = "type Expr<T>{Pair((int,bool))->Expr<(int,bool)>,Flag(bool)->Expr<bool>}\nfn bad<T>(value:Expr<T>,other:T)->int{match value{Expr::Pair(_)->other.0,Expr::Flag(_)->0}}";
    assert!(
        Session::new(source.as_bytes().to_vec()).verify().is_err(),
        "an arm equation rewrote an independent value typed T"
    );
}

#[test]
fn product_equations_never_restore_returned_payload_authority_or_discard_results() {
    let source = "type Expr<T>{Record({mut count:int})->Expr<{mut count:int}>}\nfn evaluate<T>(value:Expr<T>)->T{match value{Expr::Record(record)->record}}\nfn example(){let value=evaluate(Expr::Record(.{count:7}));let mut changed=value;changed.count+=1}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome,CompilationOutcome::Rejected {ref diagnostics} if diagnostics.iter().any(|diagnostic|matches!(diagnostic.code.as_str(),"E0520"|"E0522"))),
        "{outcome:?}"
    );
    let source = "type Expr<T>{Result(Result<int,str>)->Expr<Result<int,str>>}\nfn evaluate<T>(value:Expr<T>)->T{match value{Expr::Result(result)->result}}\nfn example(){let value=evaluate(Expr::Result(Ok(7)))}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome,CompilationOutcome::Rejected {ref diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720")),
        "{outcome:?}"
    );
}

#[test]
fn dimensions_and_callable_rows_still_require_complete_conditional_identities() {
    for source in [
        "type Expr<T>{Array([2]int)->Expr<[2]int>}\nfn evaluate<T>(value:Expr<T>)->T{match value{Expr::Array(array)->array}}",
        "type Expr<T>{Action(fn(mut []int)->() &mut)->Expr<fn(mut []int)->() &mut>}\nfn evaluate<T>(value:Expr<T>)->T{match value{Expr::Action(action)->action}}",
    ] {
        assert!(
            Session::new(source.as_bytes().to_vec()).verify().is_err(),
            "{source}: a bare Ty erased part of the conditional type identity"
        );
    }
}
