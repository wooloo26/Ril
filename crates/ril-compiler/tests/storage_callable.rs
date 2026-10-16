use ril_compiler::{CompilationOutcome, Session};

fn accepted(source: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{source}: {outcome:?}"
    );
}

fn rejects(source: &str, code: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
        "{source}: {outcome:?}"
    );
}

#[test]
fn storage_descriptors_keep_fresh_factory_reception() {
    accepted(
        "type Cell={mut count:int}\nfn make(n:int)->Cell{Cell.{count:n}}\nfn example(){let append:fn(mut []Cell,Cell)->() &mut=Array::push;let factory:fn(int)->Cell=make;let mut items:[]Cell=[];append(mut items,factory(3));items[0].count+=1}",
    );
    accepted(
        "type Cell={mut count:int}\nfn example(){let insert:fn(mut []Cell,int,Cell)->() &mut=Array::insert;let mut items:[]Cell=[];insert(mut items,0,Cell.{count:3});items[0].count+=1}",
    );
    accepted(
        "type Cell={mut count:int}\nfn example(){let set:fn(mut [str:Cell],str,Cell)->() &mut=Map::set;let mut items:[str:Cell]=[:];set(mut items,\"key\",Cell.{count:3});assert(items[\"key\"]?.count==Some(3))}",
    );
}

#[test]
fn storage_descriptor_context_preserves_modes_and_type_correlations() {
    for (source, code) in [
        (
            "fn example(){let bad:fn(mut []int,str)->() &mut=Array::push}",
            "E0301",
        ),
        (
            "fn example(){let bad:fn([]int,int)->() &mut=Array::push}",
            "E0301",
        ),
        (
            "fn example(){let bad:fn(mut []int,int)->int &mut=Array::push}",
            "E0301",
        ),
        (
            "fn example(){let bad:fn(mut [str:int],int,int)->() &mut=Map::set}",
            "E0301",
        ),
        (
            "type Cell={mut count:int}\nfn example(){let append:fn(mut []Cell,Cell)->() &mut=Array::push;let item=Cell.{count:3};let mut items:[]Cell=[];append(mut items,item);items[0].count+=1}",
            "E0522",
        ),
        (
            "fn example(){let bad:fn(mut []int,int)->() &{}=Array::push}",
            "E0534",
        ),
    ] {
        rejects(source, code);
    }
}

#[test]
fn storage_descriptor_retention_remains_explicit() {
    accepted(
        "type Cell={mut count:int}\nfn example(){let append:fn(mut []Cell,^mut Cell)->() &^mut=Array::push;let mut item=Cell.{count:3};let mut items:[]Cell=[];append(mut items,^mut item);items[0].count+=1;item.count+=1}",
    );
    rejects(
        "type Cell={mut count:int}\nfn example(){let append:fn(mut []Cell,Cell)->() &mut=Array::push;let mut item=Cell.{count:3};let mut items:[]Cell=[];append(mut items,^mut item);item.count+=1}",
        "E0405",
    );
}
