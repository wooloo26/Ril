use super::*;
#[test]
fn uppercase_static_key_values_use_the_certified_runtime_parameter() {
    execute(
        r#"
fn select<T:{..R},K:keyof T>(record:T,key:K)->T.(K){record.(K)}
fn member<K:keyof (int,str)>(value:(int,str),key:K)->(int,str).(K){value.(K)}
pub fn test_library(){
    let record=.{id:7,name:"Ada"}
    assert(select(record,"id")==7)
    assert(select(record,"name")=="Ada")
    assert(member((4,"value"),0)==4)
    assert(member((4,"value"),1)=="value")
}
"#,
    );
}
