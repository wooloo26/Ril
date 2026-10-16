#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn original_projection_forwarding_shared_rows_and_fixed_fields_execute() {
    for (index, source) in [
        include_str!("../../ril-compiler/tests/fixtures/record_bounds/original_projection.ril"),
        "fn read<T:{id:int,..R}>(value:T)->int{value.id}\nfn forward<U:{id:int,tag:str,..S}>(value:U)->int{read(value)}\npub fn test_native(){assert(forward(.{id:7,tag:\"ok\"})==7)}",
        "fn read<T:{id:int,..R}>(value:T)->int{value.id}\nfn forward<S>(value:{id:int,tag:str,..S})->int{read(value)}\npub fn test_native(){assert(forward(.{id:7,tag:\"ok\"})==7)}",
        "fn both<T:{id:int,..R},U:{flag:bool,..R}>(left:T,right:U)->int{left.id}\npub fn test_native(){assert(both(.{id:7,tag:\"ok\"},.{flag:true,tag:\"ok\"})==7)}",
        "fn first<T:{items:[2]int,..R}>(value:T)->int{value.items[0]}\npub fn test_native(){let items:[2]int=[7,9];assert(first(.{items:items})==7)}",
        "fn read<T:{id:int,tag:int,..R}>(value:T)->int{value.(\"id\")}\npub fn test_native(){assert(read(.{id:7,tag:9})==7)}",
        "fn read<T:{id:int,tag:int,..R}>(value:T)->int{value.(`id`)}\npub fn test_native(){assert(read(.{id:7,tag:9})==7)}",
        "fn read<T:{id:int,tag:int,..R}>(value:T)->int{value.(\"i\\u{64}\")}\npub fn test_native(){assert(read(.{id:7,tag:9})==7)}",
        "fn read<R,T:{id:int,..R}>(value:T,row:R)->int{value.id}\npub fn test_native(){assert(read(.{id:7,tag:\"ok\"},.{tag:\"ok\"})==7)}",
    ]
    .into_iter()
    .enumerate()
    {
        native_probe::executes(source, &format!("record-bound {index}"));
    }
}
