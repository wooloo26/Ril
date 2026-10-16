use ril_compiler::{CheckOptions, Session};
use ril_compiler_core::target::TargetLayout;

#[test]
fn local_meta_aggregates_reify_typed_scalars_without_new_numeric_holes() {
    let source = r#"
fn example() {
    meta let PAIR=(1,2)
    meta let ITEMS=[3,4]
    meta let FLOATS=(1.0f32,16777217.0)
    assert(PAIR.0+PAIR.1==3)
    assert(ITEMS[0]+ITEMS[1]==7)
    assert("{FLOATS.1}"=="16777217.0")
}
"#;
    for (target, layout) in [
        ("pointer32", TargetLayout::POINTER32),
        ("pointer64", TargetLayout::POINTER64),
    ] {
        let verified = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap();
        ril_compiler::lower::lower_core_for(&verified, layout).unwrap();
    }
}

#[test]
fn evaluated_ints_keep_their_sort_in_lengths_and_static_argument_identity() {
    let source = r#"
meta let LENGTH=1+1
type Buffer=[LENGTH]int
meta let _=assert(type<Buffer>==type<[2]int>)
fn example(){let values:Buffer=[1,2];assert(len(values)==2)}
"#;
    assert!(Session::new(source.as_bytes().to_vec()).verify().is_ok());
}
