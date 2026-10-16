use ril_compiler::{CompilationOutcome, Session};

fn rejects_resize(source: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|d|d.code=="E0301" && d.message.contains("length-changing"))),
        "{source}: {outcome:?}"
    );
}

#[test]
fn all_length_changing_operations_require_dynamic_storage() {
    for operation in [
        "Array::push(mut values, 3)",
        "Array::insert(mut values, 0, 3)",
        "let result=Array::pop(mut values)",
        "let result=Array::remove(mut values, 0)",
        "Array::truncate(mut values, 0)",
        // The signature requires dynamic storage even for an actual no-op.
        "Array::truncate(mut values, 2)",
        "Array::truncate(mut values, 10)",
    ] {
        rejects_resize(&format!(
            "fn example(){{let mut values:[2]int=[1,2];{operation}}}"
        ));
    }
    rejects_resize("fn example(){let mut values:[0]int=[];let result=Array::pop(mut values)}");
}

#[test]
fn aliases_helpers_and_clone_cannot_erase_the_storage_shape() {
    for source in [
        "fn example(){let mut values:[2]int=[1,2];let mut alias:[]int= ^mut values;alias !> Array::push(3)}",
        "fn append(mut values:[]int) &mut {values !> Array::push(3)}\nfn example(){let mut values:[2]int=[1,2];append(mut values)}",
        "fn example(){let values:[2]int=[1,2];let mut copied=clone(values);copied !> Array::push(3)}",
        "fn example(){let values:([2]int,[]int)=([1,2],[3]);let mut copied=clone(values);copied.0 !> Array::push(4)}",
        "meta let VALUES:[2]int=[1,2]\nfn example() &{VALUES}{let mut copied=clone(VALUES);copied !> Array::push(3)}",
    ] {
        rejects_resize(source);
    }
}

#[test]
fn fixed_elements_and_new_dynamic_shells_remain_mutable() {
    let source = r#"
fn replace(mut values:[2]int) &mut {values[0]=7}
fn example(){
    let mut values:[2]int=[1,2]
    replace(mut values)
    values[1]=8
    let mut reversed=Array::reverse(values)
    reversed !> Array::push(9)
    assert(values==[7,8] && reversed==[8,7,9])
    let mut combined=Array::concat(values,values)
    combined !> Array::truncate(1)
    assert(combined==[7])
}
"#;
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
}
