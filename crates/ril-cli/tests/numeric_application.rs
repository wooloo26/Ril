use std::{fs, process::Command};

#[test]
fn receiving_context_selects_arguments_before_their_generic_and_effect_calls() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("numeric-application.ril");
    fs::write(
        &path,
        r#"
eff Read<T>{get(value:T)->T}
fn read<T>(value:T)->T @Read<T>{Read<T>::get(value)}
fn identity<T>(value:T)->T{value}
fn outer<T>(value:T)->f32{identity(16777217)}
fn choose<T>(left:T,right:T)->T{left}
fn sum(left:f32,right:f32)->f32{left+right}
fn wide(value:u64)->u64{value}
type Counter={mut value:int}
fn known_peer(mut counter:Counter)->f32 &mut{counter.value+=1;3.0f32}
fn defaults(value:f32=16777217)->f32{value}
fn budgeted(limit:int)->?f32{
    with Div::exhausted()->None
    Div::budget(limit,\->{let number:f32=identity(16777217);Some(number)})
}
pub fn test_native(){
    var count=0
    let selected:f32=identity({count+=1;16777217})
    assert(count==1 && "{selected}"=="16777216.0")
    let first:f32=choose(right:{count=count*10+1;1+2},left:{count=count*10+2;16777217})
    assert(count==112 && first==selected)
    assert(sum(1+2,3.0f32)==6.0f32)
    let peer=choose(16777217+1,3.0f32)
    assert(peer==selected)
    let nested=choose(identity(16777217),peer)
    assert(nested==selected)
    let mut counter=Counter.{value:0}
    let later=choose(16777217+1,known_peer(mut counter))
    assert(later==selected && counter.value==1)
    assert(wide(18446744073709551615)==18446744073709551615u64)
    assert(defaults()==selected)
    let renamed:fn(other:f32)->f32=defaults
    assert(renamed(other:16777217)==selected)
    assert((\value:f32->value)(16777217)==selected)
    assert(outer("outer T is str")==selected)
    let optional:?f32=Some(16777217)
    assert(optional==Some(selected))
    let result:Result<f32,str>=Ok(16777217)
    assert(result is Ok(selected))
    {
        with Read<f32>::get(value)->resume value
        let answer:f32=read(16777217)
        assert(answer==selected)
        assert(Read<f32>::get(16777217)==selected)
    }
    {
        with Read<int>::get(value)->resume value+1
        assert(read(7)==8)
    }
    assert(budgeted(100)==Some(selected))
    assert(budgeted(0) is None)
}
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&path)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(result["runtime"], "returned-unit", "{result}");
    assert_eq!(result["exit"], 0, "{result}");
}
