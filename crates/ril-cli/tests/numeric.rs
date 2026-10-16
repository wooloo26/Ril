use std::{fs, process::Command};

fn execute(source_text: &str) -> serde_json::Value {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("numeric.ril");
    fs::write(&source, source_text).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&source)
        .args(["--entry", "test_numeric", "--json"])
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

#[test]
fn contextual_literals_use_the_verified_integer_width_and_float_format() {
    let result = execute(
        r#"
fn inc(value:i8)->i8 { value+1 }
fn plus(value:f32)->f32 { value+1.0 }
fn small()->u8 { return 255 }
fn small_tail()->u8 { 255 }
pub fn test_numeric() {
    assert(small()==255u8 && small_tail()==255u8)
    assert(inc(126)==127i8)
    let minimum:i8=-128
    assert(minimum==-128i8)
    let values:[]u8=[1,2]
    assert(values[0]==1u8)
    let f:f32=1.25
    assert(plus(f)==2.25f32)
}
"#,
    );
    assert_eq!(result["runtime"], "returned-unit", "{result}");
}

#[test]
fn contextual_integer_overflow_is_a_language_panic() {
    let result = execute("fn tiny()->i8 { 127+1 }\npub fn test_numeric(){let value=tiny()}");
    assert_eq!(result["runtime"], "language-panic", "{result}");
}

#[test]
fn local_meta_aggregates_and_explicit_ints_keep_their_evaluated_numeric_types() {
    let result = execute(
        r#"
pub fn test_numeric(){
    meta let PAIR=(1int,2)
    meta let ITEMS=[3int,4]
    meta let FLOATS=(16777217.0f32,16777217.0f64)
    let explicit=5_int
    assert(PAIR.0+PAIR.1==3int && ITEMS[0]+ITEMS[1]==7int)
    assert(explicit+PAIR.0==6int)
    assert("{FLOATS.0}"=="16777216.0" && "{FLOATS.1}"=="16777217.0")
}
"#,
    );
    assert_eq!(result["runtime"], "returned-unit", "{result}");
}

#[test]
fn uppercase_integer_prefixes_cross_static_and_native_literal_paths() {
    let result = execute(
        r#"
meta let STATIC=(0XFEint,0O17,0B1010)
meta let BIG=0X1_0000_0000_0000_0000bigint
meta let _=assert(STATIC==(254int,15int,10int))
meta let _=assert(BIG==18446744073709551616bigint)
type Buffer=[0X2]int
type Token<n:int>(int)
meta let _=assert(type<Token<0B10>>==type<Token<0O2>>)
meta let _=assert(type<Token<0X2>>==type<Token<2int>>)
halt fn down(n:int)->int{if n>0B0{down(n-0O1)}else{0X0}}
pub fn test_numeric() &{STATIC,BIG}{
    meta let LOCAL=(0XEEint,0O20,0B1111)
    assert(STATIC==(254int,15int,10int) && LOCAL==(238int,16int,15int))
    assert(0XEE+0B1==0O357 && 0XEE-0B1==0O355)
    assert(0X1E+1int==31int && 0X1E-1int==29int)
    assert(-0X80_i8==-128i8 && 0O377_u8==255u8 && 0B1111_1111u8==255u8)
    assert(0XFFFF_FFFF_FFFF_FFFFu64==18446744073709551615u64)
    assert(0X1_0000_0000_0000_0000bigint==BIG)
    assert(-0O20bigint==-16bigint && 0B10000bigint==16bigint)
    let values:Buffer=[7int,9int]
    assert(values[0B1]==9int && down(0X10)==0int)
    assert(match 0X2{0B1->false,0O2->true,_->false})
    assert(0X2 is 0B1..=0O3)
}
"#,
    );
    assert_eq!(result["runtime"], "returned-unit", "{result}");
}

#[test]
fn selected_integer_literals_reach_native_float_wide_and_aggregate_representations() {
    let result = execute(
        r#"
fn answer()->f32{16777217}
fn early()->u64{return 18446744073709551615}
fn choose(flag:bool)->f32{if flag{16777217}else{ -16777217}}
pub fn test_numeric(){
    let single:f32=16777217
    let negative:f32=-16777217
    let negative_zero:f32=-0
    let wide:u64=18446744073709551615
    let huge:bigint=340282366920938463463374607431768211456
    let large_float:f64=340282366920938463463374607431768211456
    let precise:f32=0X80000080000000000000000000000001
    assert("{single}"=="16777216.0" && "{negative}"=="-16777216.0")
    assert("{negative_zero}"=="-0.0")
    assert(wide==18446744073709551615u64 && huge==340282366920938463463374607431768211456bigint)
    assert(large_float==340282366920938463463374607431768211456.0f64)
    assert(precise==170141203742878835383357727663135391744.0f32)
    let array:[]f32=[16777217,1]
    let tuple:(f32,u64)=(16777217,18446744073709551615)
    let map:[int:f32]=[0:16777217]
    let record:{value:f32}=.{value:16777217}
    let block:f32={let untouched=1;16777217}
    assert(array[0]==single && array[1]==1.0f32)
    assert(tuple.0==single && tuple.1==wide && map[0]==Some(single))
    assert(record.value==single && block==single)
    assert(answer()==single && early()==wide)
    assert(choose(true)==single && choose(false)==negative)
}
"#,
    );
    assert_eq!(result["runtime"], "returned-unit", "{result}");
}
