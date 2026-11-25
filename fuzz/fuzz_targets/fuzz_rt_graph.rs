#![no_main]

use libfuzzer_sys::fuzz_target;
use ril_rt_core::{
    Runtime,
    ffi::{ril_rt_array, ril_rt_clone, ril_rt_equal, ril_rt_map_new, ril_rt_map_set},
    gc::Value,
};

fuzz_target!(|data: &[u8]| {
    let mut rt = Runtime::new();
    let ptr = &raw mut rt;
    let map = unsafe { ril_rt_map_new(ptr) };
    let mut items = Vec::new();
    for chunk in data.chunks(2).take(64) {
        let k = Value::from_small_int(i64::from(*chunk.first().unwrap_or(&0))).raw();
        let v = Value::from_small_int(i64::from(*chunk.get(1).unwrap_or(&0))).raw();
        unsafe {
            let _ = ril_rt_map_set(ptr, map, k, v);
        }
        items.push(v);
    }
    let arr = unsafe { ril_rt_array(ptr, items.as_ptr(), items.len()) };
    let cloned = unsafe { ril_rt_clone(ptr, arr) };
    let eq = unsafe { ril_rt_equal(ptr, arr, cloned) };
    assert_eq!(eq, Value::TRUE.raw());
});
