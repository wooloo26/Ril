#![no_main]

use libfuzzer_sys::fuzz_target;
use ril_driver::Driver;
use ril_test::{Stage, Unit, VirtualPackage};

fuzz_target!(|data: &[u8]| {
    let mut pkg = VirtualPackage::new(Unit::Lib);
    pkg.entry = "pkg/fuzz.ril".into();
    pkg.budget = Some(1024);
    pkg.insert("pkg/fuzz.ril".into(), data.to_vec());
    let _ = Driver.check(&pkg, Stage::Access);
});
