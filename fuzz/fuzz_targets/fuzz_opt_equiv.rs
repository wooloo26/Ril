#![no_main]

use libfuzzer_sys::fuzz_target;
use ril_driver::{CompileOptions, Driver, OptLevel};
use ril_test::{Unit, VirtualPackage};

fuzz_target!(|data: &[u8]| {
    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.budget = Some(512);
    pkg.insert("pkg/main.ril".into(), data.to_vec());
    let base = Driver.with_options(CompileOptions {
        opt_stack_promote: false,
        opt_level: OptLevel::None,
    });
    let opt = Driver.with_options(CompileOptions {
        opt_stack_promote: true,
        opt_level: OptLevel::Speed,
    });
    let _ = base.lower(&pkg);
    let _ = opt.lower(&pkg);
});
