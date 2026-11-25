#![no_main]

use libfuzzer_sys::fuzz_target;
use ril_driver::{CompileOptions, Driver};
use ril_test::{Stage, Unit, VirtualPackage};

fuzz_target!(|data: &[u8]| {
    let mut pkg = VirtualPackage::new(Unit::Bin);
    pkg.budget = Some(512);
    pkg.insert("pkg/main.ril".into(), data.to_vec());
    let compiler = Driver.with_options(CompileOptions {
        opt_stack_promote: true,
        ..CompileOptions::default()
    });
    let _ = compiler.check(&pkg, Stage::Mir);
});
