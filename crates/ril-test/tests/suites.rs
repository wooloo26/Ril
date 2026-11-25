#![forbid(unsafe_code)]

use std::{path::Path, sync::Arc};

use ril_driver::{AVAILABLE, CompileOptions, Driver};

fn main() {
    if let Some(status) = ril_driver::worker_entry() {
        std::process::exit(status);
    }
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests");
    let options = CompileOptions {
        opt_stack_promote: std::env::var_os("RIL_OPT_STACK_PROMOTE").is_some(),
        ..CompileOptions::default()
    };
    ril_test::run_harness(&path, Arc::new(Driver.with_options(options)), AVAILABLE)
}
