#![forbid(unsafe_code)]

use std::{path::PathBuf, sync::Arc};

use ril_driver::{AVAILABLE, Driver};

fn main() {
    if let Some(status) = ril_driver::worker_entry() {
        std::process::exit(status);
    }
    let root =
        std::env::var_os("RIL_TEST_ROOT").map_or_else(|| PathBuf::from("tests"), PathBuf::from);
    ril_test::run_harness(&root, Arc::new(Driver), AVAILABLE)
}
