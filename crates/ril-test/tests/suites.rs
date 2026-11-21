#![forbid(unsafe_code)]

use std::{path::Path, sync::Arc};

use ril_driver::{AVAILABLE, Driver};

fn main() {
    if let Some(status) = ril_driver::worker_entry() {
        std::process::exit(status);
    }
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests");
    ril_test::run_harness(&path, Arc::new(Driver), AVAILABLE)
}
