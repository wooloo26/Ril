#![forbid(unsafe_code)]

use std::{path::Path, sync::Arc};

use libtest_mimic::{Arguments, Failed, Trial};
use ril_driver::{AVAILABLE, Driver};
use ril_test::{Milestone, discover, trials};

fn main() {
    let args = Arguments::from_args();
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests");
    let cases = (|| {
        let milestone = match std::env::var("RIL_TEST_STAGE") {
            Ok(text) => text.parse::<Milestone>()?,
            Err(std::env::VarError::NotPresent) => AVAILABLE,
            Err(err) => return Err(err.to_string()),
        };
        Ok(trials(discover(&path)?, Arc::new(Driver), milestone))
    })()
    .unwrap_or_else(|error: String| {
        vec![Trial::test("suite_discovery", move || {
            Err(Failed::from(error))
        })]
    });
    libtest_mimic::run(&args, cases).exit();
}
