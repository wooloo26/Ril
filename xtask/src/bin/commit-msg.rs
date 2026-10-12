use std::{path::PathBuf, process::ExitCode};
fn main() -> ExitCode {
    let mut args = std::env::args_os().skip(1);
    let Some(path) = args.next() else {
        eprintln!("Expected the commit message file.");
        return ExitCode::FAILURE;
    };
    if path == "--ril-hook-version" {
        println!("{}", xtask::hooks::HOOK_ID);
        return ExitCode::SUCCESS;
    }
    if args.next().is_some() {
        eprintln!("Expected one commit message file.");
        return ExitCode::FAILURE;
    }
    match xtask::hooks::check_file(&PathBuf::from(path)) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}
