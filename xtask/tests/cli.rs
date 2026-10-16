use std::{
    fs,
    path::Path,
    process::{Command, Output},
};
fn invoke(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_xtask"))
        .args(args)
        .output()
        .unwrap()
}
#[test]
fn corpus_cli_lists_validates_and_extracts_without_execution() {
    let list = invoke(&["corpus", "list"]);
    assert!(
        list.status.success(),
        "{}",
        String::from_utf8_lossy(&list.stderr)
    );
    let listed = String::from_utf8(list.stdout).unwrap();
    let cases =
        ril_test::discover_cases(&Path::new(env!("CARGO_MANIFEST_DIR")).join("../tests")).unwrap();
    assert_eq!(listed.lines().count(), cases.len());
    assert_eq!(
        cases
            .iter()
            .filter(|case| !case.bundle.starts_with("tests/regressions/"))
            .count(),
        1067
    );
    let valid = invoke(&["corpus", "validate"]);
    assert!(valid.status.success());
    assert!(
        String::from_utf8(valid.stdout)
            .unwrap()
            .contains("semantic executions remain not-run")
    );
    let temp = tempfile::tempdir().unwrap();
    let out = temp.path().join("selected");
    let args = [
        "corpus",
        "extract",
        "tests/conformance/lexical.ril::reject-invalid-leading-byte",
        "--out",
        out.to_str().unwrap(),
    ];
    assert!(invoke(&args).status.success());
    assert_eq!(fs::read(out.join("input.ril")).unwrap(), [255]);
    assert!(!invoke(&args).status.success());
    assert!(
        !invoke(&[
            "corpus",
            "extract",
            "missing",
            "--out",
            temp.path().join("absent").to_str().unwrap()
        ])
        .status
        .success()
    );
    assert!(!invoke(&["--unknown"]).status.success());
}
fn git(repo: &Path, args: &[&str]) -> Output {
    Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(args)
        .output()
        .unwrap()
}
fn repository() -> tempfile::TempDir {
    let temp = tempfile::tempdir().unwrap();
    assert!(git(temp.path(), &["init", "--quiet"]).status.success());
    for (key, value) in [
        ("user.name", "Ril test"),
        ("user.email", "ril-test@example.invalid"),
        ("commit.gpgsign", "false"),
        ("core.hooksPath", ".git/hooks"),
    ] {
        assert!(git(temp.path(), &["config", key, value]).status.success());
    }
    temp
}
#[test]
fn native_hook_is_installed_idempotently_and_git_rejects_invalid_messages() {
    let repo = repository();
    let binary = Path::new(env!("CARGO_BIN_EXE_ril-commit-msg"));
    let hook = xtask::hooks::install(repo.path(), binary).unwrap();
    assert_eq!(xtask::hooks::install(repo.path(), binary).unwrap(), hook);
    let legal = git(
        repo.path(),
        &[
            "commit",
            "--quiet",
            "--allow-empty",
            "-m",
            "Add compiler foundation",
        ],
    );
    assert!(
        legal.status.success(),
        "{}",
        String::from_utf8_lossy(&legal.stderr)
    );
    let head = git(repo.path(), &["rev-parse", "HEAD"]).stdout;
    for message in [
        "lowercase",
        "Feat: Add backend",
        "Add backend\n\nExtra body",
        "",
    ] {
        let rejected = git(
            repo.path(),
            &["commit", "--quiet", "--allow-empty", "-m", message],
        );
        assert!(!rejected.status.success(), "{message}");
        assert_eq!(git(repo.path(), &["rev-parse", "HEAD"]).stdout, head);
    }
    let file = repo.path().join("message");
    let message = b"Improve compiler\r\n\r\n# editor comment\r\n";
    fs::write(&file, message).unwrap();
    assert!(
        Command::new(&hook)
            .current_dir(repo.path())
            .arg(&file)
            .status()
            .unwrap()
            .success()
    );
    assert_eq!(fs::read(&file).unwrap(), message);
    assert!(
        git(repo.path(), &["config", "core.commentChar", ";"])
            .status
            .success()
    );
    fs::write(&file, "Improve tests\n; editor comment\n").unwrap();
    assert!(
        Command::new(&hook)
            .current_dir(repo.path())
            .arg(&file)
            .status()
            .unwrap()
            .success()
    );
}
#[test]
fn installer_respects_custom_paths_and_preserves_other_hooks() {
    let repo = repository();
    let binary = Path::new(env!("CARGO_BIN_EXE_ril-commit-msg"));
    let hooks = repo.path().join("custom hooks");
    assert!(
        git(
            repo.path(),
            &["config", "core.hooksPath", hooks.to_str().unwrap()]
        )
        .status
        .success()
    );
    let installed = xtask::hooks::install(repo.path(), binary).unwrap();
    assert_eq!(installed.parent().unwrap(), hooks);
    fs::write(&installed, "unrelated hook").unwrap();
    assert!(xtask::hooks::install(repo.path(), binary).is_err());
    assert_eq!(fs::read(&installed).unwrap(), b"unrelated hook");
}
