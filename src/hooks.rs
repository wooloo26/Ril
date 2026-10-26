use std::{
    fs,
    io::{self, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

pub const HOOK_ID: &str = "RIL_COMMIT_MSG_HOOK_V1";
type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

pub fn validate_message(message: &str) -> Result<()> {
    let message = message.trim_matches(['\r', '\n']);
    if message.is_empty() || message.lines().count() != 1 || message.contains('\r') {
        return Err("Use one nonempty line describing the change, with no body.".into());
    }
    if !message.as_bytes()[0].is_ascii_uppercase() {
        return Err("Start the description with an uppercase ASCII letter.".into());
    }
    if message.chars().any(char::is_control) {
        return Err("The description must not contain control characters.".into());
    }
    if let Some((prefix, _)) = message.split_once(':')
        && !prefix.chars().any(char::is_whitespace)
    {
        return Err("Use a description without a type or scope prefix.".into());
    }
    Ok(())
}

/// Git performs comment stripping, honoring its configured comment character.
pub fn check_file(path: &Path) -> Result<()> {
    let bytes = fs::read(path)?;
    let mut child = Command::new("git")
        .args(["stripspace", "--strip-comments"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()?;
    child.stdin.take().unwrap().write_all(&bytes)?;
    let output = child.wait_with_output()?;
    if !output.status.success() {
        return Err("git stripspace failed".into());
    }
    validate_message(std::str::from_utf8(&output.stdout)?)
}

fn git_path(repo: &Path) -> Result<PathBuf> {
    let output = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(["rev-parse", "--path-format=absolute", "--git-path", "hooks"])
        .output()?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned().into());
    }
    Ok(PathBuf::from(std::str::from_utf8(&output.stdout)?.trim()))
}

fn owned(bytes: &[u8]) -> bool {
    bytes
        .windows(HOOK_ID.len())
        .any(|chunk| chunk == HOOK_ID.as_bytes())
}

/// Installs only this hook, never changes hooksPath or replaces another hook.
pub fn install(repo: &Path, executable: &Path) -> Result<PathBuf> {
    let hooks = git_path(repo)?;
    fs::create_dir_all(&hooks)?;
    let name = if cfg!(windows) {
        "commit-msg.exe"
    } else {
        "commit-msg"
    };
    let destination = hooks.join(name);
    for existing in [hooks.join("commit-msg"), hooks.join("commit-msg.exe")] {
        match fs::symlink_metadata(&existing) {
            Ok(metadata) => {
                if metadata.file_type().is_symlink()
                    || !metadata.is_file()
                    || !owned(&fs::read(&existing)?)
                {
                    return Err(format!(
                        "Refusing to replace an existing hook: {}",
                        existing.display()
                    )
                    .into());
                }
                if existing != destination {
                    return Err(format!(
                        "Remove the obsolete Ril hook before installing: {}",
                        existing.display()
                    )
                    .into());
                }
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error.into()),
        }
    }
    let bytes = fs::read(executable)?;
    if !owned(&bytes) {
        return Err("The source is not a Ril commit-msg executable.".into());
    }
    fs::write(&destination, bytes)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&destination, fs::Permissions::from_mode(0o755))?;
    }
    Ok(destination)
}

pub fn build_and_install(repo: &Path) -> Result<PathBuf> {
    let output = Command::new("cargo")
        .current_dir(repo)
        .args([
            "build",
            "--locked",
            "--bin",
            "ril-commit-msg",
            "--message-format=json",
        ])
        .stderr(Stdio::inherit())
        .output()?;
    if !output.status.success() {
        return Err("Failed to build the commit-msg executable.".into());
    }
    let executable = String::from_utf8(output.stdout)?
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .find_map(|item| {
            if item["reason"] == "compiler-artifact" && item["target"]["name"] == "ril-commit-msg" {
                item["executable"].as_str().map(PathBuf::from)
            } else {
                None
            }
        })
        .ok_or("Cargo did not report the hook executable.")?;
    install(repo, &executable)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validates_descriptions_without_a_length_limit() {
        for text in [
            "Add native backend",
            "Fix tests\r\n",
            "A",
            &format!("Improve {}", "a".repeat(1000)),
        ] {
            assert!(validate_message(text).is_ok(), "{text}");
        }
        for text in [
            "",
            "\n",
            "lowercase",
            "1 Change",
            "中文",
            "Feat: Add backend",
            "Fix(core): Repair parser",
            "Fix!: Break API",
            "Add backend\n\nMore detail",
            "Add backend\nAnother line",
            " Add backend",
            "Add\tbackend",
        ] {
            assert!(validate_message(text).is_err(), "{text:?}");
        }
    }
}
