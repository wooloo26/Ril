"""Run the project's checks with all configuration and caches kept here."""

import subprocess
import sys

from doc_check.cli import PROJECT, find_root


def main() -> int:
    commands = [
        ("format", ["ruff", "format", "--check", "."]),
        ("lint", ["ruff", "check", "."]),
        ("types", ["mypy"]),
        ("tests", ["pytest"]),
        ("documents", ["doc_check", "--root", str(find_root(PROJECT))]),
    ]
    failed: list[str] = []
    for name, command in commands:
        print(f"\n>>> {name}", flush=True)
        result = subprocess.run([sys.executable, "-m", *command], cwd=PROJECT, check=False)
        if result.returncode:
            failed.append(name)
    if failed:
        print(f"\nFailed: {', '.join(failed)}", file=sys.stderr)
        return 1
    print("\nAll quality checks passed.")
    return 0
