"""Build the access/provenance core, check examples, and audit proof dependencies."""

import argparse
import subprocess
import tempfile
from pathlib import Path

PROJECT = Path(__file__).resolve().parent


def run(*command: str) -> None:
    subprocess.run(command, cwd=PROJECT, check=True)


def audit_rejection(body: str, expected: str) -> None:
    # Only generated files in this project's ignored build directory are removed.
    with tempfile.TemporaryDirectory(prefix="audit-test-", dir=PROJECT / ".lake") as directory:
        probe = Path(directory) / "Probe.lean"
        probe.write_text(
            "import RilAccess\nimport AuditSupport\n"
            f"namespace RilAccess\n{body}\nend RilAccess\naudit_ril_access\n",
            encoding="utf-8",
        )
        result = subprocess.run(
            ["lake", "env", "lean", str(probe)],
            cwd=PROJECT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        if result.returncode == 0 or expected not in result.stdout:
            raise RuntimeError(f"Audit self-test did not reject as expected:\n{result.stdout}")
        print(f"PASS audit rejects {expected}", flush=True)


def main() -> None:
    argparse.ArgumentParser(description=__doc__).parse_args()
    run("lake", "build")
    run("lake", "exe", "access-check")
    # Replay the audit rather than merely running a previously built executable.
    run("lake", "env", "lean", "Audit.lean")
    audit_rejection("axiom auditProbe : False", "Unproved project axiom")
    audit_rejection("theorem auditProbe : False := by sorry", "Forbidden axiom sorryAx")
    audit_rejection("unsafe def auditProbe : Nat := 0", "Unsafe project declaration")
    audit_rejection("theorem auditProbe : (0 : Nat) = 0 := by native_decide", "Forbidden axiom")


if __name__ == "__main__":
    main()
