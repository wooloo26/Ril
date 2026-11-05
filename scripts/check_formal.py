"""Build the core, check examples, and audit every project-owned declaration."""

import argparse
import re
import subprocess
import tempfile
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[1] / "formal"


def run(*command: str) -> None:
    subprocess.run(command, cwd=FORMAL, check=True)


def audit_output(path: Path) -> str:
    result = subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=FORMAL,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=True,
    )
    print(result.stdout, end="", flush=True)
    return result.stdout


def verify_imports(output: str, root: Path = FORMAL) -> None:
    actual = set(re.findall(r"Audit module: (RilAccess(?:\.\w+)*)", output))
    expected = {
        ".".join(path.relative_to(root).with_suffix("").parts)
        for path in (root / "RilAccess").rglob("*.lean")
    } | {"RilAccess"}
    missing = expected - actual
    if missing:
        raise RuntimeError("Unaudited project modules: " + ", ".join(sorted(missing)))


def audit_rejection(body: str, expected: str, namespace: str = "RilAccess") -> None:
    # Generated probes and their cleanup stay inside this ignored build directory.
    with tempfile.TemporaryDirectory(prefix="audit-test-", dir=FORMAL / ".lake") as directory:
        probe = Path(directory) / "Probe.lean"
        probe.write_text(
            "import RilAccess\nimport AuditSupport\n"
            f"namespace {namespace}\n{body}\nend {namespace}\naudit_ril_access\n",
            encoding="utf-8",
        )
        result = subprocess.run(
            ["lake", "env", "lean", str(probe)],
            cwd=FORMAL,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        if result.returncode == 0 or expected not in result.stdout:
            raise RuntimeError(f"Audit self-test did not reject as expected:\n{result.stdout}")
        print(f"PASS audit rejects {expected} ({namespace})", flush=True)


def audit_entrypoint(module: str) -> str:
    # Main and Audit both define main; inspect their completed modules separately.
    with tempfile.TemporaryDirectory(prefix="entry-audit-", dir=FORMAL / ".lake") as directory:
        probe = Path(directory) / "Entry.lean"
        probe.write_text(
            f"import {module}\nimport AuditSupport\naudit_ril_access\n", encoding="utf-8"
        )
        output = audit_output(probe)
        verify_imports(output)
        if module not in re.findall(r"Audit module: (\S+)", output):
            raise RuntimeError(f"Unaudited entrypoint module: {module}")
        return output


def trailing_declaration_rejection() -> None:
    # A source-local audit sees only earlier declarations. Import the compiled
    # module to expose even a declaration after its apparent successful audit.
    # Keep the generated module in Lake's actual RilAccess import tree.
    library = FORMAL / ".lake" / "build" / "lib" / "lean"
    with tempfile.TemporaryDirectory(
        prefix="AuditTailProbe", dir=library / "RilAccess"
    ) as directory:
        root = Path(directory)
        source = root / "Probe.lean"
        source.write_text(
            "import Audit\naudit_ril_access\nnamespace OutsideModel\n"
            "axiom afterAudit : False\nend OutsideModel\n",
            encoding="utf-8",
        )
        compiled = subprocess.run(
            [
                "lake",
                "env",
                "lean",
                f"--root={library}",
                "-o",
                str(source.with_suffix(".olean")),
                str(source),
            ],
            cwd=FORMAL,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=True,
        )
        if "Audit passed:" not in compiled.stdout:
            raise RuntimeError("Trailing-declaration probe did not reach its source-local audit")
        try:
            audit_entrypoint(f"RilAccess.{root.name}.Probe")
        except subprocess.CalledProcessError as error:
            if "Unproved project axiom: OutsideModel.afterAudit" not in (error.stdout or ""):
                raise RuntimeError(
                    f"Unexpected trailing-declaration audit failure:\n{error.stdout}"
                ) from error
        else:
            raise RuntimeError("Completed-module audit missed a trailing declaration")
        print("PASS audit rejects declaration after source-local audit", flush=True)


def orphan_rejection(output: str) -> None:
    with tempfile.TemporaryDirectory(prefix="orphan-test-", dir=FORMAL / ".lake") as directory:
        root = Path(directory)
        (root / "RilAccess").mkdir()
        (root / "RilAccess" / "OrphanProbe.lean").write_text(
            "def orphan : Nat := 0\n", encoding="utf-8"
        )
        try:
            verify_imports(output, root)
        except RuntimeError as error:
            if "RilAccess.OrphanProbe" not in str(error):
                raise
        else:
            raise RuntimeError("Import audit failed to reject an orphan source module")
        print("PASS audit rejects unaudited source module", flush=True)


def main() -> None:
    argparse.ArgumentParser(description=__doc__).parse_args()
    run("lake", "build")
    run("lake", "exe", "access-check")
    output = audit_entrypoint("Audit")
    audit_entrypoint("Main")
    audit_rejection("axiom auditProbe : False", "Unproved project axiom")
    audit_rejection("theorem auditProbe : False := by sorry", "Forbidden axiom sorryAx")
    audit_rejection("unsafe def auditProbe : Nat := 0", "Unsafe project declaration")
    audit_rejection("theorem auditProbe : (0 : Nat) = 0 := by native_decide", "Forbidden axiom")
    audit_rejection("axiom auditProbe : False", "Unproved project axiom", "OutsideModel")
    audit_rejection(
        "axiom inherited : False\ntheorem auditProbe : False := inherited",
        "axiom",
        "OutsideModel",
    )
    audit_rejection(
        "def replacement (n : Nat) : Nat := n + 1\n"
        "@[implemented_by replacement] def auditProbe (n : Nat) : Nat := n",
        "Native implementation replacement",
        "OutsideModel",
    )
    audit_rejection(
        '@[extern "lean_nat_add"] def auditProbe (a b : Nat) : Nat := a',
        "Native implementation replacement",
        "OutsideModel",
    )
    trailing_declaration_rejection()
    orphan_rejection(output)


if __name__ == "__main__":
    main()
