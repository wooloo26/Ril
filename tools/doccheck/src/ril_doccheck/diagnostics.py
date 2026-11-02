"""Stable, editor-friendly diagnostics shared by the checkers."""

from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True, order=True)
class Diagnostic:
    path: Path
    line: int
    column: int
    code: str
    message: str

    def render(self, root: Path) -> str:
        path = self.path.relative_to(root) if self.path.is_relative_to(root) else self.path
        return f"{path.as_posix()}:{self.line}:{self.column}: {self.code} {self.message}"
