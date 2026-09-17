"""Benchmark-neutral problem interface and the FATE-M implementation."""

from __future__ import annotations

import json
import re
from abc import ABC, abstractmethod
from dataclasses import dataclass
from pathlib import Path


_PROOF_HOLE_RE = re.compile(r"(?m)(?P<assign>:=\s*)(?P<proof>by\s*\n\s*sorry\b)")
_THEOREM_RE = re.compile(r"(?m)^\s*(?:theorem|lemma)\s+(?P<name>[^\s:{(]+)")


@dataclass(frozen=True)
class BenchmarkProblem:
    """Represent one immutable benchmark theorem and its exact source context."""

    problem_id: str
    benchmark: str
    theorem_name: str
    theorem_statement: str
    informal_statement: str | None
    source_path: Path
    source_text: str
    proof_start: int
    proof_end: int

    @property
    def source_without_solution(self) -> str:
        """Return the original source with its placeholder visibly retained."""

        return self.source_text


class BenchmarkAdapter(ABC):
    """Define how a benchmark exposes problems and constructs candidate files."""

    @abstractmethod
    def load_problems(self) -> list[BenchmarkProblem]:
        """Load problems in a deterministic benchmark-defined order."""

    @abstractmethod
    def build_source(self, problem: BenchmarkProblem, proof: str) -> str:
        """Insert a proof without changing the original theorem declaration."""

    @abstractmethod
    def workspace(self) -> Path:
        """Return the directory whose Lake environment compiles the benchmark."""


class FateMAdapter(BenchmarkAdapter):
    """Load FATE-M's individual numbered Lean files without reconstructing them."""

    def __init__(self, root: Path) -> None:
        self.root = root.resolve()

    def workspace(self) -> Path:
        return self.root

    def load_problems(self) -> list[BenchmarkProblem]:
        """Load all 150 files in numeric ID order and validate one proof hole each."""

        metadata = self._load_metadata()
        paths = sorted(
            (self.root / "FATEM").glob("*.lean"),
            key=lambda path: int(path.stem),
        )
        problems = [self._load_file(path, metadata.get(path.stem)) for path in paths]
        if not problems:
            raise ValueError(f"No FATE-M problem files found under {self.root / 'FATEM'}")
        return problems

    def build_source(self, problem: BenchmarkProblem, proof: str) -> str:
        """Replace only `by\n  sorry`; every other source byte remains unchanged."""

        candidate = proof.strip()
        if not re.match(r"^by\b", candidate):
            raise ValueError("Candidate proof must begin with `by`")
        return (
            problem.source_text[: problem.proof_start]
            + candidate
            + problem.source_text[problem.proof_end :]
        )

    def get_problem(self, problem_id: str) -> BenchmarkProblem:
        """Find a problem by numeric ID, filename stem, or theorem name."""

        normalized = problem_id.removeprefix("FATEM/").removesuffix(".lean")
        for problem in self.load_problems():
            if normalized in {problem.problem_id, problem.theorem_name}:
                return problem
        raise ValueError(f"FATE-M problem not found: {problem_id}")

    def _load_metadata(self) -> dict[str, dict[str, object]]:
        rows = json.loads((self.root / "FATE-M.json").read_text(encoding="utf-8"))
        return {str(row["id"]): row for row in rows}

    def _load_file(
        self, path: Path, metadata: dict[str, object] | None
    ) -> BenchmarkProblem:
        source = path.read_text(encoding="utf-8")
        holes = list(_PROOF_HOLE_RE.finditer(source))
        if len(holes) != 1:
            raise ValueError(f"Expected exactly one `by sorry` proof hole in {path}")
        theorem = _THEOREM_RE.search(source)
        if theorem is None:
            raise ValueError(f"No theorem declaration found in {path}")
        hole = holes[0]
        statement = source[: hole.start("proof")].rstrip()
        return BenchmarkProblem(
            problem_id=path.stem,
            benchmark="FATE-M",
            theorem_name=theorem.group("name"),
            theorem_statement=statement,
            informal_statement=(str(metadata["informal_statement"]) if metadata else None),
            source_path=path,
            source_text=source,
            proof_start=hole.start("proof"),
            proof_end=hole.end("proof"),
        )

