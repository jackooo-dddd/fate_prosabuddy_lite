"""Structured Lean compiler wrapper used as the proof oracle."""

from __future__ import annotations

import re
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path

from .benchmark_adapter import BenchmarkAdapter, BenchmarkProblem


_LOCATED_ERROR_RE = re.compile(
    r"(?ms)^.*?\.lean:(?P<line>\d+):(?P<column>\d+): "
    r"error(?:\([^\n)]*\))?:\s*"
    r"(?P<message>.*?)(?=^.*?\.lean:\d+:\d+: "
    r"(?:error(?:\([^\n)]*\))?|warning(?:\([^\n)]*\))?):|\Z)"
)
_GENERIC_ERROR_RE = re.compile(r"(?is)\berror:\s*(.+)")
_UNSOLVED_RE = re.compile(
    r"(?ms)unsolved goals?\s*\n(?P<goals>.*?)(?=^.*?\.lean:\d+:\d+: "
    r"(?:error(?:\([^\n)]*\))?|warning(?:\([^\n)]*\))?):|\Z)"
)


@dataclass(frozen=True)
class LeanCheckResult:
    """Structured result for one exact Lean compiler invocation."""

    success: bool
    return_code: int
    stdout: str
    stderr: str
    primary_error: str | None
    error_line: int | None
    error_column: int | None
    unsolved_goals: list[str]
    runtime: float
    scratch_file: Path


class LeanRunner:
    """Save candidate sources and compile them inside a benchmark workspace."""

    def __init__(
        self,
        adapter: BenchmarkAdapter,
        scratch_root: Path,
        timeout_seconds: float = 180.0,
    ) -> None:
        self.adapter = adapter
        self.scratch_root = scratch_root.resolve()
        self.timeout_seconds = timeout_seconds
        self.scratch_root.mkdir(parents=True, exist_ok=True)
        self.compiler_calls = 0

    def check_proof(
        self,
        problem: BenchmarkProblem,
        proof: str,
        run_id: str,
        label: str,
    ) -> LeanCheckResult:
        """Build the exact benchmark source and compile it."""

        return self.check_source(
            problem,
            self.adapter.build_source(problem, proof),
            run_id,
            label,
        )

    def check_source(
        self,
        problem: BenchmarkProblem,
        source: str,
        run_id: str,
        label: str,
    ) -> LeanCheckResult:
        """Compile already-built source while preserving it for later audit."""

        run_dir = self.scratch_root / run_id / problem.problem_id
        run_dir.mkdir(parents=True, exist_ok=True)
        safe_label = re.sub(r"[^A-Za-z0-9_.-]", "_", label)
        scratch_file = run_dir / f"{safe_label}.lean"
        scratch_file.write_text(source, encoding="utf-8")
        self.compiler_calls += 1
        started = time.perf_counter()
        try:
            completed = subprocess.run(
                ["lake", "env", "lean", str(scratch_file)],
                cwd=self.adapter.workspace(),
                capture_output=True,
                text=True,
                timeout=self.timeout_seconds,
                check=False,
            )
            runtime = time.perf_counter() - started
            return _structure_result(
                completed.returncode,
                completed.stdout,
                completed.stderr,
                runtime,
                scratch_file,
            )
        except subprocess.TimeoutExpired as error:
            runtime = time.perf_counter() - started
            stdout = _decode_stream(error.stdout)
            stderr = _decode_stream(error.stderr)
            stderr += f"\nLean timed out after {self.timeout_seconds:.1f} seconds."
            return _structure_result(124, stdout, stderr, runtime, scratch_file)


def _structure_result(
    return_code: int,
    stdout: str,
    stderr: str,
    runtime: float,
    scratch_file: Path,
) -> LeanCheckResult:
    """Extract the first reliable error location and any reported goals."""

    combined = "\n".join(part for part in (stdout.strip(), stderr.strip()) if part)
    located = _LOCATED_ERROR_RE.search(combined)
    primary_error: str | None = None
    error_line: int | None = None
    error_column: int | None = None
    if located:
        primary_error = located.group("message").strip()
        error_line = int(located.group("line"))
        error_column = int(located.group("column"))
    elif generic := _GENERIC_ERROR_RE.search(combined):
        primary_error = generic.group(1).strip().splitlines()[0]

    goals: list[str] = []
    for match in _UNSOLVED_RE.finditer(combined):
        goal = match.group("goals").strip()
        if goal and goal not in goals:
            goals.append(goal)

    return LeanCheckResult(
        success=return_code == 0,
        return_code=return_code,
        stdout=stdout,
        stderr=stderr,
        primary_error=primary_error,
        error_line=error_line,
        error_column=error_column,
        unsolved_goals=goals,
        runtime=runtime,
        scratch_file=scratch_file,
    )


def _decode_stream(value: str | bytes | None) -> str:
    if value is None:
        return ""
    return value.decode(errors="replace") if isinstance(value, bytes) else value
