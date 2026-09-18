"""Compiler-certified prefix discovery and suffix assembly."""

from __future__ import annotations

import re
from dataclasses import dataclass

from .benchmark_adapter import BenchmarkProblem
from .error_classifier import LeanFailureKind, classify_failure
from .evaluator import extract_proof, prohibited_construct
from .lean_runner import LeanCheckResult, LeanRunner


"""
Assume a Lean proof of the form:
theorem foo (a b c : Nat)
    (h1 : a = b)
    (h2 : b = c) :
    a = c := by
  rw [h1]
  rw [h2]
  exact Nat.zero_le c
The last line is nonsense. Lean effectively reaches:
rw [h1]
rw [h2]
goal:
⊢ c = c
So prefix repair can certify:
by
  rw [h1]
  rw [h2]
and tell DeepSeek this prefix is already valid:
by
  rw [h1]
  rw [h2]
Current goal:
⊢ c = c
Return only continuation tactics.

The model might return: rfl
Then assemble_suffix() combines:
by
  rw [h1]
  rw [h2]
  rfl
and runs Lean again.
"""
@dataclass(frozen=True)
class PrefixCertification:
    """A proof prefix whose only compiler complaint is unfinished goals."""

    prefix: str
    prefix_length: int
    remaining_goal: str
    check_result: LeanCheckResult
    chunks: int


@dataclass(frozen=True)
class SuffixAssembly:
    """Record how a model continuation was combined with certified state."""

    proof: str
    suffix: str
    prefix_abandoned: bool


def split_tactic_chunks(proof: str) -> list[str]:
    """Split a `by` proof conservatively at top-level indentation boundaries."""

    lines = proof.strip().splitlines()
    if not lines or lines[0].strip() != "by":
        return []
    body = lines[1:]
    nonempty = [line for line in body if line.strip()]
    if not nonempty:
        return []
    base_indent = min(len(line) - len(line.lstrip()) for line in nonempty)
    chunks: list[list[str]] = []
    current: list[str] = []
    for line in body:
        indent = len(line) - len(line.lstrip()) if line.strip() else base_indent + 1
        if line.strip() and indent == base_indent and current:
            chunks.append(current)
            current = []
        current.append(line)
    if current:
        chunks.append(current)
    return ["\n".join(chunk).rstrip() for chunk in chunks if any(x.strip() for x in chunk)]


class PrefixRepairer:
    """Find the longest semantically valid prefix before the first failing chunk."""

    def __init__(self, runner: LeanRunner, validation_limit: int = 4) -> None:
        self.runner = runner
        self.validation_limit = validation_limit

    def certify(
        self,
        problem: BenchmarkProblem,
        proof: str,
        failed_result: LeanCheckResult,
        run_id: str,
        attempt: int,
    ) -> PrefixCertification | None:
        """Compile decreasing prefixes until Lean reports only unsolved goals."""

        if prohibited_construct(proof):
            return None
        chunks = split_tactic_chunks(proof)
        if not chunks:
            return None
        candidate_count = self._candidate_chunk_count(problem, proof, failed_result, chunks)
        tested = 0
        for count in range(candidate_count, 0, -1):
            if tested >= self.validation_limit:
                break
            prefix = "by\n" + "\n".join(chunks[:count])
            result = self.runner.check_proof(
                problem,
                prefix,
                run_id,
                f"attempt_{attempt}_prefix_{count}",
            )
            tested += 1
            if (
                not result.success
                and classify_failure(result.primary_error) is LeanFailureKind.UNSOLVED_GOALS
            ):
                remaining = "\n\n".join(result.unsolved_goals) or (
                    result.primary_error or "Unfinished goals remain."
                )
                return PrefixCertification(
                    prefix=prefix,
                    prefix_length=len(prefix),
                    remaining_goal=remaining,
                    check_result=result,
                    chunks=count,
                )
        return None

    @staticmethod
    def _candidate_chunk_count(
        problem: BenchmarkProblem,
        proof: str,
        failed_result: LeanCheckResult,
        chunks: list[str],
    ) -> int:
        # Lean locates a final `unsolved goals` error at the theorem declaration,
        # not necessarily at the last successful tactic. In that case the whole
        # candidate is already a useful semantic prefix and should be certified.
        if classify_failure(failed_result.primary_error) is LeanFailureKind.UNSOLVED_GOALS:
            return len(chunks)
        proof_start_line = problem.source_text[: problem.proof_start].count("\n") + 1
        if failed_result.error_line is None:
            return max(0, len(chunks) - 1)
        relative_error = max(1, failed_result.error_line - proof_start_line + 1)
        running_line = 2
        for index, chunk in enumerate(chunks):
            end_line = running_line + chunk.count("\n")
            if running_line <= relative_error <= end_line:
                return index
            running_line = end_line + 1
        return max(0, len(chunks) - 1)


def assemble_suffix(certified_prefix: str, model_output: str) -> SuffixAssembly:
    """Append a continuation, or explicitly abandon the prefix for a full proof."""

    text = model_output.strip()
    fenced = re.search(r"```(?:lean4?|Lean4?)?\s*(.*?)```", text, re.DOTALL)
    if fenced:
        text = fenced.group(1).strip()
    if re.match(r"^by\b", text):
        normalized_prefix = certified_prefix.strip()
        if text.startswith(normalized_prefix):
            text = text[len(normalized_prefix) :].strip()
        else:
            return SuffixAssembly(extract_proof(text), "", True)
    if not text:
        raise ValueError("Model returned an empty proof continuation")
    suffix_lines = []
    for line in text.splitlines():
        if line.strip() and len(line) - len(line.lstrip()) < 2:
            line = "  " + line.lstrip()
        suffix_lines.append(line)
    suffix = "\n".join(suffix_lines).rstrip()
    return SuffixAssembly(certified_prefix.rstrip() + "\n" + suffix, suffix, False)
