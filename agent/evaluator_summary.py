"""Aggregate problem-level outcomes for one experimental condition."""

from __future__ import annotations

from collections.abc import Iterable

from .proof_agent import ProblemRunResult


def summarize_results(
    results: Iterable[ProblemRunResult],
    *,
    benchmark: str,
    mode: str,
    model: str,
) -> dict[str, object]:
    """Compute success, call, token, compiler, and runtime totals."""

    rows = list(results)
    solved = [row for row in rows if row.success]
    total = len(rows)
    return {
        "benchmark": benchmark,
        "mode": mode,
        "model": model,
        "total_problems": total,
        "solved_problems": len(solved),
        "solve_rate": len(solved) / total if total else 0.0,
        "average_attempts": sum(row.attempts for row in rows) / total if total else 0.0,
        "average_attempts_among_solved": (
            sum(row.attempts for row in solved) / len(solved) if solved else 0.0
        ),
        "proof_generation_api_calls": sum(row.api_calls for row in rows),
        "retrieval_tool_calls": sum(row.retrieval_tool_calls for row in rows),
        "lean_compiler_calls": sum(row.lean_calls for row in rows),
        "input_tokens": sum(row.input_tokens for row in rows),
        "output_tokens": sum(row.output_tokens for row in rows),
        "total_tokens": sum(row.total_tokens for row in rows),
        "runtime": sum(row.runtime for row in rows),
        "problems": [row.to_summary_dict() for row in rows],
    }

