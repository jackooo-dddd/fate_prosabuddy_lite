"""Mode-aware prompts kept separate from agent control flow."""

from __future__ import annotations

from .benchmark_adapter import BenchmarkProblem
from .config import AgentMode
from .proving_skills import ActivatedSkill


BASE_SYSTEM_PROMPT = """You are proving one mathematical theorem in Lean 4 with Mathlib.

Return only a complete Lean proof body beginning with `by`.
Do not use `sorry`, `admit`, `by?`, `exact?`, new axioms, opaque assumptions,
fake hypotheses, or changes to the theorem statement.
Use only declarations available in the imported environment.
The proof is correct only if Lean compiles the unchanged theorem source."""

ENHANCED_DISCIPLINE = """Enhanced repair discipline:
- Fix the first reliable Lean failure before reacting to later cascading errors.
- Make one meaningful local repair and preserve compiler-certified progress.
- After a structural tactic, reason from the actual remaining goals.
- Never treat a partial proof as final success."""


def build_generation_messages(
    problem: BenchmarkProblem,
    mode: AgentMode,
    *,
    previous_proof: str | None = None,
    primary_error: str | None = None,
    failure_class: str | None = None,
    skill: ActivatedSkill | None = None,
    retrieval_context: str | None = None,
) -> list[dict[str, str]]:
    """Build a whole-proof initial or repair prompt for the selected mode."""

    system = BASE_SYSTEM_PROMPT
    if mode.is_enhanced:
        system += "\n\n" + ENHANCED_DISCIPLINE
    body = [
        f"Benchmark: {problem.benchmark}",
        f"Problem ID: {problem.problem_id}",
        f"Theorem name: {problem.theorem_name}",
    ]
    if problem.informal_statement:
        body.append(f"Informal statement:\n{problem.informal_statement}")
    body.append(f"Exact Lean source with the target hole:\n{problem.source_text}")
    if previous_proof is not None:
        body.append(f"Previous candidate proof:\n{previous_proof}")
    if primary_error is not None:
        body.append(
            "First reliable Lean diagnostic"
            + (f" ({failure_class})" if failure_class else "")
            + f":\n{primary_error}"
        )
    if retrieval_context:
        body.append(retrieval_context)
    if skill:
        body.append(f"Activated proving skill [{skill.name}]:\n{skill.text}")
    return [
        {"role": "system", "content": system},
        {"role": "user", "content": "\n\n".join(body)},
    ]


def build_prefix_messages(
    problem: BenchmarkProblem,
    certified_prefix: str,
    remaining_goal: str,
    *,
    primary_error: str | None,
    skill: ActivatedSkill | None,
    retrieval_context: str | None,
) -> list[dict[str, str]]:
    """Ask for only the suffix following a compiler-certified proof prefix.
    Don’t ask the LLM to rewrite the entire proof if Lean has already verified 
    that the beginning of the proof is correct."""

    system = BASE_SYSTEM_PROMPT + "\n\n" + ENHANCED_DISCIPLINE
    body = f"""Benchmark: {problem.benchmark}
Problem ID: {problem.problem_id}
Exact theorem source:
{problem.source_text}

The following proof prefix is already compiler-certified. Do not rewrite it.
Certified prefix:
{certified_prefix}

Current remaining goal(s):
{remaining_goal}

First diagnostic:
{primary_error or 'Only unfinished goals remain.'}

Return only the continuation tactics to append after the certified prefix.
Do not begin with `by` and do not repeat the prefix."""
    if retrieval_context:
        body += "\n\n" + retrieval_context
    if skill:
        body += f"\n\nActivated proving skill [{skill.name}]:\n{skill.text}"
    return [
        {"role": "system", "content": system},
        {"role": "user", "content": body},
    ]

