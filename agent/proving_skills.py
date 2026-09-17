"""Small, failure-triggered proving skills adapted from ProsaBuddy principles."""

from __future__ import annotations

from dataclasses import dataclass

from .error_classifier import LeanFailureKind


GOAL_DRIVEN_APPLY = """Goal-driven lemma application:
Audit a verified lemma's conclusion and premises. If its conclusion matches the
current goal, prefer `apply`, `refine`, or `simpa using` so Lean exposes the real
remaining subgoals. Do not guess every implicit argument up front."""

REWRITE_SHAPE = """Rewrite-shape discipline:
A failed rewrite means the literal goal shape does not match the lemma. Inspect
the exact target and lemma type first; normalize, unfold, or choose a bridge only
when that makes the required subterm actually present."""

GOAL_BRANCH = """Goal/branch discipline:
After `constructor`, `cases`, `rcases`, `by_cases`, `induction`, `apply`, or
`refine`, reason from Lean's actual remaining goals. Do not assume a linear proof
state or continue tactics meant for a branch that already closed."""

SMALL_STEP = """First-error small-step discipline:
Fix the first reliable Lean failure with one meaningful local change, then
recompile. Preserve compiler-certified progress instead of rewriting unrelated
parts of the proof."""


@dataclass(frozen=True)
class ActivatedSkill:
    """Record the name and compact prompt text of one selected skill."""

    name: str
    text: str


def activate_skill(
    failure: LeanFailureKind | None,
    *,
    repeated_failure: bool = False,
    has_certified_prefix: bool = False,
    has_verified_retrieval: bool = False,
) -> ActivatedSkill | None:
    """Select at most one skill from the current first-error signal."""

    if has_certified_prefix:
        return ActivatedSkill("small_step_prefix_repair", SMALL_STEP)
    if has_verified_retrieval:
        return ActivatedSkill("goal_driven_apply", GOAL_DRIVEN_APPLY)
    if failure in {
        LeanFailureKind.APPLICATION_MISMATCH,
        LeanFailureKind.INSTANCE_SYNTHESIS,
        LeanFailureKind.UNKNOWN_IDENTIFIER,
    }:
        return ActivatedSkill("goal_driven_apply", GOAL_DRIVEN_APPLY)
    if failure is LeanFailureKind.REWRITE_MISMATCH:
        return ActivatedSkill("rewrite_shape", REWRITE_SHAPE)
    if failure is LeanFailureKind.UNSOLVED_GOALS:
        return ActivatedSkill("goal_branch_discipline", GOAL_BRANCH)
    if repeated_failure:
        return ActivatedSkill("first_error_small_step", SMALL_STEP)
    return None
