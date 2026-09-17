"""Proof extraction and centralized proof-integrity checks."""

from __future__ import annotations

import re
from dataclasses import dataclass


_FENCED_RE = re.compile(r"```(?:lean4?|Lean4?)?\s*(.*?)```", re.DOTALL)
_BY_RE = re.compile(r"(?m)^\s*by\b")
_PROHIBITED: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("sorry", re.compile(r"\bsorry\b", re.I)),
    ("admit", re.compile(r"\badmit\b", re.I)),
    ("axiom declaration", re.compile(r"\baxiom\b", re.I)),
    ("opaque declaration", re.compile(r"\bopaque\b", re.I)),
    ("unsafe declaration", re.compile(r"\bunsafe\b", re.I)),
    ("fake declaration", re.compile(r"\b(?:theorem|lemma|variable|parameter)\b", re.I)),
    ("unfinished tactic suggestion", re.compile(r"\b(?:by|exact|apply|rw|simp|aesop)\?")),
)


@dataclass(frozen=True)
class ProofEvaluation:
    """State whether a candidate is eligible to count as a solved theorem."""

    success: bool
    rejection_reason: str | None = None


def extract_proof(model_output: str) -> str:
    """Extract the first proof body beginning with `by`, tolerating code fences."""

    text = model_output.strip()
    fenced = _FENCED_RE.search(text)
    if fenced:
        text = fenced.group(1).strip()
    match = _BY_RE.search(text)
    if not match:
        raise ValueError("Model output does not contain a proof beginning with `by`")
    return text[match.start() :].strip()


def prohibited_construct(proof: str) -> str | None:
    """Return the first proof bypass detected in generated text."""

    for label, pattern in _PROHIBITED:
        if pattern.search(proof):
            return label
    return None


def evaluate_candidate(proof: str, lean_success: bool) -> ProofEvaluation:
    """Require both proof integrity and successful Lean compilation."""

    prohibited = prohibited_construct(proof)
    if prohibited:
        return ProofEvaluation(False, f"Prohibited construct detected: {prohibited}")
    if not lean_success:
        return ProofEvaluation(False, "Lean rejected the candidate proof")
    return ProofEvaluation(True)
