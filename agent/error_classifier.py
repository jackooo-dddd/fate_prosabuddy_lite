"""Deterministic first-error classification for Lean diagnostics."""

from __future__ import annotations

import re
from enum import Enum


class LeanFailureKind(str, Enum):
    """Coarse failure classes used to select one focused repair skill."""

    SYNTAX = "syntax"
    UNKNOWN_IDENTIFIER = "unknown_identifier"
    TYPE_MISMATCH = "type_mismatch"
    APPLICATION_MISMATCH = "application_mismatch"
    REWRITE_MISMATCH = "rewrite_mismatch"
    INSTANCE_SYNTHESIS = "instance_synthesis"
    UNSOLVED_GOALS = "unsolved_goals"
    TACTIC_FAILURE = "tactic_failure"
    OTHER = "other"


_RULES: tuple[tuple[LeanFailureKind, re.Pattern[str]], ...] = (
    (
        LeanFailureKind.SYNTAX,
        re.compile(r"unexpected token|unexpected end|unexpected identifier|parser", re.I),
    ),
    (LeanFailureKind.UNKNOWN_IDENTIFIER, re.compile(r"unknown identifier|unknown constant", re.I)),
    (LeanFailureKind.APPLICATION_MISMATCH, re.compile(r"application type mismatch|function expected", re.I)),
    (LeanFailureKind.REWRITE_MISMATCH, re.compile(r"tactic ['‘]?rewrite|did not find instance of the pattern|rewrite failed", re.I)),
    (LeanFailureKind.INSTANCE_SYNTHESIS, re.compile(r"failed to synthesize|type class instance", re.I)),
    (LeanFailureKind.TYPE_MISMATCH, re.compile(r"type mismatch|has type.*but is expected", re.I | re.S)),
    (LeanFailureKind.UNSOLVED_GOALS, re.compile(r"unsolved goals?|declaration has metavariables", re.I)),
    (LeanFailureKind.TACTIC_FAILURE, re.compile(r"tactic .* failed|no goals to be solved|no applicable", re.I)),
)


def classify_failure(primary_error: str | None) -> LeanFailureKind | None:
    """Classify the first reliable diagnostic using ordered regex rules."""

    if not primary_error:
        return None
    for kind, pattern in _RULES:
        if pattern.search(primary_error):
            return kind
    return LeanFailureKind.OTHER
