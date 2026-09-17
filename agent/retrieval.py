"""Targeted lexical Mathlib retrieval with Lean-verified lemma signatures."""

from __future__ import annotations

import re
import subprocess
from dataclasses import dataclass, replace
from pathlib import Path

from .benchmark_adapter import BenchmarkProblem
from .lean_runner import LeanRunner


_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*(?:(?:protected|private)\s+)?"
    r"(?:theorem|lemma)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)"
)
_NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
_SECTION_RE = re.compile(r"^\s*(?:section|noncomputable\s+section)(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)?\s*$")
_END_RE = re.compile(r"^\s*end(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)?\s*$")
_TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
_STOPWORDS = {
    "theorem", "lemma", "import", "mathlib", "type", "where", "sorry",
    "true", "false", "with", "from", "this", "that", "have", "show",
    "group", "ring", "proof", "exact", "lean", "fate", "forall",
}


@dataclass(frozen=True)
class RetrievedLemma:
    """One local source candidate, optionally verified by the current Lean."""

    name: str
    signature: str
    source_file: str
    verified: bool
    score: float | None = None


@dataclass(frozen=True)
class RetrievalResult:
    """Record why retrieval ran and the candidates it produced."""

    triggered: bool
    reason: str | None
    query: str | None
    candidates: list[RetrievedLemma]
    tool_calls: int = 0

    @property
    def verified(self) -> list[RetrievedLemma]:
        return [candidate for candidate in self.candidates if candidate.verified]


class MathlibRetriever:
    """Search the pinned local Mathlib tree, then verify candidates with Lean."""

    STRUCTURAL_TRIGGERS = {
        "Subgroup", "Normal", "Ideal", "Submodule", "RingHom", "MonoidHom",
        "Quotient", "QuotientGroup", "Polynomial", "LinearMap", "AlgHom",
        "Fintype", "Equiv", "GroupHom", "AddSubgroup",
    }

    def __init__(self, mathlib_root: Path, top_k: int = 6, file_limit: int = 60) -> None:
        self.mathlib_root = mathlib_root.resolve()
        self.top_k = top_k
        self.file_limit = file_limit

    def should_trigger(
        self,
        problem: BenchmarkProblem,
        failure_class: str | None,
        repeated_failure: bool,
    ) -> tuple[bool, str | None]:
        """Trigger on structural first attempts or focused/repeated failures."""

        used_structures = sorted(
            structure for structure in self.STRUCTURAL_TRIGGERS
            if structure in problem.theorem_statement
        )
        if used_structures:
            return True, "structural theorem: " + ", ".join(used_structures)
        if failure_class in {
            "unknown_identifier", "application_mismatch", "instance_synthesis",
            "rewrite_mismatch",
        }:
            return True, f"first-error class: {failure_class}"
        if repeated_failure:
            return True, "repeated failure on the same theorem"
        return False, None

    def retrieve(
        self,
        problem: BenchmarkProblem,
        primary_error: str | None,
        reason: str,
        runner: LeanRunner,
        run_id: str,
        label: str,
    ) -> RetrievalResult:
        """Search, score, and Lean-verify a concise set of candidate lemmas."""

        terms = self._query_terms(problem, primary_error)
        query = " ".join(terms[:8])
        candidates = self._lexical_candidates(terms)
        if not candidates:
            return RetrievalResult(True, reason, query, [], 0)
        verified = self._verify(problem, candidates[: self.top_k], runner, run_id, label)
        return RetrievalResult(True, reason, query, verified, 1)

    def verify_candidates(
        self,
        problem: BenchmarkProblem,
        candidates: list[RetrievedLemma],
        runner: LeanRunner,
        run_id: str,
        label: str = "manual",
    ) -> list[RetrievedLemma]:
        """Public verification hook used by tests and future retrieval strategies."""

        return self._verify(problem, candidates, runner, run_id, label)

    def _query_terms(
        self, problem: BenchmarkProblem, primary_error: str | None
    ) -> list[str]:
        declaration_match = re.search(
            r"(?m)^\s*(?:theorem|lemma)\s+", problem.theorem_statement
        )
        formal = (
            problem.theorem_statement[declaration_match.start() :]
            if declaration_match else problem.theorem_statement
        )
        source = formal + "\n" + (primary_error or "")
        raw = _TOKEN_RE.findall(source)
        preferred: list[str] = []
        ordinary: list[str] = []
        for token in raw:
            base = token.split(".")[-1]
            if len(base) < 4 or base.lower() in _STOPWORDS:
                continue
            target = token.strip("'")
            bucket = preferred if ("." in target or target[:1].isupper()) else ordinary
            if target not in preferred and target not in ordinary:
                bucket.append(target)
        theorem_terms = [part for part in problem.theorem_name.split("_") if len(part) >= 3]
        notation_terms = []
        if "Π" in formal:
            notation_terms.append("pi")
        if "^" in formal:
            notation_terms.append("pow")
        ordered = sorted(preferred, key=lambda term: ("." not in term, term))
        result: list[str] = []
        for term in [*ordered, *theorem_terms, *notation_terms, *ordinary]:
            if term not in result:
                result.append(term)
        return result

    def _lexical_candidates(self, terms: list[str]) -> list[RetrievedLemma]:
        if not self.mathlib_root.exists() or not terms:
            return []
        files: list[Path] = []
        fragments = list(
            dict.fromkeys(
                term.lower().split(".")[-1]
                for term in terms
                if len(term.split(".")[-1]) >= 3
            )
        )[:6]
        pair_patterns = []
        for left_index, left in enumerate(fragments):
            for right in fragments[left_index + 1 :]:
                pair_patterns.extend(
                    [f"{re.escape(left)}.*{re.escape(right)}", f"{re.escape(right)}.*{re.escape(left)}"]
                )
        if pair_patterns:
            declaration_pattern = (
                r"(?:theorem|lemma)\s+[A-Za-z0-9_'.]*(?:"
                + "|".join(pair_patterns)
                + ")"
            )
            completed = subprocess.run(
                [
                    "rg", "-l", "-i", "-e", declaration_pattern,
                    "--glob", "*.lean", str(self.mathlib_root),
                ],
                capture_output=True,
                text=True,
                check=False,
            )
            pair_files = [Path(line) for line in completed.stdout.splitlines()]
            pair_files.sort(
                key=lambda path: sum(
                    fragment in str(path).lower() for fragment in fragments
                ),
                reverse=True,
            )
            files.extend(pair_files[: self.file_limit * 3])
        per_term_limit = max(8, self.file_limit // max(1, min(8, len(terms))))
        for term in terms[:8]:
            search_term = term if "." in term else term.split(".")[-1]
            completed = subprocess.run(
                [
                    "rg", "-l", "-F", search_term, "--glob", "*.lean",
                    str(self.mathlib_root),
                ],
                capture_output=True,
                text=True,
                check=False,
            )
            files.extend(
                Path(line) for line in completed.stdout.splitlines()[:per_term_limit]
            )
            files = list(dict.fromkeys(files))[: self.file_limit * 3]

        lowered_terms = {
            value
            for term in terms
            for value in (term.lower(), term.lower().split(".")[-1])
        }
        candidates: list[RetrievedLemma] = []
        for path in files:
            candidates.extend(self._declarations_in_file(path, lowered_terms))
        candidates.sort(key=lambda candidate: candidate.score or 0.0, reverse=True)
        unique: dict[str, RetrievedLemma] = {}
        for candidate in candidates:
            unique.setdefault(candidate.name, candidate)
        return list(unique.values())

    def _declarations_in_file(
        self, path: Path, terms: set[str]
    ) -> list[RetrievedLemma]:
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        scopes: list[tuple[str, str]] = []
        found: list[RetrievedLemma] = []
        for index, line in enumerate(lines):
            if namespace := _NAMESPACE_RE.match(line):
                scopes.append(("namespace", namespace.group(1)))
                continue
            if _SECTION_RE.match(line):
                scopes.append(("section", ""))
                continue
            if _END_RE.match(line):
                if scopes:
                    scopes.pop()
                continue
            declaration = _DECL_RE.match(line)
            if not declaration:
                continue
            raw_name = declaration.group("name")
            namespaces = [name for kind, name in scopes if kind == "namespace"]
            name = raw_name if "." in raw_name else ".".join([*namespaces, raw_name])
            signature_lines = [line.strip()]
            for continuation in lines[index + 1 : index + 10]:
                signature_lines.append(continuation.strip())
                if ":=" in continuation or " where" in continuation:
                    break
            signature = " ".join(signature_lines)
            haystack = (name + " " + signature + " " + path.stem).lower()
            overlap = sum(term in haystack for term in terms)
            if overlap == 0:
                continue
            name_lower = name.lower()
            name_hits = sum(term in name_lower for term in terms)
            dotted_bonus = 3.0 if any(
                "." in term and name_lower.startswith(term.rsplit(".", 1)[0].lower() + ".")
                for term in terms
            ) else 0.0
            score = float(overlap + 2 * name_hits) + dotted_bonus
            found.append(
                RetrievedLemma(name, signature, str(path), False, score)
            )
        return found

    def _verify(
        self,
        problem: BenchmarkProblem,
        candidates: list[RetrievedLemma],
        runner: LeanRunner,
        run_id: str,
        label: str,
    ) -> list[RetrievedLemma]:
        imports = "\n".join(
            line for line in problem.source_text.splitlines()
            if line.lstrip().startswith("import ")
        ) or "import Mathlib"
        checks = "\n".join(f"#check {candidate.name}" for candidate in candidates)
        source = f"{imports}\n\n{checks}\n"
        result = runner.check_source(problem, source, run_id, f"{label}_retrieval_check")
        output = result.stdout + "\n" + result.stderr
        checked: list[RetrievedLemma] = []
        candidate_starts = "|".join(
            re.escape(item.name) for item in candidates
        )
        universe_suffix = r"(?:\.\{[^}\n]+\})?"
        for candidate in candidates:
            # Lean normally prints explicit binders between a declaration name and
            # its result type, for example `Nat.add_comm (n m : Nat) : ...`.
            # Treat a declaration as verified only when its own #check output is
            # present; a source-code grep hit alone is never sufficient.
            signature_match = re.search(
                rf"(?ms)^{re.escape(candidate.name)}{universe_suffix}"
                rf"(?P<body>(?:\s|\().*?)"
                rf"(?=^(?:{candidate_starts}){universe_suffix}(?:\s|\()|"
                rf"^.*?\.lean:\d+:\d+: error(?:\([^\n)]*\))?:|\Z)",
                output,
            )
            if signature_match is None:
                checked.append(candidate)
                continue
            signature = candidate.name + signature_match.group("body").rstrip()
            checked.append(replace(candidate, signature=signature, verified=True))
        return checked


def format_retrieval(result: RetrievalResult) -> str:
    """Format only verified candidates plus a short application audit checklist."""

    if not result.verified:
        return "Verified Mathlib retrieval found no usable candidates."
    blocks = [
        "Verified local Mathlib candidates (checked in the current FATE environment):"
    ]
    for candidate in result.verified:
        blocks.append(
            f"Name: {candidate.name}\nType: {candidate.signature}\n"
            f"Source: {candidate.source_file}"
        )
    blocks.append(
        "Candidate audit: before using one, compare its conclusion with the current "
        "goal, list the premises `apply/refine` will create, and check that required "
        "implicit/typeclass arguments and premises are plausibly available."
    )
    return "\n\n".join(blocks)
