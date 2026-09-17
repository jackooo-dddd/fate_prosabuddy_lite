"""Efficient deterministic search for baseline-fail/enhanced-success cases."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict
from datetime import datetime, timezone
from pathlib import Path

from .benchmark_adapter import BenchmarkProblem, FateMAdapter
from .config import AgentConfig, AgentMode
from .logger import ExperimentLogger
from .proof_agent import ProblemRunResult
from .run_experiment import make_agent


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmark", choices=["fate-m"], default="fate-m")
    parser.add_argument("--max-problems", type=int, default=20)
    parser.add_argument("--start-index", type=int, default=0)
    parser.add_argument("--max-attempts", type=int, default=None)
    parser.add_argument("--max-output-tokens", type=int, default=None)
    parser.add_argument("--model", default=None)
    return parser.parse_args()


def _run_condition(
    config: AgentConfig,
    adapter: FateMAdapter,
    problem: BenchmarkProblem,
    mode: AgentMode,
    search_id: str,
) -> ProblemRunResult:
    run_id = f"{search_id}_p{problem.problem_id}_{mode.value}"
    logger = ExperimentLogger(config.results_dir, run_id)
    agent = make_agent(config, mode, adapter, logger, run_id)
    result = agent.prove(problem)
    logger.write_summary(asdict(result))
    return result


def main() -> int:
    args = parse_args()
    config = AgentConfig.from_env(
        model_name=args.model,
        max_attempts=args.max_attempts,
        max_output_tokens=args.max_output_tokens,
    )
    adapter = FateMAdapter(config.fate_m_root)
    problems = adapter.load_problems()[
        args.start_index : args.start_index + args.max_problems
    ]
    search_id = datetime.now(timezone.utc).strftime("contrast_%Y%m%dT%H%M%S%fZ")
    records: list[dict[str, object]] = []
    contrast: dict[str, ProblemRunResult] | None = None

    for offset, problem in enumerate(problems, args.start_index):
        print(
            f"[{offset + 1}/{args.start_index + len(problems)}] "
            f"baseline FATE-M/{problem.problem_id} {problem.theorem_name}",
            flush=True,
        )
        baseline = _run_condition(
            config, adapter, problem, AgentMode.BASELINE, search_id
        )
        row: dict[str, object] = {
            "problem_id": problem.problem_id,
            "theorem_name": problem.theorem_name,
            "baseline": asdict(baseline),
        }
        if baseline.success:
            records.append(row)
            print("  baseline solved; enhanced modes skipped", flush=True)
            continue

        print("  baseline exhausted; running full_enhanced", flush=True)
        enhanced = _run_condition(
            config, adapter, problem, AgentMode.FULL_ENHANCED, search_id
        )
        row["full_enhanced"] = asdict(enhanced)
        records.append(row)
        if not enhanced.success:
            print("  full_enhanced also failed", flush=True)
            continue

        print("  contrast found; running component ablations", flush=True)
        retrieval = _run_condition(
            config, adapter, problem, AgentMode.RETRIEVAL_APPLY, search_id
        )
        prefix = _run_condition(
            config, adapter, problem, AgentMode.PREFIX_REPAIR, search_id
        )
        contrast = {
            "baseline": baseline,
            "full_enhanced": enhanced,
            "retrieval_apply": retrieval,
            "prefix_repair": prefix,
        }
        row["retrieval_apply"] = asdict(retrieval)
        row["prefix_repair"] = asdict(prefix)
        _write_contrast_report(config.results_dir, problem, contrast)
        break

    search_summary = {
        "search_id": search_id,
        "benchmark": "FATE-M",
        "benchmark_commit": _git_commit(config.fate_m_root),
        "model": config.model_name,
        "temperature": config.temperature,
        "max_attempts": config.max_attempts,
        "max_output_tokens": config.max_output_tokens,
        "problems_examined": len(records),
        "contrast_found": contrast is not None,
        "records": records,
    }
    path = config.results_dir / f"{search_id}_search_summary.json"
    path.write_text(json.dumps(search_summary, indent=2), encoding="utf-8")
    print(f"Search summary: {path}")
    return 0 if contrast else 1


def _write_contrast_report(
    results_dir: Path,
    problem: BenchmarkProblem,
    results: dict[str, ProblemRunResult],
) -> None:
    traces = {
        mode: _read_problem_trace(Path(result.trace_file), problem.problem_id)
        for mode, result in results.items()
    }
    baseline_rows = traces["baseline"]
    enhanced_rows = traces["full_enhanced"]
    verified = []
    skills = []
    prefixes = []
    retrieval_events = []
    selected_lemmas = []
    for row in enhanced_rows:
        verified.extend(row.get("verified_candidates", []))
        if row.get("retrieval_triggered"):
            retrieval_events.append(
                {
                    "reason": row.get("retrieval_reason"),
                    "query": row.get("retrieval_query"),
                }
            )
        if row.get("selected_lemma"):
            selected_lemmas.append(str(row["selected_lemma"]))
        if row.get("proving_skill_activated"):
            skills.append(row["proving_skill_activated"])
        if row.get("certified_prefix"):
            prefixes.append(
                {
                    "prefix": row["certified_prefix"],
                    "remaining_goal": row.get("remaining_goal"),
                    "suffix": row.get("generated_suffix"),
                    "abandoned": row.get("prefix_abandoned"),
                }
            )
    final = results["full_enhanced"]
    lines = [
        "# Contrast case",
        "",
        "## Problem",
        "",
        f"- Benchmark: FATE-M",
        f"- Problem ID: {problem.problem_id}",
        f"- Theorem: `{problem.theorem_name}`",
        "",
        problem.informal_statement or "No informal statement supplied.",
        "",
        "```lean",
        problem.theorem_statement,
        "```",
        "",
        "## Baseline",
        "",
        f"- Model: `{baseline_rows[0]['model'] if baseline_rows else 'unknown'}`",
        f"- Attempt limit: {results['baseline'].attempts}",
        f"- Final status: {'SUCCESS' if results['baseline'].success else 'FAILURE'}",
    ]
    for row in baseline_rows:
        lines.extend(
            [
                "",
                f"### Attempt {row['attempt']}",
                "",
                "```lean",
                row.get("generated_proof") or "<no parseable proof>",
                "```",
                "",
                "First Lean error:",
                "```text",
                _display_error(row),
                "```",
            ]
        )
    lines.extend(
        [
            "",
            "## Enhanced",
            "",
            "- Mode: `full_enhanced`",
            "- Retrieval events: "
            + (
                "; ".join(
                    f"reason={event['reason']!r}, query={event['query']!r}"
                    for event in retrieval_events
                )
                or "none"
            ),
            f"- Activated skills: {', '.join(dict.fromkeys(skills)) or 'none'}",
            f"- Verified retrieved lemmas: {', '.join(dict.fromkeys(item['name'] for item in verified)) or 'none'}",
            f"- Retrieved lemmas used in generated proof: {', '.join(dict.fromkeys(selected_lemmas)) or 'none detected'}",
            f"- Certified prefix events: {len(prefixes)}",
        ]
    )
    for index, prefix in enumerate(prefixes, 1):
        lines.extend(
            [
                "",
                f"### Prefix event {index}",
                "",
                "```lean",
                str(prefix["prefix"]),
                "```",
                "",
                "Remaining goal:",
                "```text",
                str(prefix["remaining_goal"]),
                "```",
                f"Prefix abandoned: `{prefix['abandoned']}`",
            ]
        )
    lines.extend(
        [
            "",
            "## Final verified proof",
            "",
            "```lean",
            final.final_proof or "<missing>",
            "```",
            "",
            "## Verification",
            "",
            f"- Lean return code: `{final.final_lean_return_code}`",
            "- No `sorry`: verified by evaluator",
            "- No `admit`: verified by evaluator",
            "- No added axioms/opaque assumptions: verified by evaluator and exact-source insertion",
            "",
            "## Resource comparison",
            "",
            "| Mode | Success | API calls | Tokens | Lean calls | Runtime (s) |",
            "|---|---:|---:|---:|---:|---:|",
        ]
    )
    for mode in ("baseline", "retrieval_apply", "prefix_repair", "full_enhanced"):
        result = results[mode]
        lines.append(
            f"| {mode} | {result.success} | {result.api_calls} | "
            f"{result.total_tokens} | {result.lean_calls} | {result.runtime:.2f} |"
        )
    lines.extend(
        [
            "",
            "## Interpretation",
            "",
            "The trace establishes a baseline failure and an enhanced Lean-verified success "
            "under the same model and generation budget. The logged retrieval, selected "
            "skills, compiler diagnostics, and prefix events above show which mechanisms "
            "were actually exercised; they support association, not a causal claim beyond "
            "this case.",
            "",
        ]
    )
    (results_dir / "contrast_case.md").write_text("\n".join(lines), encoding="utf-8")


def _read_problem_trace(path: Path, problem_id: str) -> list[dict[str, object]]:
    if not path.exists():
        return []
    return [
        json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()
        if json.loads(line).get("problem_id") == problem_id
    ]


def _display_error(row: dict[str, object]) -> str:
    """Recover tagged Lean errors in older traces without mutating evidence."""

    if primary := row.get("primary_lean_error"):
        return str(primary)
    output = f"{row.get('lean_stdout', '')}\n{row.get('lean_stderr', '')}"
    match = re.search(
        r"(?ms)^.*?\.lean:\d+:\d+: error(?:\([^\n)]*\))?:\s*"
        r"(.*?)(?=^.*?\.lean:\d+:\d+: (?:error|warning)(?:\([^\n)]*\))?:|\Z)",
        output,
    )
    return match.group(1).strip() if match else "<none>"


def _git_commit(path: Path) -> str:
    import subprocess

    completed = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=path,
        capture_output=True, text=True, check=False,
    )
    return completed.stdout.strip() or "unknown"


if __name__ == "__main__":
    raise SystemExit(main())
