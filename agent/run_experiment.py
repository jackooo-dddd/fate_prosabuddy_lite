"""CLI for running one or more FATE-M problems under a selected mode."""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone

from .benchmark_adapter import FateMAdapter
from .config import AgentConfig, AgentMode
from .evaluator_summary import summarize_results
from .lean_runner import LeanRunner
from .llm_backend import DeepSeekBackend
from .logger import ExperimentLogger
from .proof_agent import ProofAgent
from .retrieval import MathlibRetriever


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=[mode.value for mode in AgentMode], default="baseline")
    parser.add_argument("--problem", help="Numeric FATE-M ID or theorem name")
    parser.add_argument("--num-problems", type=int, default=1)
    parser.add_argument("--start-index", type=int, default=0)
    parser.add_argument("--max-attempts", type=int, default=None)
    parser.add_argument("--max-output-tokens", type=int, default=None)
    parser.add_argument("--model", default=None)
    return parser.parse_args()


def make_agent(
    config: AgentConfig,
    mode: AgentMode,
    adapter: FateMAdapter,
    logger: ExperimentLogger,
    run_id: str,
) -> ProofAgent:
    """Construct an agent while keeping model settings identical across modes."""

    runner = LeanRunner(adapter, config.scratch_dir, config.lean_timeout_seconds)
    retriever = None
    if mode.uses_retrieval:
        retriever = MathlibRetriever(
            config.fate_m_root / ".lake" / "packages" / "mathlib" / "Mathlib",
            config.retrieval_top_k,
            config.retrieval_file_limit,
        )
    return ProofAgent(
        mode=mode,
        backend=DeepSeekBackend(config),
        adapter=adapter,
        runner=runner,
        logger=logger,
        run_id=run_id,
        max_attempts=config.max_attempts,
        retriever=retriever,
        prefix_validation_limit=config.prefix_validation_limit,
    )


def main() -> int:
    args = parse_args()
    config = AgentConfig.from_env(
        model_name=args.model,
        max_attempts=args.max_attempts,
        max_output_tokens=args.max_output_tokens,
    )
    mode = AgentMode(args.mode)
    adapter = FateMAdapter(config.fate_m_root)
    all_problems = adapter.load_problems()
    if args.problem:
        problems = [adapter.get_problem(args.problem)]
    else:
        problems = all_problems[args.start_index : args.start_index + args.num_problems]
        if len(problems) != args.num_problems:
            raise ValueError(
                f"Requested {args.num_problems} problems from index {args.start_index}, "
                f"but selected {len(problems)}"
            )

    run_id = datetime.now(timezone.utc).strftime(
        f"fate_m_{mode.value}_%Y%m%dT%H%M%S%fZ"
    )
    logger = ExperimentLogger(config.results_dir, run_id)
    agent = make_agent(config, mode, adapter, logger, run_id)
    results = []
    for problem in problems:
        print(
            f"[{mode.value}] FATE-M/{problem.problem_id} {problem.theorem_name} "
            f"(max {config.max_attempts} generations)",
            flush=True,
        )
        result = agent.prove(problem)
        results.append(result)
        print(
            f"[{problem.problem_id}] {'SOLVED' if result.success else 'FAILED'} "
            f"after {result.attempts} generation(s), {result.lean_calls} Lean call(s)",
            flush=True,
        )

    summary = summarize_results(
        results,
        benchmark="FATE-M",
        mode=mode.value,
        model=config.model_name,
    )
    summary.update(
        run_id=run_id,
        benchmark_commit=_git_commit(config.fate_m_root),
        max_attempts=config.max_attempts,
        temperature=config.temperature,
        max_output_tokens=config.max_output_tokens,
        timestamp=datetime.now(timezone.utc).isoformat(),
        trace_file=str(logger.trace_path),
    )
    logger.write_summary(summary)
    print(json.dumps(summary, indent=2))
    print(f"Trace: {logger.trace_path}")
    print(f"Summary: {logger.summary_path}")
    return 0 if all(result.success for result in results) else 1


def _git_commit(path: object) -> str:
    import subprocess

    completed = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=path,
        capture_output=True,
        text=True,
        check=False,
    )
    return completed.stdout.strip() or "unknown"


if __name__ == "__main__":
    raise SystemExit(main())
