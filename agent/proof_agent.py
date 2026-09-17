"""Benchmark-independent baseline and ProsaBuddy-lite proving loops."""

from __future__ import annotations

import time
from dataclasses import asdict, dataclass
from typing import Any

from .benchmark_adapter import BenchmarkAdapter, BenchmarkProblem
from .config import AgentMode
from .error_classifier import LeanFailureKind, classify_failure
from .evaluator import evaluate_candidate, extract_proof
from .lean_runner import LeanCheckResult, LeanRunner
from .llm_backend import LLMBackend
from .logger import ExperimentLogger
from .prefix_repair import PrefixCertification, PrefixRepairer, assemble_suffix
from .prompts import build_generation_messages, build_prefix_messages
from .proving_skills import activate_skill
from .retrieval import MathlibRetriever, RetrievalResult, format_retrieval


@dataclass(frozen=True)
class ProblemRunResult:
    """Final outcome and resources for one theorem under one mode."""

    problem_id: str
    theorem_name: str
    mode: str
    success: bool
    attempts: int
    final_proof: str | None
    final_lean_return_code: int | None
    api_calls: int
    retrieval_tool_calls: int
    lean_calls: int
    input_tokens: int
    output_tokens: int
    total_tokens: int
    runtime: float
    trace_file: str

    def to_summary_dict(self) -> dict[str, object]:
        """Return compact JSON-safe per-problem metrics."""

        return asdict(self)


class ProofAgent:
    """Run fair whole-proof or enhanced iterative proof repair."""

    def __init__(
        self,
        *,
        mode: AgentMode,
        backend: LLMBackend,
        adapter: BenchmarkAdapter,
        runner: LeanRunner,
        logger: ExperimentLogger,
        run_id: str,
        max_attempts: int = 5,
        retriever: MathlibRetriever | None = None,
        prefix_validation_limit: int = 4,
    ) -> None:
        self.mode = mode
        self.backend = backend
        self.adapter = adapter
        self.runner = runner
        self.logger = logger
        self.run_id = run_id
        self.max_attempts = max_attempts
        self.retriever = retriever
        self.prefix_repairer = PrefixRepairer(runner, prefix_validation_limit)

    def prove(self, problem: BenchmarkProblem) -> ProblemRunResult:
        """Use at most `max_attempts` model calls and require final Lean success."""

        run_started = time.perf_counter()
        start_lean_calls = self.runner.compiler_calls
        previous_proof: str | None = None
        primary_error: str | None = None
        failure_kind: LeanFailureKind | None = None
        certified: PrefixCertification | None = None
        retrieval_result = RetrievalResult(False, None, None, [])
        retrieval_runs = 0
        api_calls = 0
        retrieval_tool_calls = 0
        input_tokens = output_tokens = total_tokens = 0
        final_proof: str | None = None
        final_return_code: int | None = None

        for attempt in range(1, self.max_attempts + 1):
            attempt_started = time.perf_counter()
            repeated_failure = attempt >= 3
            retrieval_performed = False
            if (
                self.mode.uses_retrieval
                and self.retriever
                and (retrieval_runs == 0 or (repeated_failure and retrieval_runs < 2))
            ):
                trigger, reason = self.retriever.should_trigger(
                    problem,
                    failure_kind.value if failure_kind else None,
                    repeated_failure,
                )
                if trigger and reason:
                    retrieval_result = self.retriever.retrieve(
                        problem,
                        primary_error,
                        reason,
                        self.runner,
                        self.run_id,
                        f"{self.mode.value}_attempt_{attempt}",
                    )
                    retrieval_runs += 1
                    retrieval_performed = True
                    retrieval_tool_calls += retrieval_result.tool_calls

            skill = (
                activate_skill(
                    failure_kind,
                    repeated_failure=repeated_failure,
                    has_certified_prefix=certified is not None,
                    has_verified_retrieval=bool(retrieval_result.verified),
                )
                if self.mode.is_enhanced else None
            )
            retrieval_context = (
                format_retrieval(retrieval_result)
                if retrieval_result.triggered else None
            )

            using_prefix = self.mode.uses_prefix_repair and certified is not None
            if using_prefix:
                messages = build_prefix_messages(
                    problem,
                    certified.prefix,
                    certified.remaining_goal,
                    primary_error=primary_error,
                    skill=skill,
                    retrieval_context=retrieval_context,
                )
            else:
                messages = build_generation_messages(
                    problem,
                    self.mode,
                    previous_proof=previous_proof,
                    primary_error=primary_error,
                    failure_class=failure_kind.value if failure_kind else None,
                    skill=skill,
                    retrieval_context=retrieval_context,
                )

            generation = self.backend.generate(messages)
            api_calls += 1
            input_tokens += generation.input_tokens or 0
            output_tokens += generation.output_tokens or 0
            total_tokens += generation.total_tokens or 0

            proof = ""
            generated_suffix: str | None = None
            prefix_abandoned = False
            parse_error: str | None = None
            try:
                if using_prefix and certified:
                    assembled = assemble_suffix(certified.prefix, generation.text)
                    proof = assembled.proof
                    generated_suffix = assembled.suffix
                    prefix_abandoned = assembled.prefix_abandoned
                else:
                    proof = extract_proof(generation.text)
            except ValueError as error:
                parse_error = str(error)

            if parse_error:
                failure_kind = LeanFailureKind.SYNTAX
                primary_error = parse_error
                self.logger.log_attempt(
                    self._attempt_record(
                        problem=problem,
                        attempt=attempt,
                        model=generation.model,
                        messages=messages,
                        proof=proof,
                        lean_result=None,
                        failure_kind=failure_kind,
                        retrieval=retrieval_result,
                        retrieval_performed=retrieval_performed,
                        selected_lemma=None,
                        skill_name=skill.name if skill else None,
                        certified=None,
                        generated_suffix=generated_suffix,
                        prefix_abandoned=prefix_abandoned,
                        success=False,
                        rejection_reason=parse_error,
                        runtime=time.perf_counter() - attempt_started,
                        generation=generation,
                    )
                )
                previous_proof = generation.text
                continue

            lean_result = self.runner.check_proof(
                problem,
                proof,
                self.run_id,
                f"{self.mode.value}_attempt_{attempt}",
            )
            evaluation = evaluate_candidate(proof, lean_result.success)
            final_proof = proof
            final_return_code = lean_result.return_code
            selected_lemma = next(
                (
                    lemma.name for lemma in retrieval_result.verified
                    if lemma.name in proof
                ),
                None,
            )
            new_certification: PrefixCertification | None = None
            if not evaluation.success and self.mode.uses_prefix_repair:
                new_certification = self.prefix_repairer.certify(
                    problem, proof, lean_result, self.run_id, attempt
                )
                if new_certification:
                    certified = new_certification

            current_error = (
                evaluation.rejection_reason
                if lean_result.success and not evaluation.success
                else lean_result.primary_error
            )
            current_kind = classify_failure(current_error)
            self.logger.log_attempt(
                self._attempt_record(
                    problem=problem,
                    attempt=attempt,
                    model=generation.model,
                    messages=messages,
                    proof=proof,
                    lean_result=lean_result,
                    failure_kind=current_kind,
                    retrieval=retrieval_result,
                    retrieval_performed=retrieval_performed,
                    selected_lemma=selected_lemma,
                    skill_name=skill.name if skill else None,
                    certified=new_certification,
                    generated_suffix=generated_suffix,
                    prefix_abandoned=prefix_abandoned,
                    success=evaluation.success,
                    rejection_reason=evaluation.rejection_reason,
                    runtime=time.perf_counter() - attempt_started,
                    generation=generation,
                )
            )
            if evaluation.success:
                return self._result(
                    problem, True, attempt, final_proof, final_return_code,
                    api_calls, retrieval_tool_calls, start_lean_calls,
                    input_tokens, output_tokens, total_tokens, run_started,
                )

            previous_proof = proof
            primary_error = current_error or "Lean rejected the proof without a parsed error."
            failure_kind = current_kind or LeanFailureKind.OTHER

        return self._result(
            problem, False, self.max_attempts, final_proof, final_return_code,
            api_calls, retrieval_tool_calls, start_lean_calls,
            input_tokens, output_tokens, total_tokens, run_started,
        )

    def _result(
        self,
        problem: BenchmarkProblem,
        success: bool,
        attempts: int,
        final_proof: str | None,
        final_return_code: int | None,
        api_calls: int,
        retrieval_tool_calls: int,
        start_lean_calls: int,
        input_tokens: int,
        output_tokens: int,
        total_tokens: int,
        run_started: float,
    ) -> ProblemRunResult:
        return ProblemRunResult(
            problem_id=problem.problem_id,
            theorem_name=problem.theorem_name,
            mode=self.mode.value,
            success=success,
            attempts=attempts,
            final_proof=final_proof,
            final_lean_return_code=final_return_code,
            api_calls=api_calls,
            retrieval_tool_calls=retrieval_tool_calls,
            lean_calls=self.runner.compiler_calls - start_lean_calls,
            input_tokens=input_tokens,
            output_tokens=output_tokens,
            total_tokens=total_tokens,
            runtime=time.perf_counter() - run_started,
            trace_file=str(self.logger.trace_path),
        )

    def _attempt_record(
        self,
        *,
        problem: BenchmarkProblem,
        attempt: int,
        model: str,
        messages: list[dict[str, str]],
        proof: str,
        lean_result: LeanCheckResult | None,
        failure_kind: LeanFailureKind | None,
        retrieval: RetrievalResult,
        retrieval_performed: bool,
        selected_lemma: str | None,
        skill_name: str | None,
        certified: PrefixCertification | None,
        generated_suffix: str | None,
        prefix_abandoned: bool,
        success: bool,
        rejection_reason: str | None,
        runtime: float,
        generation: Any,
    ) -> dict[str, Any]:
        """Build the required detailed record for one model generation."""

        return {
            "problem_id": problem.problem_id,
            "benchmark": problem.benchmark,
            "mode": self.mode.value,
            "attempt": attempt,
            "model": model,
            "theorem_statement": problem.theorem_statement,
            "prompt": messages,
            "generated_proof": proof,
            "primary_lean_error": lean_result.primary_error if lean_result else rejection_reason,
            "failure_class": failure_kind.value if failure_kind else None,
            "lean_stdout": lean_result.stdout if lean_result else "",
            "lean_stderr": lean_result.stderr if lean_result else "",
            "lean_return_code": lean_result.return_code if lean_result else None,
            "lean_scratch_file": str(lean_result.scratch_file) if lean_result else None,
            "retrieval_triggered": retrieval_performed,
            "retrieval_reason": retrieval.reason,
            "retrieval_query": retrieval.query,
            "retrieved_candidates": [asdict(item) for item in retrieval.candidates],
            "verified_candidates": [asdict(item) for item in retrieval.verified],
            "selected_lemma": selected_lemma,
            "proving_skill_activated": skill_name,
            "certified_prefix": certified.prefix if certified else None,
            "certified_prefix_length": certified.prefix_length if certified else 0,
            "remaining_goal": certified.remaining_goal if certified else None,
            "generated_suffix": generated_suffix,
            "prefix_abandoned": prefix_abandoned,
            "success": success,
            "rejection_reason": rejection_reason,
            "runtime": runtime,
            "input_tokens": generation.input_tokens,
            "output_tokens": generation.output_tokens,
            "total_tokens": generation.total_tokens,
        }
