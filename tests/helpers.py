from agent.benchmark_adapter import BenchmarkProblem


def synthetic_problem() -> BenchmarkProblem:
    source = "import Mathlib\n\ntheorem agent_test : (1 : ℕ) = 1 := by\n  sorry\n"
    proof = "by\n  sorry"
    start = source.index(proof)
    return BenchmarkProblem(
        problem_id="synthetic",
        benchmark="TEST",
        theorem_name="agent_test",
        theorem_statement=source[:start].rstrip(),
        informal_statement=None,
        source_path=None,  # type: ignore[arg-type]
        source_text=source,
        proof_start=start,
        proof_end=start + len(proof),
    )

