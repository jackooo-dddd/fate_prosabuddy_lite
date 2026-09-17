import unittest

from agent.benchmark_adapter import FateMAdapter
from agent.config import PROJECT_ROOT


class FateMAdapterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.adapter = FateMAdapter(PROJECT_ROOT / "benchmark" / "FATE-M")

    def test_loads_all_fate_files_in_numeric_order(self) -> None:
        problems = self.adapter.load_problems()
        self.assertEqual(len(problems), 150)
        self.assertEqual([problem.problem_id for problem in problems[:3]], ["1", "2", "3"])

    def test_replaces_only_single_proof_hole(self) -> None:
        problem = self.adapter.get_problem("1")
        source = self.adapter.build_source(problem, "by\n  rfl")
        self.assertEqual(source[: problem.proof_start], problem.source_text[: problem.proof_start])
        self.assertEqual(source[problem.proof_start :].splitlines()[:2], ["by", "  rfl"])
        self.assertNotIn("sorry", source)


if __name__ == "__main__":
    unittest.main()

