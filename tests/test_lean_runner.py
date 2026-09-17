import tempfile
import unittest
from pathlib import Path

from agent.benchmark_adapter import FateMAdapter
from agent.config import PROJECT_ROOT
from agent.lean_runner import LeanRunner
from tests.helpers import synthetic_problem


class LeanRunnerTests(unittest.TestCase):
    def test_distinguishes_success_and_failure_and_saves_source(self) -> None:
        adapter = FateMAdapter(PROJECT_ROOT / "benchmark" / "FATE-M")
        with tempfile.TemporaryDirectory(dir=PROJECT_ROOT / "scratch") as directory:
            runner = LeanRunner(adapter, Path(directory), 180)
            good = runner.check_proof(synthetic_problem(), "by rfl", "test", "good")
            bad = runner.check_proof(
                synthetic_problem(), "by exact Nat.zero_ne_one", "test", "bad"
            )
            self.assertTrue(good.scratch_file.exists())
        self.assertTrue(good.success, good.primary_error)
        self.assertFalse(bad.success)
        self.assertIsNotNone(bad.primary_error)


if __name__ == "__main__":
    unittest.main()

