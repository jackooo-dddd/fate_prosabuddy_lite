import tempfile
import unittest
from pathlib import Path

from agent.benchmark_adapter import FateMAdapter
from agent.config import PROJECT_ROOT
from agent.lean_runner import LeanRunner
from agent.retrieval import MathlibRetriever, RetrievedLemma, RetrievalResult, format_retrieval
from tests.helpers import synthetic_problem


class RetrievalTests(unittest.TestCase):
    def test_formats_verified_candidates_only(self) -> None:
        verified = RetrievedLemma("Nat.add_comm", "Nat.add_comm : a + b = b + a", "x", True, 2)
        unverified = RetrievedLemma("Bad.name", "unknown", "y", False, 1)
        text = format_retrieval(RetrievalResult(True, "test", "Nat add", [verified, unverified]))
        self.assertIn("Nat.add_comm", text)
        self.assertNotIn("Bad.name", text)

    def test_verifies_known_lemma_with_current_lean(self) -> None:
        adapter = FateMAdapter(PROJECT_ROOT / "benchmark" / "FATE-M")
        with tempfile.TemporaryDirectory(dir=PROJECT_ROOT / "scratch") as directory:
            runner = LeanRunner(adapter, Path(directory), 180)
            retriever = MathlibRetriever(
                PROJECT_ROOT / "benchmark" / "FATE-M" / ".lake" / "packages" / "mathlib" / "Mathlib"
            )
            candidates = [RetrievedLemma("Nat.add_comm", "", "test", False, 1)]
            result = retriever.verify_candidates(
                synthetic_problem(), candidates, runner, "test_retrieval"
            )
        self.assertEqual([item.name for item in result], ["Nat.add_comm"])
        self.assertTrue(result[0].verified)


if __name__ == "__main__":
    unittest.main()

