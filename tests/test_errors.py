import unittest
from pathlib import Path

from agent.error_classifier import LeanFailureKind, classify_failure
from agent.lean_runner import _structure_result


class StructuredErrorTests(unittest.TestCase):
    def test_extracts_first_located_error(self) -> None:
        output = (
            "/tmp/Test.lean:7:3: error: unknown identifier 'foo'\n"
            "/tmp/Test.lean:8:3: error: unsolved goals\n⊢ False"
        )
        result = _structure_result(1, output, "", 0.1, None)  # type: ignore[arg-type]
        self.assertEqual(result.error_line, 7)
        self.assertEqual(result.error_column, 3)
        self.assertIn("unknown identifier", result.primary_error or "")

    def test_classifies_representative_failures(self) -> None:
        cases = {
            "unexpected identifier after decimal point": LeanFailureKind.SYNTAX,
            "unknown identifier 'x'": LeanFailureKind.UNKNOWN_IDENTIFIER,
            "application type mismatch": LeanFailureKind.APPLICATION_MISMATCH,
            "tactic 'rewrite' failed": LeanFailureKind.REWRITE_MISMATCH,
            "failed to synthesize Group α": LeanFailureKind.INSTANCE_SYNTHESIS,
            "unsolved goals\n⊢ P": LeanFailureKind.UNSOLVED_GOALS,
        }
        for message, expected in cases.items():
            with self.subTest(message=message):
                self.assertEqual(classify_failure(message), expected)

    def test_extracts_tagged_lean_error(self) -> None:
        output = (
            "/tmp/proof.lean:7:15: error(lean.synthInstanceFailed): "
            "failed to synthesize instance of type class\n  Inv R\n"
        )
        result = _structure_result(1, output, "", 0.1, Path("proof.lean"))
        self.assertEqual(result.error_line, 7)
        self.assertIn("failed to synthesize", result.primary_error or "")
        self.assertEqual(
            classify_failure(result.primary_error),
            LeanFailureKind.INSTANCE_SYNTHESIS,
        )


if __name__ == "__main__":
    unittest.main()
