import unittest

from agent.evaluator import extract_proof, prohibited_construct


class EvaluatorTests(unittest.TestCase):
    def test_extracts_fenced_proof(self) -> None:
        self.assertEqual(extract_proof("```lean\nby\n  rfl\n```"), "by\n  rfl")

    def test_rejects_proof_bypasses(self) -> None:
        for text in ("by sorry", "by admit", "by exact?", "by\n  axiom bad : False"):
            with self.subTest(text=text):
                self.assertIsNotNone(prohibited_construct(text))


if __name__ == "__main__":
    unittest.main()

