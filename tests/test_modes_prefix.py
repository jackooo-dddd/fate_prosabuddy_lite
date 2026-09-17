import unittest
from pathlib import Path

from agent.config import AgentMode
from agent.lean_runner import LeanCheckResult
from agent.prefix_repair import PrefixRepairer, assemble_suffix, split_tactic_chunks
from agent.proving_skills import activate_skill
from tests.helpers import synthetic_problem


class ModeAndPrefixTests(unittest.TestCase):
    def test_mode_features(self) -> None:
        self.assertFalse(AgentMode.BASELINE.uses_retrieval)
        self.assertTrue(AgentMode.RETRIEVAL_APPLY.uses_retrieval)
        self.assertTrue(AgentMode.PREFIX_REPAIR.uses_prefix_repair)
        self.assertTrue(AgentMode.FULL_ENHANCED.uses_retrieval)
        self.assertTrue(AgentMode.FULL_ENHANCED.uses_prefix_repair)

    def test_verified_retrieval_activates_goal_driven_application(self) -> None:
        skill = activate_skill(None, has_verified_retrieval=True)
        self.assertIsNotNone(skill)
        self.assertEqual(skill.name, "goal_driven_apply")

    def test_extracts_top_level_prefix_chunks(self) -> None:
        proof = "by\n  intro x\n  have h : True := by\n    trivial\n  exact h"
        chunks = split_tactic_chunks(proof)
        self.assertEqual(len(chunks), 3)
        self.assertIn("trivial", chunks[1])

    def test_appends_suffix_without_overwriting_prefix(self) -> None:
        result = assemble_suffix("by\n  intro x", "exact x")
        self.assertEqual(result.proof, "by\n  intro x\n  exact x")
        self.assertFalse(result.prefix_abandoned)

    def test_unsolved_candidate_keeps_all_successful_chunks(self) -> None:
        proof = "by\n  constructor\n  · trivial"
        chunks = split_tactic_chunks(proof)
        failed = LeanCheckResult(
            False, 1, "", "", "unsolved goals\n⊢ True", 1, 1,
            ["⊢ True"], 0.0, Path("diagnostic.lean"),
        )
        count = PrefixRepairer._candidate_chunk_count(
            synthetic_problem(), proof, failed, chunks
        )
        self.assertEqual(count, len(chunks))


if __name__ == "__main__":
    unittest.main()
