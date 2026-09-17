import json
import tempfile
import unittest
from pathlib import Path

from agent.logger import ExperimentLogger


class LoggerTests(unittest.TestCase):
    def test_writes_jsonl_and_summary(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            logger = ExperimentLogger(Path(directory), "run")
            logger.log_attempt({"problem_id": "1", "success": False})
            logger.write_summary({"total_problems": 1})
            row = json.loads(logger.trace_path.read_text().strip())
            summary = json.loads(logger.summary_path.read_text())
        self.assertEqual(row["problem_id"], "1")
        self.assertIn("timestamp", row)
        self.assertEqual(summary["total_problems"], 1)


if __name__ == "__main__":
    unittest.main()

