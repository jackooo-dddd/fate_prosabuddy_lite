"""Append-only attempt traces and experiment summaries."""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


class ExperimentLogger:
    """Persist all evidence needed to audit or reproduce a run."""

    def __init__(self, results_dir: Path, run_id: str) -> None:
        results_dir.mkdir(parents=True, exist_ok=True)
        self.trace_path = results_dir / f"{run_id}.jsonl"
        self.summary_path = results_dir / f"{run_id}_summary.json"

    def log_attempt(self, record: dict[str, Any]) -> None:
        """Append one proof-generation attempt with a UTC timestamp."""

        enriched = {**record, "timestamp": datetime.now(timezone.utc).isoformat()}
        with self.trace_path.open("a", encoding="utf-8") as stream:
            stream.write(json.dumps(enriched, ensure_ascii=False) + "\n")

    def write_summary(self, summary: dict[str, Any]) -> None:
        """Write aggregate metrics separately from detailed JSONL traces."""

        self.summary_path.write_text(
            json.dumps(summary, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )

