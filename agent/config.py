"""Central experiment configuration shared by every proving mode."""

from __future__ import annotations

import os
from dataclasses import dataclass, replace
from enum import Enum
from pathlib import Path

from dotenv import load_dotenv


PROJECT_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_MODEL = "deepseek-flash"


class AgentMode(str, Enum):
    """Supported experimental conditions."""

    BASELINE = "baseline"
    RETRIEVAL_APPLY = "retrieval_apply"
    PREFIX_REPAIR = "prefix_repair"
    FULL_ENHANCED = "full_enhanced"

    @property
    def uses_retrieval(self) -> bool:
        return self in {self.RETRIEVAL_APPLY, self.FULL_ENHANCED}

    @property
    def uses_prefix_repair(self) -> bool:
        return self in {self.PREFIX_REPAIR, self.FULL_ENHANCED}

    @property
    def is_enhanced(self) -> bool:
        return self is not self.BASELINE


@dataclass(frozen=True)
class AgentConfig:
    """Store reproducible model, Lean, retrieval, and path settings."""

    project_root: Path = PROJECT_ROOT
    fate_m_root: Path = PROJECT_ROOT / "benchmark" / "FATE-M"
    results_dir: Path = PROJECT_ROOT / "results"
    scratch_dir: Path = PROJECT_ROOT / "scratch"
    deepseek_base_url: str = "https://api.deepseek.com"
    model_name: str = DEFAULT_MODEL
    max_attempts: int = 5
    max_output_tokens: int | None = None
    temperature: float = 0.0
    lean_timeout_seconds: float = 180.0
    retrieval_top_k: int = 6
    retrieval_file_limit: int = 60
    prefix_validation_limit: int = 4

    @classmethod
    def from_env(cls, **overrides: object) -> "AgentConfig":
        """Load the local secret/configuration and apply CLI overrides last."""

        load_dotenv(PROJECT_ROOT / ".env")
        config = cls(
            deepseek_base_url=os.getenv("DEEPSEEK_BASE_URL", cls.deepseek_base_url),
            model_name=os.getenv("DEEPSEEK_MODEL", cls.model_name),
            max_attempts=int(os.getenv("MAX_ATTEMPTS", str(cls.max_attempts))),
            max_output_tokens=(
                int(os.environ["MAX_OUTPUT_TOKENS"])
                if os.getenv("MAX_OUTPUT_TOKENS") else None
            ),
            temperature=float(os.getenv("LLM_TEMPERATURE", str(cls.temperature))),
            lean_timeout_seconds=float(
                os.getenv("LEAN_TIMEOUT_SECONDS", str(cls.lean_timeout_seconds))
            ),
            retrieval_top_k=int(os.getenv("RETRIEVAL_TOP_K", str(cls.retrieval_top_k))),
        )
        usable = {key: value for key, value in overrides.items() if value is not None}
        return replace(config, **usable)

    @property
    def deepseek_api_key(self) -> str:
        """Read the API key at runtime without embedding it in code or logs."""

        return os.getenv("DEEPSEEK_API_KEY", "").strip()
